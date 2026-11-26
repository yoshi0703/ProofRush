"""Independently compute both invariants of the 14-vertex witness using Python 3."""

from functools import lru_cache
from itertools import combinations
import json


def witness_edges():
    """Build each block before adding its bridges."""
    edges = set()
    for start in (0, 9):
        for u, v in combinations(range(start, start + 4), 2):
            if (u, v) != (start, start + 1):
                edges.add((u, v))
        edges.update({(start, start + 4), (start + 1, start + 4)})
    for u, v in combinations(range(5, 9), 2):
        if (u, v) != (5, 6):
            edges.add((u, v))
    return edges | {(4, 5), (6, 13)}


def distances(vertices, edges):
    """Floyd–Warshall. The sentinel exceeds every finite simple-path length."""
    n = len(vertices)
    d = [[0 if i == j else n for j in vertices] for i in vertices]
    for u, v in edges:
        d[u][v] = d[v][u] = 1
    for k in vertices:
        for i in vertices:
            for j in vertices:
                d[i][j] = min(d[i][j], d[i][k] + d[k][j])
    return d


def minimum_clique_partition(adjacency):
    """Enumerate all vertex cliques, then optimize the first part of a partition."""
    n = len(adjacency)
    cliques_by_vertex = [[] for _ in adjacency]
    for mask in range(1, 1 << n):
        vertices = [i for i in range(n) if mask & (1 << i)]
        if all(adjacency[u] & (1 << v) for u, v in combinations(vertices, 2)):
            for i in vertices:
                cliques_by_vertex[i].append(mask)

    @lru_cache(None)
    def solve(mask):
        if not mask:
            return 0
        first = (mask & -mask).bit_length() - 1
        return 1 + min(solve(mask ^ c) for c in cliques_by_vertex[first] if c & mask == c)

    return solve((1 << n) - 1)


def main():
    vertices = range(14)
    edges = witness_edges()
    adj = [0 for _ in vertices]
    for u, v in edges:
        assert 0 <= u < v < len(vertices)
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    degrees = [bin(row).count("1") for row in adj]
    d = distances(vertices, edges)
    diameter = max(map(max, d))
    theta = minimum_clique_partition(adj)
    partition = [[0, 2, 3], [1, 4], [5, 7, 8], [6], [9, 11, 12], [10, 13]]
    independent = [0, 1, 5, 6, 9, 10]
    assert sorted(v for part in partition for v in part) == list(vertices)
    assert all((u, v) in edges for part in partition for u, v in combinations(part, 2))
    assert all((u, v) not in edges for u, v in combinations(independent, 2))
    assert len(edges) == 21 and set(degrees) == {3}
    assert d[2][11] == diameter == 8 < len(vertices)
    assert len(independent) == theta == 6 == len(partition)
    assert diameter > theta + 1
    print(json.dumps(dict(vertices=len(vertices), edges=sorted(edges), degrees=degrees,
                          diameter=diameter, distance_2_to_11=d[2][11],
                          vertex_clique_cover_number=theta, partition=partition,
                          independent_set=independent, proposed_upper_bound=theta + 1),
                     separators=(",", ":")))


if __name__ == "__main__":
    main()
