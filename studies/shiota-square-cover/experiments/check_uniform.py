"""Independently recover eligibility, forced centers and constraints from edge lists."""

import argparse
from collections import Counter
from itertools import combinations
import json
import random

from square_cover import reduce_drawing


def possible_centers(edge):
    orientation, x, y = edge
    if orientation == 0:
        return ((x, y - 1), (x, y + 1), (x + 1, y - 1), (x + 1, y + 1))
    return ((x - 1, y), (x + 1, y), (x - 1, y + 1), (x + 1, y + 1))


def constraints(required):
    counts = Counter(p for edge in required for p in possible_centers(edge))
    eligible = {p for p, count in counts.items() if count == 8}
    clauses = {frozenset(p for p in possible_centers(e) if p in eligible) for e in required}
    return eligible, clauses


def original_optimum(edges):
    vertices = sorted({i for edge in edges for i in edge})
    for size in range(len(vertices) + 1):
        for candidate in combinations(vertices, size):
            selected = set(candidate)
            if all(a in selected or b in selected for a, b in edges):
                return selected
    raise AssertionError('all original vertices must cover')


def direct_sat(clauses, predicted):
    from pysat.card import CardEnc, EncType
    from pysat.solvers import Solver

    labels = {p: i + 1 for i, p in enumerate(sorted(set().union(*clauses)))}
    raw = [[labels[p] for p in clause] for clause in clauses]
    for bound, expected in ((predicted, True), (predicted - 1, False)):
        if bound < 0:
            continue
        rows = list(raw)
        if bound < len(labels):
            rows += CardEnc.atmost(list(labels.values()), bound, encoding=EncType.cardnetwrk).clauses
        with Solver(name='cadical195', bootstrap_with=rows) as solver:
            assert solver.solve() is expected, ('SAT disagrees at budget', bound)


def check(vertices, edges, stats, use_sat=False):
    chosen = original_optimum(edges)
    result = reduce_drawing(vertices, edges, len(chosen))
    eligible, clauses = constraints(result.required)
    assert eligible == result.guards | result.optional and result.guards.isdisjoint(result.optional)
    assert {next(iter(c)) for c in clauses if len(c) == 1} == result.guards
    pure = {c for c in clauses if c.isdisjoint(result.guards)}
    recovered = {c for c in pure if len(c) == 2}
    assert all(any(frozenset(pair) in recovered for pair in combinations(clause, 2)) for clause in pure)
    used = set(result.hubs.values())
    links = set()
    witness = result.guards | {result.hubs[i] for i in chosen}
    degrees = Counter(i for pair in edges for i in pair)
    ranks = [{v: j for j, v in enumerate(sorted({vertices[i][k] for i in degrees}))} for k in (0, 1)]
    for (a, b), path in result.paths.items():
        assert (path[0], path[-1]) == (result.hubs[a], result.hubs[b])
        assert len(set(path)) == len(path) and not (set(path[1:-1]) & used)
        used.update(path[1:-1])
        distance = sum(abs(ranks[k][vertices[a][k]] - ranks[k][vertices[b][k]]) for k in (0, 1))
        skips = int(degrees[a] == 3) + int(degrees[b] == 3)
        assert len(path) - 1 == 34 * distance - skips - int(skips % 2 == 0)
        assert (len(path) - 1) % 2 == 1
        links.update(frozenset((p, q)) for p, q in zip(path, path[1:]))
        start = 2 if b not in chosen else 1
        witness.update(path[start:-1:2])
    assert used == result.optional and links == recovered
    assert len(witness) == result.budget == result.offset + len(chosen)
    assert all(witness & clause for clause in clauses)
    if use_sat:
        direct_sat(clauses, result.budget)
        stats['edge_only_sat_optima'] += 1
    stats.update(drawings=1, physical_edges=len(result.required), original_edges=len(edges))


def random_grid(rng, w, h):
    vertices = [(x, y) for x in range(w) for y in range(h)]
    choices = [(i, j) for i, p in enumerate(vertices) for j, q in enumerate(vertices[:i])
               if abs(p[0] - q[0]) + abs(p[1] - q[1]) == 1]
    rng.shuffle(choices)
    degree = Counter()
    edges = []
    for a, b in choices:
        if degree[a] < 3 and degree[b] < 3 and rng.random() < 0.78:
            edges.append((a, b))
            degree.update((a, b))
    return vertices, edges


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sat', action='store_true', help='also solve selected raw covers by SAT (PySAT)')
    args = parser.parse_args()
    stats = Counter()
    check([], [], stats, args.sat)
    check([(0, 0), (1, 0)], [(0, 1)], stats, args.sat)
    simple_edge = reduce_drawing([(0, 0), (2, 0)], [(0, 1)], 1)
    isolated = reduce_drawing([(0, 0), (2, 0), (1, 1)], [(0, 1)], 1)
    assert isolated == simple_edge
    square = [(0, 0), (1, 0), (1, 1), (0, 1)]
    grid_edges = [(0, 1), (1, 2), (2, 3), (3, 0)]
    for mask in range(16):
        check(square, [p for i, p in enumerate(grid_edges) if mask & (1 << i)], stats)

    # A collinear degree-two vertex splits one side of a rectangle, yielding an odd cycle.
    five = [(0, 0), (1, 0), (2, 0), (2, 1), (0, 1)]
    cycle = [(i, (i + 1) % 5) for i in range(5)]
    check(five, cycle, stats, args.sat)
    huge = 10 ** 400
    check([(huge*x - 2*huge, huge*y) for x, y in five], cycle, stats)
    # Two adjacent tees exercise the two-skip case; the exterior edges exercise one skip.
    double_tee = [(0, 0), (1, 0), (-1, 0), (0, 1), (1, -1), (2, 0)]
    tee_edges = [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5)]
    rng = random.Random(20261127)
    for _ in range(24):
        order = list(range(len(double_tee)))
        rng.shuffle(order)
        check([double_tee[j] for j in order], [(order.index(a), order.index(b)) for a, b in tee_edges], stats)
    for _ in range(100):
        check(*random_grid(rng, 4, 3), stats)

    for vertices, edges in [([(0, 0), (2, 0), (1, 0)], [(0, 1)]),
                            ([(0, 1), (2, 1), (1, 0), (1, 2)], [(0, 1), (2, 3)]),
                            ([(0, 0), (1, 0), (0, 1), (-1, 0), (0, -1)], [(0, i) for i in range(1, 5)])]:
        try:
            reduce_drawing(vertices, edges, 0)
        except ValueError:
            stats['invalid_drawings_rejected'] += 1
        else:
            raise AssertionError('invalid drawing accepted')
    print(json.dumps(dict(sorted(stats.items())), indent=2))


if __name__ == '__main__':
    main()
