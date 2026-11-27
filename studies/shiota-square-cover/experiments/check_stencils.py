"""Independent unit-edge verification of axial and junction tile gadgets."""

from functools import cache
from itertools import combinations, product
import json
from pathlib import Path

BASE = Path(__file__).resolve().parent
STEP = [(1, 0), (1, 0), (0, 1), (0, 1), (-1, 0), (-1, 0), (0, -1), (0, -1)]
ZERO = (0, 0)


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def times(n, p):
    return tuple(n * a for a in p)


def norm(p):
    return max(map(abs, p))


def box(r):
    return product(range(-r, r + 1), repeat=2)


def pair(a, b):
    return frozenset((a, b))


@cache
def boundary(p):
    vertex = add(p, (-1, -1))
    out = set()
    for d in STEP:
        next_vertex = add(vertex, d)
        out.add(pair(vertex, next_vertex))
        vertex = next_vertex
    assert len(out) == 8
    return frozenset(out)


def local_check(anchor, role, link):
    centers = [add(anchor, b) for b in box(2)]
    coverage = {e: {0: set(), 1: set(), 2: set()} for e in boundary(anchor)}
    for p in centers:
        r = role(p)
        if r:
            for e in boundary(p) & coverage.keys():
                coverage[e][r].add(p)
    r = role(anchor)
    eligible = all(d[1] or d[2] for d in coverage.values())
    assert eligible == bool(r), ("unaccounted eligible placement", anchor, r)
    if r == 2:
        assert any(d[2] == {anchor} and not d[1] for d in coverage.values()), (
            "guard lacks forced witness", anchor)
    if r == 1:
        for e, d in coverage.items():
            assert d[2] or any(link(x, y) for x, y in combinations(d[1], 2)), (
                "uncovered edge does not encode any link", anchor, sorted(e), d)
        for p in centers:
            if p != anchor and role(p) == 1 and link(anchor, p):
                assert any(d[1] == {anchor, p} and not d[2] for d in coverage.values()), (
                    "intended link lacks a private witness", anchor, p)


def check_straight_period():
    def role(p):
        x, y = p
        if y == 0:
            return 1
        if abs(y) == 1 and x % 4 in (0, 1):
            return 2
        return 0

    return check_center_list(
        product(range(4), range(-3, 4)), role,
        lambda a, b: a[1] == b[1] == 0 and abs(a[0] - b[0]) == 1,
    )


def check_center_list(centers, role, link):
    count = 0
    for p in centers:
        local_check(p, role, link)
        count += 1
    return count


def stencil(metadata):
    name = metadata["name"]
    radius = metadata["radius"]
    directions = tuple(map(tuple, metadata["directions"]))
    phases = metadata["phases"]
    guards = set(map(tuple, metadata["guards"]))
    expected_options = set(map(tuple, metadata["options"]))
    expected_links = {pair(*map(tuple, link)) for link in metadata["links"]}
    assert len(directions) == len(phases) and len(directions) == len(set(directions))
    assert all(sum(map(abs, d)) == 1 for d in directions)
    assert all(0 <= phase < 4 for phase in phases)
    assert all(norm(p) <= radius for p in guards)

    if name == "switch":
        path = [(-2, 0), (0, 1), (0, -1), (2, 0)]
        assert path[0] == times(2, directions[0]) and path[-1] == times(2, directions[1])
        assert len(set(path)) == len(path)
        assert all(norm(p) <= 2 for p in path)
        hub = set(path)
        hub_links = {pair(a, b) for a, b in zip(path, path[1:])}
        start = 2
    else:
        hub = {ZERO}
        start = 2 if name == "tee" else 1
        hub_links = {pair(ZERO, times(start, d)) for d in directions}

    material = set(hub)
    diagram = set(hub_links)
    for d in directions:
        material.update(times(t, d) for t in range(start, radius + 3))
        diagram.update(pair(times(t, d), times(t + 1, d))
                       for t in range(start, radius + 2))

    assert expected_options == {p for p in material if norm(p) <= radius}, name
    assert expected_links == {e for e in diagram if all(norm(p) <= radius for p in e)}, name
    assert not (guards & expected_options), name
    assert all(len(e) == 2 and norm(tuple(x-y for x, y in zip(*e))) <= 2 for e in diagram)

    def role(p):
        if norm(p) <= radius:
            return 1 if p in expected_options else 2 if p in guards else 0
        x, y = p
        for (a, b), phase in zip(directions, phases):
            t, off = a*x + b*y, a*y - b*x
            if t <= radius:
                continue
            if off == 0:
                return 1
            if abs(off) == 1 and (t - phase) % 4 in (0, 1):
                return 2
        return 0

    def link(p, q):
        if norm(p) <= radius + 2 and norm(q) <= radius + 2:
            return pair(p, q) in diagram
        return any(
            p == times(sum(a*b for a, b in zip(p, d)), d)
            and q == times(sum(a*b for a, b in zip(q, d)), d)
            and min(sum(a*b for a, b in zip(p, d)), sum(a*b for a, b in zip(q, d))) >= start
            and norm(tuple(x-y for x, y in zip(p, q))) == 1
            for d in directions
        )

    return role, link


def check_stencil(metadata):
    role, link = stencil(metadata)
    # Any other radius-2 neighborhood is empty or a period-4 wire translate.
    return check_center_list(box(metadata["radius"] + 2), role, link)


def main():
    tables = json.loads((BASE / "stencils.json").read_text())
    wire = check_straight_period()
    cores = {name: check_stencil(dict(table, name=name)) for name, table in tables.items()}
    print(json.dumps({"wire": wire, "cores": cores}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
