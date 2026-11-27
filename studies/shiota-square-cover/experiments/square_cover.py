"""Reduce bendless orthogonal subcubic Vertex Cover to Shiota's exact edge cover.

Input JSON: vertices are integer pairs, edges are pairs of zero-based vertex indices,
and budget is a nonnegative integer. Output lists the unit edges and exact budget.
"""

import argparse
from collections import defaultdict
from dataclasses import dataclass
from functools import cache
import json
from pathlib import Path
import sys


Point = tuple[int, int]
Edge = tuple[int, int, int]  # orientation (0 horizontal, 1 vertical), left/bottom x,y
PITCH = 17
HALF = 8


def translate(p, direction, distance=1):
    return (p[0] + distance * direction[0], p[1] + distance * direction[1])


def scale(p, factor):
    return (p[0] * factor, p[1] * factor)


def axial(p, q):
    dx, dy = q[0] - p[0], q[1] - p[1]
    if (dx == 0) == (dy == 0):
        raise ValueError(f'edge {p}, {q} is not a nondegenerate axis-aligned segment')
    length = abs(dx) + abs(dy)
    return (dx // length, dy // length), length


def perimeter(p):
    x, y = p
    for a in (x - 1, x):
        for b in (y - 1, y + 1):
            yield 0, a, b
    for a in (x - 1, x + 1):
        for b in (y - 1, y):
            yield 1, a, b


def compressed_points(vertices, edges):
    points = []
    for p in vertices:
        if len(p) != 2 or any(type(c) is not int for c in p):
            raise ValueError('vertices must be integer coordinate pairs')
        points.append(tuple(p))
    if len(set(points)) != len(points):
        raise ValueError('coincident input vertices')
    used = {i for edge in edges for i in edge}
    for i in set(range(len(points))) - used:
        x, y = points[i]
        for a, b in edges:
            (ax, ay), (bx, by) = points[a], points[b]
            if min(ax, bx) <= x <= max(ax, bx) and min(ay, by) <= y <= max(ay, by):
                raise ValueError('an isolated vertex lies on a source edge')
    ranks = [{c: i for i, c in enumerate(sorted({points[v][j] for v in used}), start=1)}
             for j in (0, 1)]
    return {v: (2 * ranks[0][points[v][0]], 2 * ranks[1][points[v][1]]) for v in used}


def source_edges(edges, n):
    result = []
    seen = set()
    for pair in edges:
        if len(pair) != 2 or any(type(i) is not int or not 0 <= i < n for i in pair):
            raise ValueError('edge endpoint outside vertex list')
        a, b = sorted(pair)
        if a == b or (a, b) in seen:
            raise ValueError('input graph must be simple')
        seen.add((a, b))
        result.append((a, b))
    return sorted(result)


def coarse_wiring(points, edges):
    ports = defaultdict(set)
    occupied = set(points.values())
    for a, b in edges:
        p, q = points[a], points[b]
        step, length = axial(p, q)
        reverse = scale(step, -1)
        ports[p].add(step)
        ports[q].add(reverse)
        for distance in range(1, length):
            hub = translate(p, step, distance)
            if hub in occupied:
                raise ValueError(f'edge interiors must be disjoint from other edges and vertices at {hub}')
            occupied.add(hub)
            ports[hub].update((step, reverse))
    if any(len(directions) > 3 for directions in ports.values()):
        raise ValueError('maximum source degree is three')
    switches = set()
    for a, b in edges:
        p, q = points[a], points[b]
        skips = int(len(ports[p]) == 3) + int(len(ports[q]) == 3)
        if skips % 2 == 0:
            step, _ = axial(p, q)
            switches.add(translate(p, step))
    return ports, switches


@cache
def templates():
    data = json.loads(Path(__file__).with_name('stencils.json').read_text())
    for core in data.values():
        if core['radius'] != 3 or set(core['phases']) != {0}:
            raise ValueError('expected phase-zero cores of radius three')
    return data


def oriented(p, basis):
    u, v = basis
    return (p[0] * u[0] + p[1] * v[0], p[0] * u[1] + p[1] * v[1])


@cache
def owned_tile(port_set, switch):
    directions = set(port_set)
    if switch:
        name = 'switch'
    elif len(directions) == 1:
        name = 'end'
    elif len(directions) == 3:
        name = 'tee'
    elif all(scale(d, -1) in directions for d in directions):
        name = 'line'
    else:
        name = 'corner'

    data = templates()[name]
    original = [tuple(d) for d in data['directions']]
    # The formal model maps world coordinates to canonical local coordinates.
    # Enumerate its eight choices in the same order, using the inverse on points.
    for swap in (False, True):
        for sx, sy in ((1, 1), (-1, 1), (1, -1), (-1, -1)):
            basis = ((0, sx), (sy, 0)) if swap else ((sx, 0), (0, sy))
            if {oriented(d, basis) for d in original} == directions:
                guards = {oriented(p, basis) for p in data['guards']}
                options = {oriented(p, basis) for p in data['options']}
                for d in directions:
                    flank = (-d[1], d[0])
                    for t in range(4, HALF + 1):
                        center = scale(d, t)
                        options.add(center)
                        if t % 4 in (0, 1):
                            guards.update((translate(center, flank), translate(center, flank, -1)))
                return frozenset(guards), frozenset(options), basis
    raise ValueError(f'no orientation for {name} and {directions}')


def physical_path(p, q, ports, switches, bases):
    step, distance = axial(p, q)
    start = scale(p, PITCH)
    end_index = PITCH * distance
    switch_hub = translate(p, step)
    # Only the first interior coarse site of this directed source edge may switch.
    has_switch = switch_hub in switches
    result = []
    for t in range(end_index + 1):
        if (t == 1 and len(ports[p]) == 3) or (t == end_index - 1 and len(ports[q]) == 3):
            continue
        if has_switch and abs(t - PITCH) <= 1:
            if t == PITCH:
                u, v = bases[switch_hub]
                orientation = 1 if u == step else -1
                mid = scale(switch_hub, PITCH)
                result.extend((translate(mid, v, orientation), translate(mid, v, -orientation)))
        else:
            result.append(translate(start, step, t))
    return tuple(result)


@dataclass
class Reduction:
    required: set[Edge]
    budget: int
    guards: set[Point]
    optional: set[Point]
    paths: dict[tuple[int, int], tuple[Point, ...]]
    hubs: dict[int, Point]
    offset: int


def reduce_drawing(vertices, edges, budget):
    if type(budget) is not int or budget < 0:
        raise ValueError('Vertex Cover budget must be a nonnegative integer')
    unordered = source_edges(edges, len(vertices))
    points = compressed_points(vertices, unordered)
    edges = [(a, b) if points[a] < points[b] else (b, a) for a, b in unordered]
    ports, switches = coarse_wiring(points, edges)
    guards, optional, bases = set(), set(), {}
    for site, directions in ports.items():
        local_guards, local_options, basis = owned_tile(tuple(sorted(directions)), site in switches)
        physical = scale(site, PITCH)
        guards.update(translate(physical, off) for off in local_guards)
        optional.update(translate(physical, off) for off in local_options)
        bases[site] = basis

    paths = {(a, b): physical_path(points[a], points[b], ports, switches, bases) for a, b in edges}
    hubs = {i: scale(p, PITCH) for i, p in points.items()}
    offset = len(guards) + sum((len(path) - 2) // 2 for path in paths.values())
    exact_budget = min(len(guards) + len(optional), offset + budget)
    required = {edge for center in guards | optional for edge in perimeter(center)}
    return Reduction(required, exact_budget, guards, optional, paths, hubs, offset)


def main():
    if hasattr(sys, 'set_int_max_str_digits'):
        # Coordinates and the budget can have arbitrarily long decimal encodings.
        sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    args = parser.parse_args()
    case = json.loads(args.input.read_text())
    result = reduce_drawing(case['vertices'], case['edges'], case['budget'])
    print(json.dumps({'unit_edges': sorted(result.required), 'exact_budget': result.budget}, separators=(',', ':')))


if __name__ == '__main__':
    main()
