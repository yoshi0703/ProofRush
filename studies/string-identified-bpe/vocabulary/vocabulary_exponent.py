"""Exact checks for a compressed unary-spelling diamond family."""
from collections import Counter, defaultdict
from math import isqrt


def euler_groups(m):
    side = isqrt(m - 1) + 2
    options = [[i for i in range(side) if i != j] for j in range(side)]
    stack = [0]
    reverse = []
    while stack:
        j = stack[-1]
        if options[j]:
            stack.append(options[j].pop())
        else:
            reverse.append(stack.pop())
    groups = reverse[::-1][:m]
    assert len(groups) == m and len(set(zip(groups, groups[1:]))) == m - 1
    return side, groups


def form(k, m):
    layers_count = k // (2 * m)
    assert layers_count >= m
    side, groups = euler_groups(layers_count)
    base = 2 * side * m + 1

    def u(j, i):
        return groups[j] * m + i + 1

    def v(j, i):
        return base - u(j, i)

    core = []
    rules = []
    for j in range(layers_count):
        hub = (j + 1) * base
        for i in range(m):
            rules.extend([(u(j, i), hub), (hub + u(j, i), v(j, i))])
    for s in range(m):
        for x in range(m):
            for y in range(m):
                layers = [(j, (x, y)[j % 2]) for j in range(s, layers_count)]
                core.append([u(j, i) for j, i in layers[::-1]] + [(s + 1) * base]
                            + [v(j, i) for j, i in layers])

    side_private = isqrt(k - 1) + 1
    scale = (layers_count + 1) * base + 1
    radix = side_private + 1
    pairs = [((a + 1) * scale, (b + 2) * radix * scale)
             for a in range(side_private) for b in range(side_private)][:k]
    assert len({a + b for a, b in pairs}) == k
    decoys = [list(pair) for pair in pairs for _ in range(m + 1)]
    return layers_count, base, core, decoys, rules, pairs


def boundary_options(row, in_decoy):
    if in_decoy:
        combined = sum(row)
        return {row[0], combined}, {row[-1], combined}
    return {row[0]}, {row[-1]}


def guard_colors(rows, n_core, m):
    choices = [boundary_options(row, i >= n_core) for i, row in enumerate(rows)]
    resources = [[(0, ending) for ending in choices[i][1]] +
                 [(1, start) for start in choices[i+1][0]]
                 for i in range(len(rows) - 1)]
    load = Counter(item for choices in resources for item in choices)
    cap = 4 * (max(load.values(), default=0) // m) + 1
    colors = []
    occupancy = defaultdict(Counter)
    for boundary in resources:
        forbidden = set()
        for resource in boundary:
            forbidden.update(color for color, count in occupancy[resource].items() if count >= m)
        choice = next(color for color in range(cap) if color not in forbidden)
        colors.append(choice)
        for resource in boundary:
            occupancy[resource][choice] += 1
    for assignments in occupancy.values():
        assert max(assignments.values()) <= m
    return colors


def scan(stream, pair):
    result = []
    i = 0
    while i < len(stream):
        if i + 1 < len(stream) and (stream[i], stream[i+1]) == pair:
            result.append(sum(pair))
            i += 2
        else:
            result.append(stream[i])
            i += 1
    return result


def counts(words):
    return Counter(pair for w in words for pair in zip(w, w[1:]))


def audit(k, m, *, exact_history):
    layers, base, core, decoys, comparator, pairs = form(k, m)
    assert len(core) == m**3 and len(comparator) <= k and len(pairs) == k
    assert max(counts(core).values()) <= m
    rows = core + decoys
    guard_start = max(map(sum, pairs)) + 1
    colors = guard_colors(rows, len(core), m)
    guards = [guard_start + color for color in colors]
    word = []
    for i, row in enumerate(rows):
        if i:
            word.append(guards[i - 1])
        word.extend(row)
    alphabet = len(set(word))
    assert alphabet <= (2 * len(set(euler_groups(layers)[1])) * m +
                        m + 2 * (isqrt(k - 1) + 1) + len(set(guards)))
    assert alphabet**2 <= 30**2 * k * m

    # Verify a scrambled greedy ordering against exact raw counts in the serialized word.
    # The universal tie conclusion follows separately from the all-endpoint guard certificate.
    compressed = word
    if exact_history:
        for merge in pairs[::2] + pairs[1::2]:
            raw = counts([compressed])
            assert raw[merge] == max(raw.values()) == m + 1
            after = scan(compressed, merge)
            assert len(compressed) - len(after) == m + 1
            compressed = after
        assert len(word) - len(compressed) == k * (m + 1)

        compressed = word
        for merge in comparator:
            compressed = scan(compressed, merge)
        utility = m**3 * (2 * layers - m + 1)
        assert len(word) - len(compressed) == utility
        assert compressed.count((layers + 1) * base) == m**3
        assert k * (m + 1) * m <= 4 * utility

    return layers, alphabet, len(set(guards)), len(word)


if __name__ == "__main__":
    checked = 0
    for k in [2, 7, 8, 18, 27, 32, 48, 50, 71, 72, 95, 98, 128, 162, 200, 242, 288, 337,
              512, 1024, 2500]:
        most = isqrt(k // 2)
        for m in sorted({1, max(1, most // 2), most}):
            check_history = k <= 337
            layers, alphabet, guard_count, length = audit(k, m, exact_history=check_history)
            checked += int(check_history)
            print(f"k={k:4d} m={m:2d} L={layers:4d} initial_types={alphabet:4d} "
                  f"guards={guard_count:3d} initial_tokens={length}")
    print(f"Replayed {checked} complete comparator and greedy histories.")
