"""Exact finite replays of the two-sided construction. Positive integers are unary spelling lengths."""
from collections import Counter
from fractions import Fraction
from math import isqrt


def labels(m, level, variant):
    base = 2 * m * m + 1
    left = level * m + variant + 1
    return left, (level + 1) * base, base - left


def corpus(m):
    rows = Counter()
    for seed in range(m):
        for x in range(m):
            for y in range(m):
                row = [(seed + 1) * (2 * m * m + 1)]
                for level in range(seed, m):
                    left, _, right = labels(m, level, x if level % 2 == 0 else y)
                    row = [left, *row, right]
                rows[tuple(row)] += 1
    return rows


def raw_scores(rows):
    freq = Counter()
    for row, weight in rows.items():
        for pair in zip(row, row[1:]):
            freq[pair] += weight
    return freq


def full(row, pair):
    changed = []
    pos = 0
    while pos < len(row):
        if row[pos:pos+2] == pair:
            changed.append(sum(pair))
            pos += 2
        else:
            changed.append(row[pos])
            pos += 1
    return tuple(changed)


def apply(rows, pair):
    new = Counter()
    total = 0
    for row, weight in rows.items():
        out = full(row, pair)
        total += weight * (len(row) - len(out))
        new[out] += weight
    return new, total


def run(m, budget):
    assert m >= 1 and budget >= 2*m*m
    core = corpus(m)
    initial = raw_scores(core)
    assert max(initial.values()) == m
    assert all(a != b for a, b in initial)
    assert sum(core.values()) == m**3
    # All color choices are independent on consecutive levels. Need no sampled rows.
    rows = core
    total = 0
    for level in range(m):
        for variant in range(m):
            left, hub, right = labels(m, level, variant)
            rows, first = apply(rows, (left, hub))
            rows, second = apply(rows, (left + hub, right))
            assert first == second == (level + 1) * m
            total += first + second
    last_hub = (m+1) * (2*m*m+1)
    assert rows == {(last_hub,): m**3} and total == m**3*(m+1)

    # Distinct private unary spellings above all core tokens. Their products do
    # not occur in any other row. Single-token rows have zero internal pairs.
    private_start = last_hub + 2*budget + 1
    private = [(private_start + i, private_start + i) for i in range(budget)]
    records = core.copy()
    for pair in private:
        records[pair] = m + 1
    # On two-token private rows, raw ranking equals disjoint replacement ranking.
    # Verify the full maximizing set after each prefix of the given greedy order.
    accumulated = 0
    for i, pair in enumerate(private):
        values = raw_scores(records)
        best = max(values.values())
        assert best == m+1
        assert {p for p, freq in values.items() if freq == best} == set(private[i:])
        records, gain = apply(records, pair)
        assert gain == best
        accumulated += gain
    assert accumulated == budget*(m+1)
    return Fraction(accumulated, total)


if __name__ == '__main__':
    for m in range(1, 9):
        budget = 2*m*m
        ratio = run(m, budget)
        assert ratio == Fraction(2, m)
        print(f'm={m} budget={budget} greedy={budget*(m+1)} comparator={m**3*(m+1)} upper={ratio}')
    for k in (19, 37, 54, 77, 109):
        m = isqrt(k//2)
        assert run(m, k) == Fraction(k, m**3)
