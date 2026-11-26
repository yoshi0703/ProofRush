#!/usr/bin/env python3
"""Exact check of the dyadic construction; the input is a sequence of string-valued atoms."""
from collections import Counter
from fractions import Fraction


def core_rows(budget, seeds):
    rows = Counter()
    for s in range(seeds):
        for period in ((0, 1), (0, 0, 1, 1)):
            for phase in range(len(period)):
                word = [2**s, 2**s]
                for j in range(s + 1, budget):
                    if period[(j + phase) % len(period)]:
                        word.append(2**j)
                    else:
                        word.insert(0, 2**j)
                rows[tuple(word)] += 1
    return rows


def full(row, pair):
    """Integers are exact unary spelling lengths. A private pair has its own letters."""
    result = []
    gain = 0
    i = 0
    while i < len(row):
        if row[i:i + 2] == pair:
            x, y = pair
            result.append(x + y if isinstance(x, int) else ('private product', x, y))
            i += 2
            gain += 1
        else:
            result.append(row[i])
            i += 1
    return tuple(result), gain


def stage(rows, pair):
    next_rows = Counter()
    total = 0
    for row, weight in rows.items():
        output, gain = full(row, pair)
        next_rows[output] += weight
        total += weight * gain
    return next_rows, total


def counts(rows):
    result = Counter()
    for word, weight in rows.items():
        last, odd = None, False
        for symbol in word:
            if last == symbol:
                if odd:
                    result[symbol, symbol] += weight
                odd = not odd
            else:
                if last is not None:
                    result[last, symbol] += weight
                last, odd = symbol, True
    return result


def check(budget, seeds):
    rows = core_rows(budget, seeds)
    maximum = max(counts(rows).values())
    bound = max(6, seeds + 2)
    assert maximum <= bound
    private = [(f'x{i}', f'y{i}') for i in range(budget)]
    for p in private:
        rows[p] += bound + 1
    greedy, compare = rows, rows
    greedy_gain, compare_gain = 0, 0
    for j, p in enumerate(private):
        scores = counts(greedy)
        top = max(scores.values())
        assert {q for q, score in scores.items() if score == top} == set(private[j:])
        greedy, gain = stage(greedy, p)
        greedy_gain += gain
        compare, gain = stage(compare, (2**j, 2**j))
        assert gain == 6 * min(j + 1, seeds)
        compare_gain += gain
    assert greedy_gain == budget * (bound + 1)
    assert compare_gain == 3 * seeds * (2 * budget - seeds + 1)
    return Fraction(greedy_gain, compare_gain)


if __name__ == '__main__':
    assert counts({(1, 1, 2): 1}) == Counter({(1, 1): 1, (1, 2): 1})
    # Checks include cases below the k,L >= 4 range stated in the theorem.
    for k in range(1, 31):
        for size in range(1, k + 1):
            check(k, size)
    assert check(4, 4) == Fraction(7, 15) < Fraction(15, 32)
    print('465 parameter pairs passed with exact counts, including all maximizing rule types.')
    print('k=4, L=4: every greedy order saves 28 and the comparator saves 60.')
