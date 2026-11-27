#!/usr/bin/env python3
"""Finite, exact replay for the independent Kászonyi stratum audit."""

from itertools import combinations, product
import json
from math import comb, prod


def box(n, base, shifts):
    """Signed corner map, using the paper's modulo-n indices and parity signs."""
    corners = {}
    for choices in product((0, 1), repeat=len(shifts)):
        index = (base + sum(b * step for b, step in zip(choices, shifts))) % n
        assert index not in corners
        corners[index] = (-1) ** sum(choices)
    return corners


def mixed_difference(values, base, shifts):
    corners = box(len(values), base, shifts)
    return sum(values[index] * sign for index, sign in corners.items())


def sparse_kernel_check(n, primes, order):
    # Each matrix column records the coefficients of one coordinate across all
    # canonical mixed differences. A pair is linearly dependent exactly when
    # its nonempty columns agree up to sign, since all entries are 0 or ±1.
    columns = [[] for _ in range(n)]
    for subset in combinations(primes, order):
        shifts = tuple(n // p for p in subset)
        for base in range(n):
            for index, sign in box(n, base, shifts).items():
                columns[index].append((subset, base, sign))
    assert all(columns)
    negative = [
        [(subset, base, -sign) for subset, base, sign in column]
        for column in columns
    ]
    zero_sum_pairs = []
    for x, y in combinations(range(n), 2):
        assert columns[x] != columns[y]
        if columns[x] == negative[y]:
            zero_sum_pairs.append((x, y))
    expected = []
    if n % 2 == 0 and order == len(primes):
        expected = [(x, x + n // 2) for x in range(n // 2)]
    assert zero_sum_pairs == expected
    crossing_pairs = 0
    for (x, antipode_x), (y, antipode_y) in combinations(zero_sum_pairs, 2):
        assert x < y < antipode_x < antipode_y
        crossing_pairs += 1
    return {
        "canonical_rows": comb(len(primes), order) * n,
        "support_pairs_examined": comb(n, 2),
        "equal_coefficient_kernel_pairs": len(zero_sum_pairs),
        "crossing_among_kernel_pairs": crossing_pairs,
    }


def actual_word_is_primitive(gaps):
    word = "".join("a" + "b" * exponent for exponent in gaps)
    for root_length in range(1, len(word) // 2 + 1):
        if len(word) % root_length == 0:
            if word == word[:root_length] * (len(word) // root_length):
                return False
    return True


def ray_check(prime_powers, alpha):
    primes = tuple(prime_powers)
    n = prod(p ** e for p, e in prime_powers.items())
    power_products = [
        prod(p ** prime_powers[p] for p in subset)
        for subset in combinations(primes, alpha)
    ]
    ray = [sum(i % v == 0 for v in power_products) for i in range(n)]
    for t in (1, 2, 5, 9):
        assert actual_word_is_primitive([t * x for x in ray])
    lower_witnesses = 0
    high_rows = 0
    for order in range(1, len(primes) + 1):
        for subset in combinations(primes, order):
            for units in product(*(range(1, p) for p in subset)):
                shifts = tuple(t * (n // p) for p, t in zip(subset, units))
                if order <= alpha:
                    assert mixed_difference(ray, 0, shifts) == comb(
                        len(primes) - order, alpha - order
                    )
                    lower_witnesses += 1
                else:
                    assert all(mixed_difference(ray, x, shifts) == 0 for x in range(n))
                    high_rows += n
    return {
        "n": n,
        "prime_powers": prime_powers,
        "alpha": alpha,
        "lower_witnesses_all_unit_scales": lower_witnesses,
        "higher_rows_all_bases_and_unit_scales": high_rows,
        "literal_words_tested_for_proper_power": 4,
        "kernel": sparse_kernel_check(n, primes, alpha + 1),
    }


def source_example_check():
    n = 30
    values = [
        i % 2 + (0, 0, 1, 1, 2)[i % 5] + (1, 3, 2)[i % 3] + (i % 10 == 0)
        for i in range(n)
    ]
    assert values == [
        2, 4, 3, 3, 5, 3, 1, 5, 3, 4, 4, 3, 2, 5, 4,
        2, 3, 4, 2, 6, 3, 2, 4, 4, 3, 4, 2, 3, 4, 5,
    ]
    nonzero_mixed_pairs = []
    for p, q in combinations((2, 3, 5), 2):
        if any(mixed_difference(values, x, (n // p, n // q)) for x in range(n)):
            nonzero_mixed_pairs.append((p, q))
    assert nonzero_mixed_pairs == [(2, 5)]
    assert all(mixed_difference(values, x, (15, 10, 6)) == 0 for x in range(n))
    assert actual_word_is_primitive(values)
    return {"n": n, "nonzero_mixed_pairs": nonzero_mixed_pairs, "primitive": True}


def main():
    configurations = [
        {2: 1, 3: 1},
        {3: 1, 5: 1},
        {2: 1, 3: 2},
        {2: 1, 3: 1, 5: 1},
        {2: 2, 3: 1, 5: 1},
        {2: 1, 3: 2, 5: 1},
        {3: 1, 5: 1, 7: 1},
        {2: 1, 3: 1, 5: 1, 7: 1},
        {3: 2, 5: 1, 7: 1},
    ]
    print(json.dumps({
        "source_example_2": source_example_check(),
        "ray_and_kernel_checks": [
            ray_check(powers, alpha)
            for powers in configurations
            for alpha in range(1, len(powers))
        ],
    }, indent=2))


if __name__ == "__main__":
    main()
