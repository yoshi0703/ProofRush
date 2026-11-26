#!/usr/bin/env python3
"""Independently replay all pair-offset certificates for the 43r > 13n bound.

Run: python3 -B independent_rank.py
Only Python's standard library is needed. No functions or data are imported
from the original certificate generator. Indicator-matrix ranks are computed
by Gaussian elimination over GF(3), with a GF(2) fallback if needed.
"""
from collections import Counter
from fractions import Fraction
from itertools import product

SUBSTITUTION = {1: (1, 2), 2: (2, 3), 3: (1, 4), 4: (3, 2)}
ALLOWED_PAIRS = {
    (1, 2), (1, 4), (2, 1), (2, 2), (2, 3),
    (3, 1), (3, 2), (4, 1), (4, 2),
}
FACTOR_LENGTH = {
    **dict.fromkeys(range(21, 26), 129),
    **dict.fromkeys(range(26, 30), 137),
    30: 139, 31: 145, 32: 145, 33: 166, 34: 167,
    35: 168, 36: 169, 37: 177, 38: 177, 39: 177, 40: 257,
}


def substitute(word, iterations):
    """Apply the literal substitution, returning an immutable tuple."""
    for _ in range(iterations):
        word = tuple(symbol for letter in word for symbol in SUBSTITUTION[letter])
    return word


def gaussian_rank_mod(rows, prime, target_rank):
    """Row-reduce over GF(prime), stopping as soon as target_rank is reached."""
    basis = {}
    for row in rows:
        row = list(row)
        for column in range(len(row)):
            if row[column] == 0:
                continue
            if column in basis:
                multiplier = row[column]
                pivot = basis[column]
                for j in range(column, len(row)):
                    row[j] = (row[j] - multiplier * pivot[j]) % prime
                continue
            inverse = pow(row[column], -1, prime)
            basis[column] = [(value * inverse) % prime for value in row]
            if len(basis) >= target_rank:
                return len(basis)
            break
    return len(basis)


def indicator_rows(word, width):
    """Encode each width-letter factor by concatenated four-coordinate indicators."""
    rows = []
    for start in range(len(word) - width + 1):
        row = [0] * (4 * width)
        for offset, letter in enumerate(word[start:start + width]):
            row[4 * offset + letter - 1] = 1
        rows.append(row)
    return rows


def certificate_method(word, order):
    """Find a successor, predecessor, or independent modular-rank witness."""
    successors = {}
    for start in range(len(word) - order):
        block = word[start:start + order]
        next_letter = word[start + order]
        if block in successors and successors[block] != next_letter:
            return "unequal successors"
        successors[block] = next_letter

    predecessors = {}
    for start in range(1, len(word) - order + 1):
        block = word[start:start + order]
        previous_letter = word[start - 1]
        if block in predecessors and predecessors[block] != previous_letter:
            return "unequal predecessors"
        predecessors[block] = previous_letter

    for width in (order + 1, order + 2):
        rows = indicator_rows(word, width)
        for prime in (3, 2):
            rank = gaussian_rank_mod(rows, prime, 3 * order + 2)
            if rank > 3 * order + 1:
                return f"GF({prime}) rank, width u+{width - order}"
    return None


def integer_determinant(matrix):
    """Exact fraction-free Bareiss elimination; the input here is only 4x4."""
    matrix = [list(row) for row in matrix]
    sign = 1
    previous_pivot = 1
    for k in range(len(matrix) - 1):
        if matrix[k][k] == 0:
            swap = next(i for i in range(k + 1, len(matrix)) if matrix[i][k])
            matrix[k], matrix[swap] = matrix[swap], matrix[k]
            sign = -sign
        pivot = matrix[k][k]
        for i in range(k + 1, len(matrix)):
            for j in range(k + 1, len(matrix)):
                numerator = matrix[i][j] * pivot - matrix[i][k] * matrix[k][j]
                assert numerator % previous_pivot == 0
                matrix[i][j] = numerator // previous_pivot
        previous_pivot = pivot
    return sign * matrix[-1][-1]


def check_morphism():
    """Check the pair cover, base codeword determinant and aggregation maps."""
    internal_pairs = set(SUBSTITUTION.values())
    boundary_pairs = {(SUBSTITUTION[a][-1], SUBSTITUTION[b][0]) for a, b in ALLOWED_PAIRS}
    assert internal_pairs <= ALLOWED_PAIRS
    assert boundary_pairs <= ALLOWED_PAIRS
    seed = substitute((1,), 5)
    assert set(zip(seed, seed[1:])) == ALLOWED_PAIRS
    assert integer_determinant([substitute((letter,), 2) for letter in range(1, 5)]) == 10
    # The exact grouping equations are printed below. This finite check is a
    # supplementary sanity test, not a replacement for their algebraic proof.
    for coefficients in product(range(-2, 3), repeat=4):
        first = [sum(coefficients[i] for i in range(4)
                     if SUBSTITUTION[i + 1][0] == letter) for letter in range(1, 5)]
        second = [sum(coefficients[i] for i in range(4)
                      if SUBSTITUTION[i + 1][1] == letter) for letter in range(1, 5)]
        if not any(first + second):
            assert not any(coefficients)
    print("Pair closure and occurrence checks passed; four-codeword determinant = 10.")
    print("Grouping maps: (c1+c3,c2,c4,0) and (0,c1+c4,c2,c3).")


def main():
    check_morphism()
    total_offsets = 0
    all_methods = Counter()
    for order, factor_length in FACTOR_LENGTH.items():
        block_length = 1 << (factor_length - 1).bit_length()
        iterations = block_length.bit_length() - 1
        factors = set()
        for pair in sorted(ALLOWED_PAIRS):
            expanded_pair = substitute(pair, iterations)
            for offset in range(block_length):
                factor = expanded_pair[offset:offset + factor_length]
                assert len(factor) == factor_length
                factors.add(factor)
        methods = Counter()
        for factor in sorted(factors):
            method = certificate_method(factor, order)
            if method is None:
                raise AssertionError(f"Uncovered factor at order {order}: {factor}")
            methods[method] += 1
        assert Fraction(factor_length + 1, order - 1) <= Fraction(86, 13)
        offsets = len(ALLOWED_PAIRS) * block_length
        total_offsets += offsets
        all_methods.update(methods)
        print(f"u={order} K={factor_length} offsets={offsets} distinct={len(factors)} "
              f"ratio={(Fraction(factor_length + 1, order - 1))} methods={dict(methods)}", flush=True)
    assert total_offsets == 48384
    print(f"PASS: {total_offsets} raw pair-offset checks; methods over distinct factors: {dict(all_methods)}")


if __name__ == "__main__":
    main()
