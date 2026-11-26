"""Construct and check forced losses for specified inverse words and ternary classes."""

from fractions import Fraction
from functools import lru_cache
from itertools import product


# A letter (bits, offset) represents the inverse (2^bits * g - offset) / 9.
LETTERS = ((3, 1), (3, -1), (4, 5), (4, -5))


def children(n):
    def odd_part(value):
        return value // (value & -value)

    return odd_part(3 * n + 1), odd_part(3 * n - 1)


@lru_cache(maxsize=100_000)
def wins_in(n, plies):
    return n > 1 and plies > 0 and any(
        child == 1 or loses_in(child, plies - 1) for child in children(n)
    )


@lru_cache(maxsize=100_000)
def loses_in(n, plies):
    return n > 1 and plies > 0 and all(
        child > 1 and wins_in(child, plies - 1) for child in children(n)
    )


def seed_in_class(residue, h):
    """Compute an exponent by lifting (64^m-1)/9 one ternary digit at a time."""
    exponent, period = 0, 1
    for _ in range(h):
        modulus = 27 * period
        matches = [exponent + digit * period for digit in range(3)
                   if pow(64, exponent + digit * period, modulus) == (9 * residue + 1) % modulus]
        assert len(matches) == 1
        exponent = matches[0]
        period *= 3
    while exponent < 2:
        exponent += period
    return ((1 << (6 * exponent)) - 1) // 9


def loss_after_word(word, residue, h):
    """Word lists the innermost map first. Fix the final residue before picking the seed."""
    multiplier, offset, denominator = 1, 0, 1
    for bits, shift in word:
        multiplier <<= bits
        offset = (offset << bits) + shift * denominator
        denominator *= 9
    modulus = denominator * 3**h
    required = (offset + denominator * residue) * pow(multiplier, -1, modulus) % modulus
    start = seed_in_class(required, h + 2 * len(word))
    assert loses_in(start, 2)
    for depth, (bits, shift) in enumerate(word, start=1):
        start, remainder = divmod((start << bits) - shift, 9)
        assert remainder == 0 and loses_in(start, 2 + 2 * depth)
    assert start % 3**h == residue % 3**h
    return start


def main():
    # Since 9 is odd its inverse modulo 2^k exists, so each image is an entire odd ball.
    images = []
    for bits, shift in LETTERS:
        modulus = 2 ** (bits + 1)
        residue = ((1 << bits) - shift) * pow(9, -1, modulus) % modulus
        images.append((residue, modulus))
    assert images == [(15, 16), (1, 16), (19, 32), (13, 32)]
    assert len({r % 16 for r, _ in images}) == 4

    checked = 0
    for length in range(3):
        for word in product(LETTERS, repeat=length):
            for residue in range(9):
                loss_after_word(word, residue, 2)
                # To control w modulo nine, control g modulo twenty-seven.
                child_class = (1 + 3 * residue) * pow(2, -1, 27) % 27
                losing_child = loss_after_word(word, child_class, 3)
                winner, remainder = divmod(2 * losing_child - 1, 3)
                assert remainder == 0 and winner % 9 == residue
                assert wins_in(winner, 3 + 2 * length)
                checked += 1

    def polynomial(x):
        return x**4 - 2 * x - 2

    assert polynomial(Fraction(14945, 10000)) < 0 < polynomial(Fraction(14946, 10000))
    print(f"Checked {checked} word/residue pairs, each with a forced loss and a forced win.")
    print("The four dyadic image balls have residues/moduli", images)


if __name__ == "__main__":
    main()
