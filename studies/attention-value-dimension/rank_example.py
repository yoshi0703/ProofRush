"""Certify an integer full-rank minor by deterministic elimination modulo a prime."""
from itertools import repeat
from math import isqrt
from random import Random

PRIME = 1_000_000_007
HEADS, DEGREE, WIDTH = 30, 6, 4


def multiply(left, right):
    coefficients = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            coefficients[i + j] = (coefficients[i + j] + a * b) % PRIME
    return coefficients


def power_vectors(size, total):
    """All exponents of homogeneous monomials of the stated total degree."""
    if size == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in power_vectors(size - 1, total - first):
            yield (first, *rest)


def rank_mod_prime(matrix):
    rows, columns = len(matrix), len(matrix[0])
    rank = 0
    for col in range(columns):
        pivot = next((r for r in range(rank, rows) if matrix[r][col]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        invert_pivot = pow(matrix[rank][col], -1, PRIME)
        for row in matrix[rank + 1:]:
            factor = row[col] * invert_pivot % PRIME
            if factor:
                for j in range(col, columns):
                    row[j] = (row[j] - factor * matrix[rank][j]) % PRIME
        rank += 1
        if rank == rows:
            break
    return rank


assert all(PRIME % d for d in range(2, isqrt(PRIME) + 1))
denominator = [1]
for a in range(1, HEADS + 1):
    denominator = multiply(denominator, [a, 1])
rng = Random(27)
forms = [denominator] + [[rng.randrange(-8, 9) for _ in range(HEADS + 1)] for _ in range(WIDTH)]
rows = HEADS * DEGREE + 1
columns = []
for powers in power_vectors(len(forms), DEGREE):
    polynomial = [1]
    for form, power in zip(forms, powers):
        for factor in repeat(form, power):
            polynomial = multiply(polynomial, factor)
    columns.append(polynomial + [0] * (rows - len(polynomial)))
matrix = [list(row) for row in zip(*columns)]
rank = rank_mod_prime(matrix)
assert rank == rows
print(f"H={HEADS} D={DEGREE} value_channels={WIDTH} modulus={PRIME} "
      f"columns={len(columns)} rows={rows} rank={rank}")
