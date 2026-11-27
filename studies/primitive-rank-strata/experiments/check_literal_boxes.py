"""Recheck the concrete witnesses directly in Kászonyi's cyclic coordinates."""
from itertools import combinations, product
from math import prod


def box_coefficients(n, origin, primes):
    return {
        (origin + sum(r * (n // p) for r, p in zip(bits, primes))) % n:
            (-1) ** sum(bits)
        for bits in product((0, 1), repeat=len(primes))
    }


def check(primes, rank, n=None):
    squarefree = prod(primes)
    n = n or squarefree
    theta = n // squarefree
    values = tuple(1 + sum(all((i // theta) % p == 0 for p in active)
                           for active in combinations(primes, rank))
                   for i in range(n))
    for size in range(1, len(primes) + 1):
        for axes in combinations(primes, size):
            deltas = [sum(values[i] * s for i, s in box_coefficients(n, b, axes).items())
                      for b in range(n)]
            assert (any(deltas)) == (size <= rank)
            assert deltas[0] == (sum(set(axes) <= set(active)
                                     for active in combinations(primes, rank)))
    word = "".join("a" + "b" * e for e in values)
    assert all(word != word[:d] * (len(word) // d)
               for d in range(1, len(word)) if len(word) % d == 0)
    supports = {b: set(box_coefficients(n, b, primes)) for b in range(n)}
    excluded = 0
    for i, j in combinations(range(n), 2):
        isolated = any(i in points and j not in points for points in supports.values())
        antipodal = 2 in primes and (j-i) % n == n // 2
        assert isolated == (not antipodal)
        excluded += int(isolated)
    print(f"n={n}, rank={rank}, word length={len(word)}, "
          f"{excluded} of {n*(n-1)//2} support pairs separated by a top box")


def check_published_example():
    e = tuple(map(int, "243353153443254234263244342345"))
    actual = {
        axes
        for size in (1, 2, 3)
        for axes in combinations((2, 3, 5), size)
        if any(sum(e[j] * c for j, c in box_coefficients(30, i, axes).items())
               for i in range(30))
    }
    assert actual == {(2,), (3,), (5,), (2, 5)}
    print("Published Example 2 has one nonzero pair difference and zero triple difference")


if __name__ == "__main__":
    check((2, 3), 1)
    check((2, 3), 1, 12)
    check((3, 5), 1)
    check((3, 5, 7), 2)
    check_published_example()
