"""Finite checks supporting the uniform rank note. Runs with Python 3.10+."""
from math import gcd, isqrt, prod
from overlap import expand, pair_representatives
from cross_check import bareiss


def prefix(minimum):
    word = "1"
    while len(word) < minimum:
        word = expand(word)
    return word[:minimum]


def complete_factors(length):
    block_size = 1 << (length - 1).bit_length()
    guaranteed = (max(pair_representatives().values()) + 2) * block_size
    word = prefix(guaranteed)
    return {word[i:i+length] for i in range(len(word) - length + 1)}


def matrix_rank(entries, shift, order, prime):
    matrix = [
        [v % prime for v in entries[shift+i:shift+i+order]]
        for i in range(order)
    ]
    rank = 0
    for col in range(order):
        pivot = next((i for i in range(rank, order) if matrix[i][col]), None)
        if pivot is None:
            continue
        matrix[pivot], matrix[rank] = matrix[rank], matrix[pivot]
        inv = pow(matrix[rank][col], -1, prime)
        for i in range(rank + 1, order):
            coefficient = matrix[i][col] * inv % prime
            if coefficient:
                for j in range(col, order):
                    matrix[i][j] = (matrix[i][j] - coefficient*matrix[rank][j]) % prime
        rank += 1
    return rank


def rank_gap_checks(entries):
    checked = 0
    for prime in [5,7,11,13]:
        for shift in range(13):
            ranks = [matrix_rank(entries,shift,n,prime) for n in range(1,35)]
            nonsingular = [n for n,r in enumerate(ranks,1) if r==n]
            for previous, following in zip(nonsingular,nonsingular[1:]):
                assert following <= 13*previous
                for n in range(previous+1,following):
                    assert ranks[n-1] == max(previous,2*n-following)
                    checked += 1
    return checked


def primes_up_to(limit):
    return [
        x for x in range(2,limit+1)
        if not any(x%d == 0 for d in range(2,isqrt(x)+1))
    ]


def prime_obstructions(entries, limit):
    primes = primes_up_to(limit)
    remaining = prod(primes)
    witnesses = {}

    def observe(determinant, shift, order):
        nonlocal remaining
        factors = gcd(determinant,remaining)
        if factors > 1:
            for prime in primes:
                if factors % prime == 0:
                    remaining //= prime
                    factors //= prime
                    witnesses[prime] = (shift, order, determinant)
                    if factors == 1:
                        break

    previous = [1] * len(entries)
    current = entries
    for i, value in enumerate(current):
        observe(value,i,1)
    for order in range(2,(len(entries)+1)//2+1):
        next_row = []
        for shift in range(len(current)-2):
            numerator = current[shift]*current[shift+2]-current[shift+1]**2
            value, remainder = divmod(numerator,previous[shift+2])
            assert remainder == 0 and value
            observe(value,shift,order)
            next_row.append(value)
        if remaining == 1:
            break
        previous,current = current,next_row
    uncovered = [p for p in primes if p not in witnesses]
    return witnesses, uncovered


def main():
    counts = [len(complete_factors(n)) for n in range(1,10)]
    assert counts == [4,9,15,22,28,35,42,49,56], counts
    print("Exact factor counts for lengths 1–9:", counts)

    entries = list(map(int,prefix(1024)))
    print("Verified singular-order gap formulas:", rank_gap_checks(entries))
    witnesses, uncovered = prime_obstructions(entries,25000)
    print("Prime obstructions:",len(witnesses),"uncovered:",uncovered)
    assert not uncovered
    for p in (2,3,5,7,11,13,997,24989):
        print("p="+str(p),witnesses[p])
    for prime, shift, order, expected_rank, expected_constant, expected_slope in (
        (5,31,5,3,25,10), (11,39,10,8,11979,5324)
    ):
        rows = [entries[shift+i:shift+i+order] for i in range(order)]
        constant = bareiss([row[:] for row in rows])
        slope = bareiss([[v+1 for v in row] for row in rows]) - constant
        assert (constant,slope)==(expected_constant,expected_slope)
        assert (constant % prime,slope % prime)==(0,0)
        assert matrix_rank(entries,shift,order,prime)==expected_rank
        print(f"Affine-lift obstruction: p={prime} shift={shift} order={order} polynomial={constant}+{slope}X")


if __name__ == "__main__":
    main()
