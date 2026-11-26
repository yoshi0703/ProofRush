"""An exact check for survey carryover estimates, including interference."""
from fractions import Fraction
from itertools import combinations
from math import comb


def contrast(counts, previous, population=20):
    """Unbiased two-stage estimate of the previous assignment contrast."""
    n = len(counts)
    p = Fraction(len(previous), population)
    ys = sum(counts.values())
    n_revisited = sum(i in previous for i in counts)
    visited_sum = sum(y for i, y in counts.items() if i in previous)
    centered = visited_sum - Fraction(n_revisited * ys, n)
    return centered * (population - 1) / (population * (n - 1) * p * (1 - p))


def outcome(i, previous, population):
    # A deliberately heterogeneous response, affected by assignments to neighbors.
    return (2*i + 1) ** 2 + 3 * (i not in previous) + 7 * ((i+1) % population in previous)


def check(N, m, n):
    indices = range(N)
    both_stages = Fraction(0)
    for a in combinations(indices, m):
        all_y = [outcome(i, a, N) for i in indices]
        population_diff = (Fraction(sum(all_y[i] for i in a), m) -
                           Fraction(sum(all_y[i] for i in indices if i not in a), N-m))
        at_a = sum(contrast({i: all_y[i] for i in b}, a, N)
                   for b in combinations(indices, n)) / comb(N, n)
        assert population_diff == at_a
        both_stages += at_a
    both_stages /= comb(N, m)
    swaps = Fraction(0)
    for i in indices:
        for j in indices:
            if i == j:
                continue
            remaining = [v for v in indices if v not in {i,j}]
            swaps += sum(outcome(i, (*a,i), N) - outcome(i, (*a,j), N)
                         for a in combinations(remaining, m-1))
    swaps /= N*(N-1)*comb(N-2, m-1)
    assert swaps == both_stages
    return both_stages


if __name__ == '__main__':
    cases = [(N,m,n) for N in range(3,8) for m in range(1,N) for n in range(2,N+1)]
    for args in cases:
        check(*args)
    print(f'Exact nested randomization and swap contrast verified for {len(cases)} designs.')
