#!/usr/bin/env python3
"""Exact endpoint exponential bases and coefficients using one state per coordinate subset."""
from fractions import Fraction as F
from functools import cache
from itertools import permutations, product

from experiment import distribution, exact_terminal, uniform


def leading_term(target, competitor, word, verify_orders=False):
    """Return (K,C) for q_w(word) ~ C*K**w, with equal class priors."""
    assert target[word] > 0
    d = len(word)
    full = (1 << d) - 1

    @cache
    def exits(subset):
        visible = [j for j in range(d) if subset & (1 << j)]
        hidden = [j for j in range(d) if j not in visible]
        def fibers(weights):
            result = {}
            for x, mass in weights.items():
                if all(x[j] == word[j] for j in visible):
                    for j in hidden:
                        result[j, x[j]] = result.get((j, x[j]), 0) + mass
            return result
        p, q = fibers(target), fibers(competitor)
        posterior = {e: value / (value + q.get(e, 0)) for e, value in p.items() if value}
        maximum = max(posterior.values())
        # Unnormalized target cylinder masses share the same parent denominator.
        tied_mass = sum(p[e] for e in posterior if posterior[e] == maximum)
        return {j: (posterior[j, word[j]] / maximum, p[j, word[j]] / tied_mass) for j in hidden}

    @cache
    def backward(subset):
        if subset == full:
            return F(1), F(1)
        branches = []
        for j, (base, coeff) in exits(subset).items():
            child_base, child_coeff = backward(subset | (1 << j))
            branches.append((base * child_base, coeff * child_coeff))
        best = max(base for base, _ in branches)
        return best, sum(coeff for base, coeff in branches if base == best)

    result = backward(0)
    if verify_orders:
        best, total = F(0), F(0)
        for order in permutations(range(d)):
            subset, base, coeff = 0, F(1), F(1)
            for j in order:
                step_base, step_coeff = exits(subset)[j]
                base *= step_base
                coeff *= step_coeff
                subset |= 1 << j
            if base > best:
                best, total = base, F(0)
            if base == best:
                total += coeff
        assert result == (best, total)
    return result


def main():
    for d, exponent_base in [(2, F(17, 21)), (3, F(37, 57))]:
        zero, one = (0,) * d, (1,) * d
        target = distribution({zero: F(1, 4), one: F(3, 4)})
        other = uniform(x for x in product((0, 1), repeat=d) if x != zero)
        for word, expected in [(zero, (exponent_base, F(1, 3))), (one, (F(1), F(1)))]:
            assert leading_term(target, other, word, True) == expected
        print(f"D={d}: private mass asymptotic to (1/3)*({exponent_base})^w; shared mass tends to 1.")
    # Nonexchangeable classes. Different orders to the same endpoint can have different costs.
    words = list(product((0, 1), repeat=3))
    target = distribution(dict(zip(words, map(lambda v: F(v, 24), [2, 1, 3, 4, 6, 1, 2, 5]))))
    other = distribution(dict(zip(words, map(lambda v: F(v, 24), [5, 2, 0, 4, 1, 8, 3, 1]))))
    limiting_law = exact_terminal(target, other, None)
    for word in words:
        base, coeff = leading_term(target, other, word, True)
        assert 0 < base <= 1 and coeff > 0
        assert (coeff if base == 1 else 0) == limiting_law[word]
    print("All eight endpoint recursions agree with full path enumeration and the limiting chain.")


if __name__ == "__main__":
    main()
