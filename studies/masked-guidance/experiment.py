#!/usr/bin/env python3
"""Exact finite verification of ideal continuous-time masked CFG, using only Python's stdlib."""
from fractions import Fraction as F
from functools import cache
from itertools import permutations, product
from math import prod


def distribution(weights):
    assert all(weight >= 0 for weight in weights.values())
    assert sum(weights.values()) == 1
    return {word: weight for word, weight in weights.items() if weight}


def uniform(words):
    words = tuple(words)
    return {word: F(1, len(words)) for word in words}


def mixture(first, second, fraction):
    return distribution({x: fraction * first.get(x, 0) + (1 - fraction) * second.get(x, 0)
                         for x in first.keys() | second.keys()})


def independent(d, s):
    return distribution({word: prod(s if bit else 1 - s for bit in word)
                         for word in product((0, 1), repeat=d)})


def exact_terminal(target, competitor, strength):
    """Sum every reveal-order path. None selects the limiting chain, with all maximizing ties."""
    unconditional = mixture(target, competitor, F(1, 2))
    d = len(next(iter(target)))
    alphabet = sorted({b for x in unconditional for b in x})
    root = (None,) * d

    def cylinder(weights, state):
        return sum((p for x, p in weights.items()
                    if all(a is None or a == b for a, b in zip(state, x))), F(0))

    @cache
    def exits(state):
        parent_target = cylinder(target, state)
        parent_total = cylinder(unconditional, state)
        rates, score_ratios = {}, {}
        for j, visible in enumerate(state):
            if visible is not None:
                continue
            for b in alphabet:
                child = state[:j] + (b,) + state[j + 1:]
                conditioned = cylinder(target, child) / parent_target
                if conditioned:
                    unconditioned = cylinder(unconditional, child) / parent_total
                    rates[child] = conditioned
                    score_ratios[child] = conditioned / unconditioned
        if strength is None:
            maximum = max(score_ratios.values())
            weights = {child: rate for child, rate in rates.items() if score_ratios[child] == maximum}
        else:
            weights = {child: rate * score_ratios[child] ** strength for child, rate in rates.items()}
        total = sum(weights.values())
        return {child: weight / total for child, weight in weights.items()}

    endpoint = {}
    for x in target:
        mass = F(0)
        for order in permutations(range(d)):
            state, path_mass = root, F(1)
            for j in order:
                child = state[:j] + (x[j],) + state[j + 1:]
                path_mass *= exits(state).get(child, 0)
                if not path_mass:
                    break
                state = child
            mass += path_mass
        endpoint[x] = mass
    assert sum(endpoint.values()) == 1
    return endpoint


def square_formula(target, competitor, x, w):
    """Independent evaluation of Eq. (15) via normalized tilted rows and columns."""
    full = mixture(target, competitor, F(1, 2))
    tilted = {y: p * (p / full[y]) ** w for y, p in target.items()}
    numerator, denominator = F(0), F(0)
    for j in range(2):
        for b in {y[j] for y in target}:
            fiber = [y for y in target if y[j] == b]
            p = sum(target[y] for y in fiber)
            m = sum(v for y, v in full.items() if y[j] == b)
            first_weight = p * (p / m) ** w
            denominator += first_weight
            if x[j] == b:
                numerator += first_weight * tilted[x] / sum(tilted[y] for y in fiber)
    return numerator / denominator


def diagonal_tests():
    for d, value, odds_ratio in [(2, F(63, 80), F(21, 17)), (3, F(171, 208), F(57, 37))]:
        zero, one = (0,) * d, (1,) * d
        target = distribution({zero: F(1, 4), one: F(3, 4)})
        competitor = uniform(x for x in product((0, 1), repeat=d) if x != zero)
        for w in [0, 1, 2, 8]:
            result = exact_terminal(target, competitor, w)
            odds = 3 * odds_ratio ** w
            assert result[one] == odds / (1 + odds)
            if d == 2:
                assert result[one] == square_formula(target, competitor, one, w)
            if w == 1:
                assert result[one] == value
        assert exact_terminal(target, competitor, None)[one] == 1
        print(f"binary diagonal D={d}: ordinary 3/4, w=1 {value}, strong limit 1")


def product_tests():
    s, w = F(1, 100), 50
    for d, alphabet in [(3, (0, 1)), (2, (0, 1, 2))]:
        zero = (0,) * d
        typical = [(0, 1, 0), (0, 0, 1)] if d == 3 else [(0, 2), (2, 0)]
        target = independent(d, s)
        competitor = mixture(uniform(typical), uniform(x for x in product(alphabet, repeat=d)
                                                       if x != zero), 1 - s / 4)
        def overlap(law):
            return sum(p for x, p in law.items() if x in competitor)
        baseline = overlap(target)
        assert baseline == 1 - (1 - s) ** d
        assert exact_terminal(target, competitor, 0) == target
        predicted = (1 / (1 + (3 - s) / s * F(4, 5) ** w) if d == 3 else
                     1 / (1 + (1 - s) / s * F(35, 46) ** w))
        observed = overlap(exact_terminal(target, competitor, w))
        assert observed >= predicted > F(99, 100)
        assert overlap(exact_terminal(target, competitor, None)) == 1
        # Integers certify this six-decimal interval, without floating point.
        floor = observed.numerator * 10**6 // observed.denominator
        print(f"product D={d}: ordinary {baseline}, w=50 lower bound {float(predicted):.9f}, "
              f"exact guided mass in [{floor}/10^6, {floor + 1}/10^6), strong limit 1")


if __name__ == "__main__":
    diagonal_tests()
    product_tests()
