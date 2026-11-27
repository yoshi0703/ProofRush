"""An explicit sample-rate proxy for finite identity testing at strict TV distance.

All arithmetic is exact on rational input, including comparisons involving
zero probabilities and the computation of integer base-two exponents.
"""
import argparse
import json
import sys
from fractions import Fraction as F
from pathlib import Path

from rate_arithmetic import ceil_fraction, dyadic_power, group_probabilities, split_at


def exponent_for(coefficient, budget, degree):
    """Least nonnegative k with coefficient <= budget*2**(degree*k)."""
    if coefficient <= budget:
        return 0
    if not budget or not degree:
        return None
    ratio = F(coefficient) / budget
    numerator, denominator = ratio.as_integer_ratio()
    exponent = numerator.bit_length() - denominator.bit_length()
    if numerator > denominator << exponent:
        exponent += 1
    return (exponent + degree - 1) // degree


def earlier(x, y):
    """Minimum in the nonnegative integers extended by None = infinity."""
    if x is None:
        return y
    if y is None:
        return x
    return min(x, y)


def head_terms(head, w):
    omitted = 1 - w - head[0][0]
    weight = F(0)
    sigma = dyadic_power(w * (1-w), 1, 2)
    yield (omitted, sigma, F(1))
    for index, (q, count) in enumerate(head):
        multiplicity = count - int(index == 0)
        if multiplicity:
            omitted -= multiplicity*q
            weight += multiplicity*dyadic_power(q, 2, 3)
            yield (omitted, max(sigma, dyadic_power(weight, 3, 4)), F(1))


def tail_terms(tail, delta_head):
    initial = sum(k*q*dyadic_power(q, 1, 2) for q, k in tail)
    prefix = F(0)
    moment = initial
    yield delta_head, moment**2
    for q, k in tail:
        prefix += k*q
        moment -= k*q*dyadic_power(q, 1, 2)
        yield max(delta_head, prefix), moment**2


def regular_exponent(head, tail, w, e):
    """Minimize over head cuts, maximizing over all tail cuts and three terms."""
    budgets = list(tail_terms(tail, e-w))
    optimum = None
    for coefficients in head_terms(head, w):
        worst = 0
        for baseline, growing in budgets:
            for degree, coefficient in enumerate(coefficients):
                threshold = earlier(exponent_for(coefficient, baseline, degree),
                                    exponent_for(coefficient, growing, degree+4))
                if threshold is None:
                    worst = None
                    break
                worst = max(worst, threshold)
            if worst is None:
                break
        optimum = earlier(optimum, worst)
    if optimum is None:
        raise ArithmeticError("No feasible prefix for normalized reference law")
    return optimum


def rate(blocks, epsilon):
    if isinstance(epsilon, float):
        raise ValueError("use a fraction string or integer for epsilon")
    e = F(epsilon)
    if not 0 < e <= 1:
        raise ValueError("epsilon must lie in (0,1]")
    groups = group_probabilities(blocks)
    delta = 1-e
    if delta <= groups[-1][0]:
        return {"profile": 0, "branch": "empty"}
    j = sum(k*q*min(1, dyadic_power(q/delta, 1, 2)) for q, k in groups)
    if j >= 16*delta:
        return {"profile": ceil_fraction(1/j), "branch": "small-overlap"}
    head, tail, head_mass = split_at(groups, delta)
    k = regular_exponent(head, tail, 1-head_mass, e)
    return {"profile": 4**k, "branch": "regular", "exponent": k}


if __name__ == "__main__":
    # The published input model allows arbitrary binary lengths, including the
    # decimal JSON representation of an exponentially large sample count.
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    print(json.dumps(rate(data["blocks"], data["epsilon"]), indent=2))
