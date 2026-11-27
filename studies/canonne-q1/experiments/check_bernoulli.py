"""Exact minimax sample counts for the one-sided Bernoulli subfamily in this check."""
from fractions import Fraction as F
from itertools import product
import json

from closed_rate import rate


def binomial_masses(n, p):
    d = p.denominator
    u = p.numerator
    v = d - u
    denom = d**n
    if not u:
        return [F(1)] + [F(0)] * n
    if not v:
        return [F(0)] * n + [F(1)]
    mass = v**n
    result = [F(mass, denom)]
    for k in range(n):
        mass = mass * u * (n - k) // (v * (k + 1))
        result.append(F(mass, denom))
    assert sum(result) == 1
    return result


def upper_tail_power(n, q, p):
    """Exact most powerful test at null type-I error 1/3."""
    null = binomial_masses(n, q)
    alt = binomial_masses(n, p)
    budget = F(1, 3)
    power = F(0)
    for a, b in zip(reversed(null), reversed(alt)):
        fraction = min(F(1), budget / a) if a else F(1)
        power += fraction * b
        budget -= fraction * a
    return power


def exact_bernoulli(q, e):
    # Strict alternative consists precisely of p>q+e.
    assert 0 <= q <= e < 1 - q
    lo, hi = 0, 1
    while upper_tail_power(hi, q, q + e) < F(2, 3):
        lo, hi = hi, 2 * hi
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if upper_tail_power(mid, q, q + e) >= F(2, 3):
            hi = mid
        else:
            lo = mid
    assert upper_tail_power(hi - 1, q, q + e) < F(2, 3) <= upper_tail_power(hi, q, q + e)
    return hi


if __name__ == "__main__":
    rows = []
    for q,e in product((F(0), F(1,64), F(1,16), F(1,8), F(1,4), F(1,3)),
                       (F(1,32), F(1,16), F(1,8), F(1,4), F(1,3), F(1,2), F(2,3), F(7,8))):
        if q <= e < 1-q:
            actual = exact_bernoulli(q,e)
            proxy = rate([(q,1),(1-q,1)],e)["profile"]
            rows.append([str(q),str(e),actual,proxy])
    ratios = [F(pred,n) for _,_,n,pred in rows]
    print(json.dumps({"columns":["q","e","least_valid_n","closed_formula"],
                      "rows":rows,"min_ratio":str(min(ratios)),"max_ratio":str(max(ratios))},
                     indent=2))
