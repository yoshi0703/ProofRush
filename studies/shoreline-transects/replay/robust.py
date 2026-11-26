#!/usr/bin/env python3
"""Replay the sampling laws and the bias/variance certificates exactly."""

import argparse
from fractions import Fraction as F
from itertools import combinations, product
from math import comb


def designs():
    def product_weights(edge, interior):
        scores = [
            comb(2, e) * comb(18, 4 - e) * edge**e * interior**(4 - e)
            for e in range(3)
        ]
        return tuple(F(z, sum(scores)) for z in scores)

    successive = [F(0)] * 3
    for path in product((0, 1), repeat=4):
        e = sum(path)
        if e > 2:
            continue
        weighted_left = [90, 6]
        likelihood = F(1)
        for kind in path:
            likelihood *= F(weighted_left[kind], sum(weighted_left))
            weighted_left[kind] -= (5, 3)[kind]
        successive[e] += likelihood
    return {
        "U": product_weights(1, 1),
        "W": product_weights(3, 5),
        "S": tuple(successive),
    }


def matrix(design):
    p, q = design[1:]
    return 2 * p - p**2, q - q**2, -p * q


def parameters(laws, ratio):
    u, v = laws["U"][1:]
    p, q = laws["S"][1:]
    x = 2 / (u + p + ratio * (v + q))
    return x, ratio * x


def moments(law, weights):
    _, p, q = law
    x, y = weights
    mean_factor = p * x + q * y
    endpoint_variance = 2 * p * x**2 + q * y**2 - mean_factor**2
    interior_variance = sum(law[e] * F(14 + e, 4 - e) for e in range(3))
    return mean_factor - 1, endpoint_variance, interior_variance


def analytic_moments(law, weights, abundance):
    endpoint = abundance[:2]
    interior = abundance[2:]
    h, i = sum(endpoint), sum(interior)
    within_interior = sum((F(observation) - F(i, 18)) ** 2 for observation in interior) / 18
    x, y = weights
    _, p, q = law
    mean_factor = p * x + q * y
    mean = i + mean_factor * h
    variance = (
        F(18**2, 17) * within_interior * moments(law, weights)[2]
        + p * x**2 * (endpoint[0] - endpoint[1]) ** 2
        + h**2 * (p * x**2 + q * y**2 - mean_factor**2)
    )
    return mean, variance


def enumerate_moments(law, weights, abundance):
    first = second = F(0)
    for sample in combinations(range(20), 4):
        e = sum(index < 2 for index in sample)
        likelihood = law[e] / (comb(2, e) * comb(18, 4 - e))
        total = F(18, 4 - e) * sum(abundance[index] for index in sample if index >= 2)
        if e:
            total += F(2, e) * weights[e - 1] * sum(
                abundance[index] for index in sample if index < 2
            )
        first += likelihood * total
        second += likelihood * total**2
    return first, second - first**2


def check(exact):
    laws = designs()
    u, w, s = [laws[name] for name in ("U", "W", "S")]
    assert u == (F(12, 19), F(32, 95), F(3, 95))
    assert w == (F(500, 669), F(160, 669), F(3, 223))
    assert s == (F(53125, 70434), F(17871250, 76672827), F(2804903, 221499278))
    assert all(sum(law) == 1 and all(x > 0 for x in law) for law in laws.values())
    assert all(u[e] > w[e] > s[e] for e in (1, 2))
    assert s[1] / u[1] > s[2] / u[2]
    for low in (w, s):
        a, b, c = (upper - lower for upper, lower in zip(matrix(u), matrix(low)))
        assert a > 0 and b > 0 and a * b > c**2
    assert moments(u, (0, 0))[2] == F(394, 95)
    assert all(moments(u, (0, 0))[2] > moments(low, (0, 0))[2] for low in (w, s))

    a, b, c = matrix(u)
    p, q = s[1:]
    variance_ratio = (a * q - c * p) / (b * p - c * q)
    assert variance_ratio == F(3588353044, 2722240129)
    for label, ratio, bound in [
        ("minimum bias", F(0), F(377880857, 2075649607)),
        ("monotone minimum bias", F(1), F(164167, 821909)),
        ("variance-optimal direction", variance_ratio, F(87297371240626991, 426167501616563263)),
        ("same weight per observed endpoint", F(2), F(705641617, 3281345387)),
        ("uniform endpoint weights", None, F(705641617, 1993493502)),
    ]:
        weights = parameters(laws, ratio) if ratio is not None else (F(5, 2), F(5))
        summary = {model: moments(law, weights) for model, law in laws.items()}
        assert max(abs(values[0]) for values in summary.values()) == bound
        if ratio is not None:
            factor = (s[1] + ratio * s[2]) / (u[1] + ratio * u[2])
            assert summary["U"][0] == bound and summary["S"][0] == -bound
            assert (1 - factor) / (1 + factor) == bound
        worst = max(max(values[1:]) for values in summary.values())
        print(f"{label}: x1={weights[0]}, x2={weights[1]}, bias={bound} ({float(bound):.8f}), "
              f"variance={float(worst):.8f}")
        if exact:
            for model, values in summary.items():
                print(f"  {model}: bias {values[0]}, endpoint variance {values[1]}, "
                      f"interior variance {values[2]}")

    abundance = (17, 3) + tuple((i * i + 3 * i) % 13 for i in range(18))
    for law in laws.values():
        for ratio in (F(0), F(1), F(5, 4)):
            weights = parameters(laws, ratio)
            assert analytic_moments(law, weights, abundance) == enumerate_moments(
                law, weights, abundance
            )
    print("Enumerated all 4,845 possible samples for each of nine moment checks.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--exact", action="store_true", help="print all moment fractions")
    check(parser.parse_args().exact)
