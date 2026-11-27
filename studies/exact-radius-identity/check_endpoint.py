#!/usr/bin/env python3
"""Exact small-example replay of the endpoint argument, using the standard library.

The checks compare finite probability and combinatorial identities against direct
enumeration. They do not test unspecified absolute constants or asymptotic rates.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product
from math import ceil, comb, factorial, isqrt, lcm, prod


def compositions(total, size):
    """Yield integer weight vectors summing to total, including zero entries."""
    if size == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in compositions(total - first, size - 1):
            yield (first, *rest)


def subsets(labels):
    for size in range(len(labels) + 1):
        yield from combinations(labels, size)


def minimum_cover_costs(weights, counts, limit):
    """Minimum reference cost for covering at least j positions, for every j."""
    unreachable = sum(weights) + 1
    costs = [0] + [unreachable] * limit
    for weight, count in zip(weights, counts):
        if count:
            costs = [
                min(costs[j], weight + costs[max(0, j - count)])
                for j in range(limit + 1)
            ]
    return costs


def check_cover_dp():
    checks = 0
    for size in range(2, 5):
        for weights in compositions(6, size):
            for n in range(7):
                for observations in combinations_with_replacement(range(size), n):
                    counts = tuple(observations.count(i) for i in range(size))
                    observed = tuple(set(observations))
                    choices = [
                        (sum(counts[i] for i in labels), sum(weights[i] for i in labels))
                        for labels in subsets(observed)
                    ]
                    expected = [
                        min(cost for covered, cost in choices if covered >= b)
                        for b in range(n + 1)
                    ]
                    costs = minimum_cover_costs(weights, counts, n)
                    assert costs == expected, (weights, observations, costs, expected)
                    for b in {0, (n + 1) // 2, n}:
                        reachable_cost = min(
                            sum(weights[i] for i in {observations[j] for j in positions})
                            for positions in combinations(range(n), b)
                        )
                        assert costs[b] == reachable_cost, (weights, observations, b)
                    checks += len(costs)
    return checks


def repeat_count(observations):
    return len(observations) - len(set(observations))


def repeat_distribution(weights, n):
    """Numerators for probabilities of repeat counts under iid integer weights."""
    result = [0] * (n + 1)
    for observations in product(range(len(weights)), repeat=n):
        numerator = prod(weights[i] for i in observations)
        result[repeat_count(observations)] += numerator
    assert sum(result) == sum(weights) ** n
    return result


def binomial_tail(n, p, minimum):
    return sum(comb(n, j) * p**j * (1 - p) ** (n - j) for j in range(minimum, n + 1))


def check_split_null():
    checks = 0
    for size in range(2, 5):
        for weights in compositions(4, size):
            groups = tuple(max(1, ceil(Fraction(size * w, 4))) for w in weights)
            common = lcm(*groups)
            split = tuple(
                common * w // group for w, group in zip(weights, groups)
                for _ in range(group)
            )
            total = 4 * common
            assert sum(split) == total and len(split) <= 2 * size
            assert max(split) * size <= total
            assert sum(w for w in split if 8 * size * w >= total) * 4 >= 3 * total
            for alt in compositions(4, size):
                split_alt = tuple(
                    common * w // group for w, group in zip(alt, groups)
                    for _ in range(group)
                )
                assert len(split_alt) == len(split) and sum(split_alt) == total
                assert sum(abs(p - q) for p, q in zip(split_alt, split)) == (
                    common * sum(abs(p - q) for p, q in zip(alt, weights))
                )
            for n in range(6):
                repeats = repeat_distribution(split, n)
                bound_p = min(Fraction(1), Fraction(n, size))
                for minimum in range(n + 1):
                    exact = Fraction(sum(repeats[minimum:]), total**n)
                    assert exact <= binomial_tail(n, bound_p, minimum), (weights, n, minimum)
                    checks += 1
    return checks


def check_uniform_occupancy():
    """Uniform on K labels maximizes distinct-count tails, with zeros allowed."""
    checks = 0
    for size in range(2, 5):
        for n in range(6):
            uniform = repeat_distribution((1,) * size, n)
            for weights in compositions(6, size):
                other = repeat_distribution(weights, n)
                for minimum in range(n + 1):
                    assert sum(other[minimum:]) * size**n >= sum(uniform[minimum:]) * 6**n, (
                        weights, n, minimum
                    )
                    checks += 1
    return checks


def falling(size, n):
    return factorial(size) // factorial(size - n) if n <= size else 0


def check_hidden_law(q, tail, support_size, n):
    supports = tuple(combinations(tail, support_size))
    mixture_counts = Counter()
    for support in supports:
        mixture_counts.update(product(support, repeat=n))
    mixture_denom = len(supports) * support_size**n
    assert sum(mixture_counts.values()) == mixture_denom
    q_tail = sum((q[i] for i in tail), Fraction())
    assert all(q[i] == q_tail / len(tail) for i in tail)
    null_survival = Fraction()
    hidden_survival = Fraction()
    overlap = Fraction()
    half_l1 = Fraction()
    distinct = []
    for observations in product(range(len(q)), repeat=n):
        seen = set(observations)
        hidden = Fraction(mixture_counts[observations], mixture_denom)
        null = prod((q[i] for i in observations), start=Fraction(1))
        # A support must contain precisely these s required distinct labels.
        s = len(seen)
        support_count = (
            comb(len(tail) - s, support_size - s)
            if seen.issubset(tail) and s <= support_size else 0
        )
        assert mixture_counts[observations] == support_count, (q, observations, support_size)
        overlap += min(hidden, null)
        half_l1 += abs(hidden - null) / 2
        if s == n and seen.issubset(tail):
            null_survival += null
            hidden_survival += hidden
            distinct.append((null, hidden))
    assert overlap == 1 - half_l1
    assert null_survival == (q_tail / len(tail))**n * falling(len(tail), n)
    assert hidden_survival == Fraction(falling(support_size, n), support_size**n)
    assert overlap >= min(null_survival, hidden_survival)
    if null_survival and hidden_survival:
        assert all(null / null_survival == hidden / hidden_survival for null, hidden in distinct)
    return overlap, null_survival, hidden_survival


def check_hidden_alternatives():
    checks = 0
    for size in range(2, 8):
        tail = tuple(range(size))
        uniform = (Fraction(1, size),) * size
        for support_size in range(1, size + 1):
            for n in range(5):
                _, null, hidden = check_hidden_law(uniform, tail, support_size, n)
                assert null >= hidden
                if n <= support_size // 2:
                    assert hidden >= Fraction(1, 2)**n
                checks += 1
    for size in range(3, 8):
        tail = tuple(range(1, size))
        for n in range(1, len(tail) // 2 + 1):
            for d in map(Fraction, ("1/100", "1/7", "1/2", "9/10")):
                t = min(Fraction(1, 2), len(tail) * d / (4 * n))
                q = (1 - t,) + (t / len(tail),) * len(tail)
                for support in combinations(tail, 2 * n):
                    alt = tuple(Fraction(1, 2 * n) if i in support else Fraction()
                                for i in range(size))
                    half_l1 = sum(abs(p - q_i) for p, q_i in zip(alt, q)) / 2
                    overlap = sum(min(p, q_i) for p, q_i in zip(alt, q))
                    assert half_l1 == 1 - overlap and overlap == 2 * n * t / len(tail)
                    assert overlap <= d / 2 < d and half_l1 > 1 - d
                _, null, hidden = check_hidden_law(q, tail, 2 * n, n)
                assert null >= (t / 2)**n and hidden >= Fraction(1, 2)**n
                checks += 1
    for size in range(4, 8):
        for k in (Fraction(4), Fraction(9, 2), Fraction(size) - Fraction(1, 10)):
            if not 4 <= k < size:
                continue
            d = k / size
            support_size = k // 2
            null = (Fraction(1, size),) * size
            for support in combinations(range(size), support_size):
                alt = tuple(Fraction(1, support_size) if i in support else Fraction()
                            for i in range(size))
                overlap = sum(min(p, q) for p, q in zip(alt, null))
                assert overlap == Fraction(support_size, size) < d
                assert sum(abs(p - q) for p, q in zip(alt, null)) / 2 > 1 - d
                checks += 1
    for n in range(4):
        overlap, null, hidden = check_hidden_law(
            (Fraction(1), Fraction(), Fraction()), (1, 2), 2, n
        )
        assert overlap == null == int(n == 0)
        assert hidden == Fraction(falling(2, n), 2**n)
        checks += 1
    for size in range(2, 8):
        for d in map(Fraction, ("1/100", "1/3")):
            q = (d / 2,) + ((1 - d / 2) / (size - 1),) * (size - 1)
            assert sum(q) == 1 and all(q_i > 0 for q_i in q)
            for n in range(1, 5):
                # A point alternative has exactly one ordered record, even if n > 1.
                assert 1 - sum(abs(Fraction(i == 0) - q_i) for i, q_i in enumerate(q)) / 2 < d
                sample_overlap = sum(
                    min(prod(q[i] for i in observations), int(set(observations) == {0}))
                    for observations in product(range(size), repeat=n)
                )
                assert sample_overlap == (d / 2)**n
                checks += 1
    return checks


def check_fixed_position_witness(weights, d, b):
    """Check the heavy/light versus repeated-label certificate, with integer cutoffs."""
    total = sum(weights)
    m = len(weights)
    light = {i for i, weight in enumerate(weights) if b * weight <= 4 * d * total}
    assert Fraction(sum(weights[i] for i in light), total) <= 4 * m * d / b
    repeat_cutoff = ceil(Fraction(b, 4))
    light_cutoff = ceil(Fraction(b, 2))
    certificates = dict.fromkeys(combinations(range(b), repeat_cutoff), 0)
    event_count = 0
    for observations in product(range(m), repeat=b):
        numerator = prod(weights[i] for i in observations)
        seen = set()
        prefix_cost = 0
        repeats_with_low_prefix_cost = []
        for j, label in enumerate(observations):
            if label in seen:
                if prefix_cost <= d * total:
                    repeats_with_low_prefix_cost.append(j)
            else:
                seen.add(label)
                prefix_cost += weights[label]
        for selected in combinations(repeats_with_low_prefix_cost, repeat_cutoff):
            certificates[selected] += numerator
        if prefix_cost <= d * total:
            event_count += numerator
            assert (
                len(repeats_with_low_prefix_cost) >= repeat_cutoff
                or sum(label in light for label in observations) >= light_cutoff
            ), (weights, d, observations)
    for selected, numerator in certificates.items():
        assert Fraction(numerator, total**b) <= d**repeat_cutoff, (weights, d, selected)
    light_mass = Fraction(sum(weights[i] for i in light), total)
    bound = binomial_tail(b, light_mass, light_cutoff) + sum(
        Fraction(numerator, total**b) for numerator in certificates.values()
    )
    assert Fraction(event_count, total**b) <= bound
    return Fraction(event_count, total**b)


def check_high_confidence_null():
    checks = 0
    profiles = tuple(compositions(4, 3)) + ((0, 1), (1, 1), (10, 1, 1, 1), (97, 2, 1, 0))
    for weights in profiles:
        m, total = len(weights), sum(weights)
        for d in map(Fraction, ("0", "1/100", "1/13", "1/4", "1/2", "3/4")):
            for n in range(1, 6):
                b = (n + 1) // 2
                fixed = check_fixed_position_witness(weights, d, b)
                rejection = 0
                for observations in product(range(m), repeat=n):
                    counts = tuple(observations.count(i) for i in range(m))
                    costs = minimum_cover_costs(weights, counts, b)
                    if costs[b] <= d * total:
                        rejection += prod(weights[i] for i in observations)
                assert Fraction(rejection, total**n) <= comb(n, b) * fixed
                checks += 1
    return checks


def check_high_confidence_alternative():
    checks = 0
    for weights in compositions(4, 3):
        for alternative in compositions(4, 3):
            overlap = Fraction(sum(min(q, p) for q, p in zip(weights, alternative)), 4)
            if overlap == 1:
                continue
            richer = [i for i, (q, p) in enumerate(zip(weights, alternative)) if q < p]
            assert Fraction(sum(weights[i] for i in richer), 4) <= overlap
            assert Fraction(sum(alternative[i] for i in richer), 4) >= 1 - overlap
            for n in range(1, 6):
                b = (n + 1) // 2
                samples = []
                for observations in product(range(3), repeat=n):
                    counts = tuple(observations.count(i) for i in range(3))
                    minimum_cost = minimum_cover_costs(weights, counts, b)[b]
                    samples.append((minimum_cost, prod(alternative[i] for i in observations)))
                for d in (overlap, (1 + overlap) / 2):
                    miss = Fraction(sum(p for cost, p in samples if cost > 4 * d), 4**n)
                    assert miss <= 2**n * d**(n // 2), (weights, alternative, n, d)
                    checks += 1
    return checks


def check_rounding():
    checks = 0
    for k in (Fraction(numerator, 4) for numerator in range(4, 257)):
        for confidence in (Fraction(1), min(k, Fraction(11, 10)), k):
            # Exact ceil(sqrt(k*confidence)) for a rational confidence exponent.
            square = k * confidence
            b = isqrt(square.numerator // square.denominator)
            if b * b < square:
                b += 1
            assert (b - 1)**2 < square <= b**2 and b <= 2 * k
            k_uniform = ceil(8 * k)
            h = b // 4
            assert h <= k_uniform <= 9 * k
            if b >= 8:
                assert Fraction(h**2, k_uniform) >= b**2 / (576 * k)
            if k >= 4:
                assert k / 4 <= k // 2 < k
            checks += 1
    for m in range(2, 21):
        for n in range(1, m + 2):
            if n <= (m - 1) // 2:
                assert 2 * n <= m - 1
                assert all(1 - Fraction(j, m - 1) >= Fraction(1, 2) for j in range(n))
            else:
                assert Fraction(n, m) >= Fraction(1, 4)
            b = (n + 1) // 2
            assert n - b == n // 2
            assert n - b + 1 > n // 2  # Fewest failures on an alternative miss.
            checks += 1
    return checks


def main():
    print("Exact endpoint replay (no simulation)")
    for label, check in (
        ("DP thresholds vs label subsets and position subsets", check_cover_dp),
        ("Split null, half-L1 preservation, and repeat-tail dominance", check_split_null),
        ("Uniform occupancy stochastic dominance", check_uniform_occupancy),
        ("Hidden-uniform ordered laws, survival, and strict alternatives", check_hidden_alternatives),
        ("Rounded null witnesses and the rejection union bound", check_high_confidence_null),
        ("Inclusive and strict alternative miss bounds", check_high_confidence_alternative),
        ("Batch and support integer cutoffs", check_rounding),
    ):
        print(f"{label}: {check():,} exact cases passed")


if __name__ == "__main__":
    main()
