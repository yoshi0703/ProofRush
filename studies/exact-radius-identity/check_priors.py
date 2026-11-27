"""Exact replay of the ordered-mixture and projection calculations."""

from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import comb, prod


def tv(p, q):
    return sum(abs(a - b) for a, b in zip(p, q)) / 2


def overlap(p, q, labels):
    return sum(min(p[i], q[i]) for i in labels)


def iid(p, xs):
    return prod(p[i] for i in xs)


def mixed_law(prior, xs):
    return sum(weight * iid(p, xs) for weight, p in prior)


def paired_prior(q, labels, z):
    sorted_labels = sorted(labels, key=lambda i: q[i], reverse=True)
    pairs = [(a, b) for a, b in zip(sorted_labels[::2], sorted_labels[1::2]) if q[b] > 0]
    amount_ratio = z / sum(q[b] for _, b in pairs)
    assert 0 <= amount_ratio <= 1
    prior = []
    for signs in product((-1, 1), repeat=len(pairs)):
        p = list(q)
        for (a, b), sign in zip(pairs, signs):
            p[a] += sign * amount_ratio * q[b]
            p[b] -= sign * amount_ratio * q[b]
        assert sum(p) == 1 and min(p) >= 0 and tv(p, q) == z
        prior.append((F(1, 2 ** len(pairs)), tuple(p)))
    return prior


def latent_prior(q, labels, k):
    w = sum(q[i] for i in labels)
    conditional = {i: q[i] / w for i in labels if q[i]}
    result = Counter()
    for latent in product(conditional, repeat=k):
        result[tuple(sorted(latent))] += prod(conditional[i] for i in latent)
    assert sum(result.values()) == 1
    mean_support_q_mass = sum(weight * sum(q[i] for i in set(latent)) for latent, weight in result.items())
    assert mean_support_q_mass <= k * sum(q[i] ** 2 for i in labels) / w
    return result


def collapse(q, perturbed, suffix, ks):
    bins = [latent_prior(q, labels, k).items() for labels, k in zip(suffix, ks)]
    prior = Counter()
    for (weight, base), latents in product(perturbed, product(*bins)):
        p = list(base)
        for labels, k, (latent, wt) in zip(suffix, ks, latents):
            weight *= wt
            s = sum(base[i] for i in labels)
            counts = Counter(latent)
            for i in labels:
                p[i] = F(counts[i], k) * s
        assert sum(p) == 1 and min(p) >= 0
        prior[tuple(p)] += weight
    assert sum(prior.values()) == 1
    return [(weight, p) for p, weight in prior.items()]


def verify_comparison(q, retained_prior, suffix, ks, e, n_values):
    collapsed = collapse(q, retained_prior, suffix, ks)
    removed = sorted(i for B in suffix for i in B)
    retained = sorted(set(range(len(q))) - set(removed))
    U = sum(q[i] for i in removed)
    for _, p in collapsed:
        A = sum(max(q[i] - p[i], 0) for i in retained)
        B = overlap(p, q, removed)
        assert tv(p, q) == U + A - B
    valid = [(wt, p) for wt, p in collapsed if tv(p, q) > e]
    valid_mass = sum(wt for wt, _ in valid)
    assert valid_mass > 0
    good = [(wt / valid_mass, p) for wt, p in valid]
    for n in n_values:
        disjoint = list(product(range(len(q)), repeat=n))
        null = [iid(q, xs) for xs in disjoint]
        retain = [mixed_law(retained_prior, xs) for xs in disjoint]
        raw = [mixed_law(collapsed, xs) for xs in disjoint]
        strict = [mixed_law(good, xs) for xs in disjoint]
        assert sum(null) == sum(retain) == sum(raw) == sum(strict) == 1
        latent_bound = comb(n, 2) * max(
            sum(sum(p[i] for i in labels) ** 2 / k for labels, k in zip(suffix, ks))
            for _, p in retained_prior
        )
        assert tv(retain, raw) <= latent_bound
        assert tv(raw, strict) <= 1 - valid_mass
        assert tv(null, strict) <= tv(null, retain) + latent_bound + 1 - valid_mass
        chisq = sum((b - a) ** 2 / a for a, b in zip(null, retain) if a)
        inner = sum(
            w1 * w2 * sum(p1[i] * p2[i] / q[i] for i in range(len(q)) if q[i]) ** n
            for (w1, p1), (w2, p2) in product(retained_prior, repeat=2)
        )
        assert 1 + chisq == inner
        assert 4 * tv(null, retain) ** 2 <= chisq
        print(f"n={n} strict-prior TV={tv(null, strict)} far prior mass={valid_mass}")


def main():
    # The first example keeps the unequal medium bin and moves mass within it.
    q = (F(5, 8), F(1, 10), F(1, 12), F(1, 15), F(0),
         F(1, 32), F(1, 40), F(1, 40), F(1, 50), F(1, 50), F(3, 800))
    assert sum(q) == 1
    medium = range(1, 5)
    diffuse = range(5, 11)
    prior = paired_prior(q, medium, F(1, 16))
    verify_comparison(q, prior, [diffuse], [2], F(1, 8), (1, 2, 3))

    # The second example changes a bin mass and collapses both suffix bins.
    q = (F(1, 2), F(1, 6), F(1, 12), F(1, 8), F(1, 10), F(1, 40))
    assert sum(q) == 1
    medium = range(1, 3)
    diffuse = range(3, 6)
    z = F(3, 10)
    p = list(q)
    p[0] -= z
    for i in medium:
        p[i] *= (F(1, 4) + z) / F(1, 4)
    assert sum(p) == 1 and tv(p, q) == z
    verify_comparison(q, [(F(1), tuple(p))], [medium, diffuse], [1, 2], F(1, 2), (1, 2, 3))


if __name__ == "__main__":
    main()
