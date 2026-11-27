"""Exact reference-probability arithmetic for the finite testing rate."""
from collections import Counter
from fractions import Fraction as F


def two_power(exponent):
    return F(2**exponent) if exponent >= 0 else F(1, 2 ** (-exponent))


def dyadic_power(value, numerator, denominator):
    """Largest power of two <= value**(numerator/denominator), or zero."""
    if not value:
        return F(0)
    powered = value**numerator
    top = powered.numerator
    bottom = powered.denominator
    exponent = top.bit_length() - bottom.bit_length()
    if (top << max(-exponent, 0)) < (bottom << max(exponent, 0)):
        exponent -= 1
    return two_power(exponent // denominator)


def ceil_fraction(value):
    return -(-value.numerator // value.denominator)


def group_probabilities(blocks):
    groups = Counter()
    for probability, count in blocks:
        if isinstance(probability, float):
            raise ValueError("use fraction strings or integers for probability masses")
        q = F(probability)
        if not 0 <= q <= 1 or type(count) is not int or count < 1:
            raise ValueError("an atom needs a nonnegative probability and a positive integer count")
        groups[q] += count
    if sum(q * k for q, k in groups.items()) != 1:
        raise ValueError("probabilities with their multiplicities must sum to one")
    return sorted(groups.items(), reverse=True)


def split_at(groups, mass):
    head = []
    tail = []
    cumulative = F(0)
    for q, k in groups:
        kept = min(k, ceil_fraction((mass - cumulative) / q)) if cumulative < mass else 0
        if kept:
            head.append((q, kept))
            cumulative += q * kept
        if kept < k and q > 0:
            tail.append((q, k - kept))
    return head, tail, cumulative
