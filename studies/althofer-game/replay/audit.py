"""Independently check the explicit finite strategy witnesses using exact integers."""

from functools import lru_cache


def odd_part(value):
    return value // (value & -value)


def valuation(value):
    return (value & -value).bit_length() - 1


def children(n):
    return odd_part(3 * n - 1), odd_part(3 * n + 1)


@lru_cache(maxsize=100_000)
def wins(n, depth):
    return n > 1 and depth > 0 and any(
        child == 1 or loses(child, depth - 1) for child in children(n)
    )


@lru_cache(maxsize=100_000)
def loses(n, depth):
    return n > 1 and depth > 0 and all(
        child > 1 and wins(child, depth - 1) for child in children(n)
    )


def two_ply_formula(n):
    for offset, first_exponent in ((-1, 6), (1, 9), (-5, 11), (5, 8)):
        power = 9 * n - offset
        if power > 0 and power & (power - 1) == 0:
            exponent = power.bit_length() - 1
            if exponent >= first_exponent and (exponent - first_exponent) % 6 == 0:
                return True
    return False


def check_two_and_four():
    for n in range(3, 1_000_000, 2):
        literal = all(child > 1 and 1 in children(child) for child in children(n))
        assert literal == two_ply_formula(n)
    print('Two-ply check on all 499,999 nonterminal odd starts below one million.')

    for sign in (-1, 1):
        count = 0
        for exponent in range(12, 280):
            if (pow(2, exponent, 81) - 4 * sign) % 81:
                continue
            z = ((1 << exponent) - 4 * sign) // 324
            n = sign + 16 * z
            assert z > 0 and z % 2 and valuation(n - sign) == 4
            assert loses(n, 4) and not loses(n, 2) and not wins(n, 5)
            count += 1
        print(f'Four-ply witnesses at anchor {sign}: {count}.')


def check_lift(sign, order, modulus, residue):
    base_order = 2 + (order - 2) % 3
    lifts = (order - base_order) // 3
    offset, divisor = {2: (5 * sign, 9), 3: (sign, 9), 4: (65 * sign, 81)}[base_order]
    modulus_for_power = divisor * modulus * 9**lifts
    inverse_eight = pow(8**lifts, -1, modulus)
    seed_class = sign + 9**lifts * (residue - sign) * inverse_eight
    target = (divisor * seed_class - offset) % modulus_for_power
    # Two is a primitive root of every positive power of three.
    exponent = 12
    while pow(2, exponent, modulus_for_power) != target:
        exponent += 1
    seed, remainder = divmod((1 << exponent) + offset, divisor)
    assert remainder == 0
    difference, remainder = divmod(seed - sign, 9**lifts)
    assert remainder == 0
    n = sign + 8**lifts * difference
    assert n > 1 and n % 2 and valuation(n - sign) == order and n % modulus == residue
    assert loses(n, 4 + 2 * lifts)


def check_descent():
    for horizon in range(1, 5):
        for modulus in range(1, 21):
            start = 1 + odd_part(modulus) * 2 ** (valuation(modulus) + 4 * horizon + 3)
            frontier = {start}
            for _ in range(horizon):
                following = set()
                for n in frontier:
                    for child in children(n):
                        reply = max(children(child))
                        assert reply > n and (reply - 1) % modulus == 0
                        following.add(reply)
                frontier = following
    print('Both adversarial choices checked for horizons 1–4 and moduli 1–20.')


if __name__ == '__main__':
    check_two_and_four()
    for sign in (-1, 1):
        for order in range(2, 10):
            for modulus in (1, 3, 9, 27):
                for residue in range(modulus):
                    check_lift(sign, order, modulus, residue)
    print('Both anchors, valuations 2–9 and all residues modulo 1, 3, 9 and 27 checked.')
    check_descent()
