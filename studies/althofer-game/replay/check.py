"""Check the two-ply classification and algebraic strategy families exactly."""

import argparse
from functools import lru_cache


def moves(n):
    children = []
    for x in (3 * n - 1, 3 * n + 1):
        while x % 2 == 0:
            x //= 2
        children.append(x)
    return tuple(children)


@lru_cache(maxsize=100_000)
def force(n, limit, own_turn):
    """Whether the prospective winner can force a hit in at most limit plies."""
    if n == 1:
        return not own_turn
    if limit == 0:
        return False
    possibilities = (force(x, limit - 1, not own_turn) for x in moves(n))
    return any(possibilities) if own_turn else all(possibilities)


def val2(z):
    assert z
    return (z & -z).bit_length() - 1


def rank_two_formula(limit):
    result = set()
    for start, offset in ((6, -1), (9, 1), (11, -5), (8, 5)):
        for exponent in range(start, (9 * limit + 5).bit_length() + 1, 6):
            n, rem = divmod((1 << exponent) + offset, 9)
            assert rem == 0
            if n <= limit:
                result.add(n)
    return result


def exponent_for(target, modulus):
    """Discrete log of target to base two modulo a positive power of three."""
    current, period = 3, 2
    exponent = 0 if target % 3 == 1 else 1
    assert target % 3
    while current < modulus:
        current *= 3
        exponent = next(a for a in range(exponent, exponent + 3 * period, period)
                        if pow(2, a, current) == target % current)
        period *= 3
    assert current == modulus
    return exponent + max(0, (12 - exponent + period - 1) // period) * period


def losing_seed(sign, valuation, modulus, residue):
    denominator, offset = {
        2: (9, 5 * sign),
        3: (9, sign),
        4: (81, 65 * sign),
    }[valuation]
    combined_modulus = denominator * modulus
    exponent = exponent_for(denominator * residue - offset, combined_modulus)
    n, rem = divmod((1 << exponent) + offset, denominator)
    assert rem == 0 and n > 1
    assert val2(n - sign) == valuation and n % modulus == residue % modulus
    return n


def losing_witness(sign, valuation, modulus, residue):
    lifts, remainder = divmod(valuation - 2, 3)
    base = 2 + remainder
    seed_modulus = modulus * 9**lifts
    seed_residue = sign + 9**lifts * (residue - sign) * pow(8**lifts, -1, modulus)
    n = losing_seed(sign, base, seed_modulus, seed_residue)
    assert force(n, 4 if base == 4 else 2, False)
    for _ in range(lifts):
        z, rem = divmod(n - sign, 9)
        assert rem == 0
        previous = sign + 8 * z
        assert all(n in moves(child) for child in moves(previous))
        n = previous
    assert val2(n - sign) == valuation and n % modulus == residue
    return n, (4 if base == 4 else 2) + 2 * lifts


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=5_000_000)
    args = parser.parse_args()
    actual = set()
    for n in range(3, args.limit + 1, 2):
        children = moves(n)
        if all(child != 1 and 1 in moves(child) for child in children):
            actual.add(n)
    predicted = rank_two_formula(args.limit)
    assert actual == predicted, (actual - predicted, predicted - actual)
    print("rank-two classification:", len(actual), "through", args.limit)
    print("rank-two states:", sorted(actual))

    witnesses = 0
    for sign in (-1, 1):
        for valuation in range(2, 9):
            for modulus in (3, 9, 27):
                for residue in range(modulus):
                    n, bound = losing_witness(sign, valuation, modulus, residue)
                    assert force(n, bound, False)
                    if valuation == 4:
                        assert not force(n, 2, False)
                    if valuation == 2:
                        exponent = exponent_for(3 * residue + sign, 3 * modulus)
                        win = ((1 << exponent) - sign) // 3
                        win_bound = 1
                    else:
                        child_residue = (sign + 3 * (residue - sign) *
                                         pow(2, -1, modulus)) % (modulus * 3)
                        child, depth = losing_witness(
                            sign, valuation - 1, modulus * 3, child_residue,
                        )
                        assert (child - sign) % 3 == 0
                        win = sign + 2 * ((child - sign) // 3)
                        win_bound = depth + 1
                    assert force(win, win_bound, True)
                    assert val2(win - sign) == valuation and win % modulus == residue
                    witnesses += 1
    print("valuation/residue cells with separate W and L certificates:", witnesses)


if __name__ == "__main__":
    main()
