"""Check a uniquely forced bad greedy history in one unweighted stream."""
from fractions import Fraction

from verify_witness import leftmost, occurrences, replace, spell


def replay(initial, rules, require_unique):
    row = initial
    gains = []
    for lengths in rules:
        present = set(zip(row, row[1:]))
        counts = {pair: len(leftmost(occurrences(row, pair))) for pair in present}
        pair = tuple(map(spell, lengths))
        chosen = leftmost(occurrences(row, pair))
        most = max(counts.values())
        winners = {p for p, n in counts.items() if n == most}
        if require_unique:
            assert winners == {pair}
        print(f"pair={lengths} saving={len(chosen)} max={most} maximizers={len(winners)}")
        gains.append(len(chosen))
        row = replace(row, chosen)
    return sum(gains)


def main():
    witness = (8, 4, 2, 1, 1, 8, 2, 2, 4, 4, 4, 8, 8, 8)
    rows = [witness] * 40 + [witness[:j] for j in range(2, 6)]
    stream = []
    for index, row in enumerate(rows):
        if index:
            stream.append(chr(0xE000 + index))
        stream.extend(map(spell, row))

    print("Uniquely forced greedy")
    greedy = replay(tuple(stream), ((8, 4), (12, 2), (14, 1), (15, 1)), True)
    print("Full comparator")
    better = replay(tuple(stream), ((1, 1), (2, 2), (4, 4), (8, 8)), False)
    assert (greedy, better) == (170, 404)
    ratio = Fraction(greedy, better)
    assert ratio <= Fraction(17, 40) < Fraction(15, 32)
    print(f"upper bound on greedy/OPT = {ratio} <= 17/40 < 15/32")


if __name__ == "__main__":
    main()
