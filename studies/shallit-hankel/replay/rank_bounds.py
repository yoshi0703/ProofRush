"""Finite arithmetic for the all-shift 43*rank > 13*order theorem."""

from itertools import permutations

MORPHISM = dict(zip("1234", ("12", "23", "14", "32")))
PAIRS = tuple("12 14 21 22 23 31 32 41 42".split())
LENGTHS = {
    21: 129, 22: 129, 23: 129, 24: 129, 25: 129,
    26: 137, 27: 137, 28: 137, 29: 137, 30: 139,
    31: 145, 32: 145, 33: 166, 34: 167, 35: 168,
    36: 169, 37: 177, 38: 177, 39: 177, 40: 257,
}
PRIME = (1 << 61) - 1


def expand(word: str, steps: int) -> str:
    for _ in range(steps):
        word = "".join(MORPHISM[c] for c in word)
    return word


def adjacent(word: str) -> set[str]:
    return {word[i:i + 2] for i in range(len(word) - 1)}


def pair_cover(length: int):
    level = (length - 1).bit_length()
    width = 1 << level
    for pair in PAIRS:
        yield expand(pair, level), width


def check_substitution() -> None:
    allowable = set(PAIRS)
    assert set(MORPHISM.values()) <= allowable
    assert set().union(*(adjacent(expand(pair, 1)) for pair in PAIRS)) <= allowable
    assert adjacent(expand("1", 5)) == allowable
    assert max(len({w[i:i + 8] for i in range(width)})
               for w, width in pair_cover(8)) <= 49
    for length, count in [(1, 4), (2, 9), (3, 15), (4, 22),
                          (5, 28), (6, 35), (7, 42), (8, 49)]:
        words = {w[i:i + length] for w, width in pair_cover(length)
                 for i in range(width)}
        assert len(words) == count
    code = [tuple(map(int, expand(c, 2))) for c in MORPHISM]
    determinant = 0
    for perm in permutations(range(4)):
        inversions = sum(perm[i] > perm[j] for i in range(4) for j in range(i+1, 4))
        term = (-1) ** inversions
        for i, j in enumerate(perm):
            term *= code[i][j]
        determinant += term
    assert determinant == 10


def conflict(word: str, width: int) -> bool:
    before: dict[str, str] = {}
    after: dict[str, str] = {}
    for start in range(len(word) - width + 1):
        state = word[start:start + width]
        if start and before.setdefault(state, word[start - 1]) != word[start - 1]:
            return True
        stop = start + width
        if stop < len(word) and after.setdefault(state, word[stop]) != word[stop]:
            return True
    return False


def one_hot_rows(word: str, width: int) -> list[int]:
    """Return the rows of the indicator matrix packed as bits."""
    mask = (1 << (4 * width)) - 1
    row = 0
    rows = []
    for i, c in enumerate(word):
        row = ((row << 4) | (1 << (int(c) - 1))) & mask
        if i + 1 >= width:
            rows.append(row)
    return rows


def rank_exceeds(rows: list[int], bound: int) -> bool:
    pivots: dict[int, int] = {}
    for row in rows:
        while row:
            bit = row.bit_length()
            pivot = pivots.get(bit, 0)
            if pivot:
                row ^= pivot
            else:
                pivots[bit] = row
                if len(pivots) > bound:
                    return True
                break
    return False


def check_base_factors() -> None:
    for u, length in LENGTHS.items():
        assert 13 * (length + 1) <= 86 * (u - 1)
        counts = [0, 0, 0]
        for word, width in pair_cover(length):
            rows_right = one_hot_rows(word, u + 1)
            rows_both = one_hot_rows(word, u + 2)
            for start in range(width):
                stop = start + length
                if conflict(word[start:stop], u):
                    counts[0] += 1
                    continue
                if rank_exceeds(rows_right[start:stop - u], 3 * u + 1):
                    counts[1] += 1
                    continue
                if rank_exceeds(rows_both[start:stop - u - 1], 3 * u + 1):
                    counts[2] += 1
                    continue
                raise ValueError(f"missing certificate for u={u}: {word[start:stop]}")
        print(f"u={u}, K={length}, witnesses literal/right/both={counts}")


def check_small_orders() -> None:
    # Lucas--Lehmer for the exact Mersenne prime used in the field computation.
    seed = 4
    for _ in range(59):
        seed = (seed * seed - 2) % PRIME
    assert seed == 0
    done = 0
    for word, width in pair_cover(161):
        two_ago = [1] * len(word)
        previous = list(map(int, word))
        done += width
        for order in range(2, 82):
            row = []
            for i in range(len(previous) - 2):
                numerator = previous[i] * previous[i + 2] - previous[i + 1] ** 2
                denominator = two_ago[i + 2]
                row.append((numerator * pow(denominator, -1, PRIME)) % PRIME)
            assert all(row), (word, order)
            assert len(row) >= width
            done += width
            two_ago, previous = previous, row
    print(f"certified {done} pair-offset small-order checks, all shifts of orders 1..81")


if __name__ == "__main__":
    check_substitution()
    check_base_factors()
    check_small_orders()
