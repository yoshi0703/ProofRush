"""Independently check the initial modular sum and sample exact minors."""
from argparse import ArgumentParser
from random import Random
from subprocess import check_output
from pathlib import Path
from overlap import expand, pair_representatives

MODULUS = (1 << 61) - 1


def bareiss(matrix):
    sign = 1
    previous = 1
    for column in range(len(matrix) - 1):
        row = next(
            (i for i in range(column, len(matrix)) if matrix[i][column]), None
        )
        if row is None:
            return 0
        if row != column:
            matrix[row], matrix[column] = matrix[column], matrix[row]
            sign = -sign
        pivot = matrix[column][column]
        for i in range(column + 1, len(matrix)):
            for j in range(column + 1, len(matrix)):
                value = pivot * matrix[i][j] - matrix[i][column] * matrix[column][j]
                matrix[i][j], remainder = divmod(value, previous)
                assert remainder == 0
            matrix[i][column] = 0
        previous = pivot
    return sign * matrix[-1][-1]


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--hankel", type=Path, default=Path(__file__).with_name("hankel"))
    binary = parser.parse_args().hankel.resolve()
    certify_prime = 4
    for _ in range(59):
        certify_prime = (certify_prime**2 - 2) % MODULUS
    assert certify_prime == 0  # Lucas–Lehmer, exponent 61 is prime.

    word = "1"
    while len(word) < 204800:
        word = expand(word)
    entries = list(map(int, word))

    def determinant(offset, order):
        matrix = [entries[offset + r:offset + r + order] for r in range(order)]
        return bareiss(matrix)

    length = 40
    all_small = [
        determinant(offset, order)
        for order in range(1, (length + 1) // 2 + 1)
        for offset in range(length - 2 * order + 2)
    ]
    assert all(all_small)
    command = [binary, str(length)]
    observed = check_output(command, text=True).strip()
    expected = (
        f"length={length} count={len(all_small)} "
        f"checksum={sum(all_small) % MODULUS} modulus={MODULUS}"
    )
    assert observed == expected, (observed, expected)

    rng = Random(911)
    for _ in range(128):
        order = rng.randint(1, 40)
        offset = rng.randrange(204800 - 2 * order + 2)
        assert determinant(offset, order) % MODULUS != 0, (offset, order)
    assert max(pair_representatives().values()) + 2 == 25
    print(f"exact prefix determinants={len(all_small)}, exact samples=128, prime={MODULUS}")


if __name__ == "__main__":
    main()
