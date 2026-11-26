"""Replay both histories against the SHA-256-pinned Baliga–Xie–Byju v3 supplement."""
import argparse
from hashlib import sha256
from pathlib import Path
import sys
from types import ModuleType
from zipfile import ZipFile

from verify_witness import spell


SUPPLEMENT_SHA256 = "2bc232a3bab2b04035eec9be4bc4d788ea7d62d2b1d2d1ed3e90d97790680cdf"


def load_module(archive, module_name):
    path = f"supplement/check/stringid/{module_name}.py"
    module = ModuleType(module_name)
    sys.modules[module_name] = module
    exec(compile(archive.read(path), path, "exec"), vars(module))
    return module


def trace(models, initial, rules, expected_gains, greedy):
    row = initial
    gains = []
    for a, b in rules:
        operands = spell(a), spell(b)
        present = models.pairs_present((row,))
        scores = {pair: models.rep_count((row,), *pair, (1,)) for pair in present}
        gain = scores[operands]
        if greedy:
            assert gain == max(scores.values())
        row, observed = models.full_scan_row(row, *operands, "".join(operands))
        assert observed == gain
        gains.append(gain)
        print(f"pair={(a, b)} gain={gain} max={max(scores.values())} after={tuple(map(len, row))}")
    assert gains == expected_gains
    return sum(gains)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("supplement", type=Path, help="Original Zenodo ZIP, still compressed")
    args = parser.parse_args()
    digest = sha256(args.supplement.read_bytes()).hexdigest()
    if digest != SUPPLEMENT_SHA256:
        parser.error(f"Unexpected SHA-256 {digest}")
    with ZipFile(args.supplement) as archive:
        models = load_module(archive, "models")
        author = load_module(archive, "check_nonfree")

    row = tuple(map(spell, (8, 4, 2, 1, 1, 8, 2, 2, 4, 4, 4, 8, 8, 8)))
    print("Greedy")
    greedy = trace(models, row, [(8, 4), (12, 2), (14, 1), (15, 1)], [1, 1, 1, 1], True)
    print("Comparator (also a greedy history)")
    better = trace(models, row, [(1, 1), (2, 2), (4, 4), (8, 8)], [1, 2, 3, 4], True)
    partial_optima = author.opt_table((row,), (1,), 4)
    assert partial_optima == [0, 1, 3, 6, 10]
    assert better == partial_optima[4]
    assert not author.c_ok(4, greedy, better)
    print(f"Author partial optima, budgets 0–4: {partial_optima}")
    print(f"Author c_4 comparison: {greedy}/{better} < 15/32")


if __name__ == "__main__":
    main()
