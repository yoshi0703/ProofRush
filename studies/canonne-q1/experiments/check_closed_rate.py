"""Independent exact comparison of the closed exponent with direct dyadic crossings."""
import sys
import json
import subprocess
import tempfile
from decimal import Decimal
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from random import Random

sys.dont_write_bytecode = True
from closed_rate import exponent_for, rate


def down_power(q, numerator, denominator):
    if not q:
        return F(0)
    target = q**numerator
    chosen = F(1)
    while chosen**denominator > target:
        chosen /= 2
    while (2*chosen)**denominator <= target:
        chosen *= 2
    return chosen


def retained_counts(values, endpoints):
    for kept in range(len(values)+1):
        if not endpoints or not kept or kept == len(values) or values[kept-1] != values[kept]:
            yield kept


def direct(values, e, endpoints):
    q = sorted(values, reverse=True)
    delta = 1-e
    if delta <= q[-1]:
        return 0
    j = sum(v*min(1, down_power(v/delta, 1, 2)) for v in q)
    if j >= 16*delta:
        return (j.numerator+j.denominator-1)//j.numerator
    total = F(0)
    head_length = 0
    while total < delta:
        total += q[head_length]
        head_length += 1
    off_head, tail = q[1:head_length], q[head_length:]
    w = 1-total
    gap = e-w
    head_costs = []
    for k in retained_counts(off_head, endpoints):
        head_costs.append((sum(off_head[k:]), max(
            down_power(w*(1-w), 1, 2),
            down_power(sum(down_power(v, 2, 3) for v in off_head[:k]), 3, 4),
        )))
    tail_budgets = []
    for k in retained_counts(tail, endpoints):
        tail_budgets.append((max(gap, sum(tail[:k])),
                      sum(v*down_power(v, 1, 2) for v in tail[k:])**2))
    k = 0
    while True:
        t = 2**k
        left = min(max(b, c/t, F(1, t*t)) for b, c in head_costs)
        right = min(max(b, h*t**4) for b, h in tail_budgets)
        if left <= right:
            return t*t
        k += 1
        assert k < 300


def main():
    cases = 0
    for c, b, a in product([F(0), F(1, 7), F(1), F(43), F(2**50, 3)], repeat=3):
        if a.denominator != 1 or a > 100:
            continue
        a = int(a)
        actual = exponent_for(c, b, a)
        if actual is None:
            assert c > b and (b == 0 or a == 0)
        else:
            assert c <= b * 2**(a*actual)
            assert actual == 0 or c > b * 2**(a*(actual-1))
        cases += 1
    rng = Random(20261127)
    difference = None
    for i in range(1500):
        weights = [rng.randrange(1, 40) if j == 0 else rng.randrange(20)
                   for j in range(rng.randrange(1, 13))]
        q = [F(x, sum(weights)) for x in weights]
        if i % 5 == 0:
            q = [F(1, len(q)) for _ in q]
        borders = [F(1, 10**40), F(1), 1-min(q), F(1)-F(1, 10**35), F(1, 2)]
        e = borders[i % len(borders)] if i % 3 == 0 else F(rng.randrange(1, 100), 100)
        if not e:
            e = F(1, 2)
        result = rate([(str(p), 1) for p in q], str(e))["profile"]
        direct_end = direct(q, e, True)
        assert result == direct_end, (q, e, result, direct_end)
        direct_all = direct(q, e, False)
        if direct_end != direct_all and difference is None:
            difference = (q, e, direct_end, direct_all)
    print(f"{cases} exponent tests and 1,500 rational crossing tests passed")
    print("First difference between endpoint-only and all-count scans:", difference)
    # Cover the standard decimal conversion limit on both input and output.
    with tempfile.TemporaryDirectory() as tmp:
        digits_input = Path(tmp) / "binary.json"
        for exponent in (8000, 16000):
            # Decimal arithmetic constructs the test input independently of CPython's int formatting.
            denominator = format(Decimal(1 << exponent), "f")
            digits_input.write_text(json.dumps({"blocks": [["1/2", 2]], "epsilon": "1/"+denominator}))
            result = subprocess.check_output([sys.executable, "-B", str(Path(__file__).with_name("closed_rate.py")),
                                              str(digits_input)], text=True)
            observed = json.loads(result, parse_int=Decimal)
            assert observed["exponent"] == exponent-1
            assert observed["profile"] == Decimal(1 << (2*exponent-2))
    print("Two large-decimal input/output regressions passed")
    for bits in (16, 128, 1000):
        m = 2**bits
        result = rate([(str(F(1, 2)), 1), (str(F(1, 2*m)), m), ("0", 1)], "1/2")
        print(f"compressed 2^{bits} equal tail atoms: output bit size {result['profile'].bit_length()}")


if __name__ == "__main__":
    main()
