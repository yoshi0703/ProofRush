#!/usr/bin/env python3
"""
Exact rational verifier for the asymmetric one-sided linear kernel certificate
used in `Erdos030.sidon_sub_094295` (m = 48, L = 4, p_i = (2i + 1) / 48^2).

Achieves sqrt(a * b) = 0.94294036... < 0.94295, strictly sharper than:
  - Hou & Zhao (Sep 2026, arXiv:2607.01169): 0.94349
  - Carter, O'Bryant & Tao (Oct 2026, arXiv:2610.36207): 0.94304
and within 1.32e-4 of the exact continuous smoothing limit 2*sqrt(2)/3 = 0.94280904...
"""

from fractions import Fraction
import json
import math

M = 48
L = 4
N_BOUND = L * M  # 192
P_DEN = M * M    # 2304
W_DEN = 1_000_000

P_NUM = [2 * i + 1 for i in range(M)]

W_NUM = [
    # Block 0 (0..15)
    10521, 31801, 53521, 75701, 98341, 121471, 145081, 169201,
    193821, 218961, 244641, 270851, 297621, 324961, 352871, 381371,
    # Block 1 (16..31)
    410471, 440181, 470511, 501491, 533111, 565391, 598351, 632001,
    666361, 701431, 737231, 773791, 811101, 849211, 888101, 927821,
    # Block 2 (32..47)
    968371, 1009771, 1052041, 1095211, 1139281, 1184281, 1230241, 1277161,
    1325081, 1374021, 1423991, 1475011, 1527131, 1580341, 1634691, 1690191,
    # Block 3 (48..63)
    725871, 740711, 755401, 769941, 784321, 798521, 812531, 826321,
    839901, 853231, 866321, 879131, 891651, 903871, 915771, 927321,
    # Block 4 (64..79)
    938501, 949311, 959711, 969681, 979201, 988251, 996811, 1004841,
    1012331, 1019251, 1025561, 1031251, 1036271, 1040611, 1044231, 1047101,
    # Block 5 (80..95)
    1049191, 1050451, 1050861, 1050381, 1048981, 1046601, 1043221, 1038791,
    1033261, 1026611, 1018771, 1009701, 999351, 987681, 974631, 960151,
    # Block 6 (96..111)
    954931, 959601, 964051, 968291, 972321, 976131, 979721, 983091,
    986251, 989191, 991921, 994431, 996721, 998801, 1000681, 1002341,
    # Block 7 (112..127)
    1003811, 1005071, 1006131, 1007001, 1007691, 1008191, 1008521, 1008681,
    1008691, 1008541, 1008251, 1007821, 1007281, 1006621, 1005871, 1005031,
    # Block 8 (128..143)
    1004121, 1003161, 1002161, 1001141, 1000121, 999111, 998151, 997251,
    996431, 995721, 995161, 994751, 994551, 994571, 994851, 995431,
    # Block 9 (144..159)
    996231, 997051, 997791, 998461, 999051, 999571, 1000031, 1000421,
    1000751, 1001021, 1001241, 1001411, 1001541, 1001621, 1001661, 1001661,
    # Block 10 (160..175)
    1001631, 1001571, 1001491, 1001381, 1001251, 1001111, 1000961, 1000801,
    1000631, 1000461, 1000301, 1000141, 999981, 999831, 999701, 999581,
    # Block 11 (176..191)
    999471, 999381, 999311, 999271, 999241, 999231, 999241, 999271,
    999331, 999391, 999481, 999571, 999681, 999781, 999891, 1005481,
]


def verify_certificate() -> dict:
    assert len(P_NUM) == M
    assert len(W_NUM) == N_BOUND
    assert sum(P_NUM) == P_DEN
    assert sum(x * x for x in P_NUM) == 147440
    assert sum(x * x for x in W_NUM) == 176012388616832

    p = [Fraction(x, P_DEN) for x in P_NUM]
    w = [Fraction(x, W_DEN) for x in W_NUM]

    min_slack = None
    for q in range(N_BOUND + 1):
        val = sum(p[i] * (w[q + i] if q + i < N_BOUND else Fraction(1)) for i in range(M))
        assert val >= 1, f"Covering inequality failed at q={q}: {val}"
        slack = val - 1
        if min_slack is None or slack < min_slack:
            min_slack = slack

    a = M * sum(x * x for x in p)
    b = 1 + (sum(x * x for x in w) / M - L)
    assert b > 0
    ab = a * b
    assert ab < Fraction(94295, 100000) ** 2

    return {
        "m": M,
        "L": L,
        "a_exact": f"{a.numerator}/{a.denominator}",
        "b_exact": f"{b.numerator}/{b.denominator}",
        "a_float": float(a),
        "b_float": float(b),
        "ab_float": float(ab),
        "sqrt_ab": math.sqrt(float(ab)),
        "continuous_limit_2sqrt2_over_3": 2 * math.sqrt(2) / 3,
        "gap_to_limit": math.sqrt(float(ab)) - 2 * math.sqrt(2) / 3,
        "min_covering_slack": float(min_slack),
        "strictly_below_094295": ab < Fraction(94295, 100000) ** 2,
    }


if __name__ == "__main__":
    print(json.dumps(verify_certificate(), indent=2))
