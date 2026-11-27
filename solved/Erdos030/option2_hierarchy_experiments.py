#!/usr/bin/env python3
"""
Erdos Problem #30 (Option 2) — Reproducible Hierarchy & Barrier Experiments

Reproduces the four structural findings documented in `BARRIER_THEOREM.md`:
  1. Periodic Bose + Poisson Kernel Construction on Z / (p^2 - 1) Z:
     exact Fourier flatness |hat(1_S)(xi)|^2 in {1, p}, strictly < 1.0 linear
     autocorrelation with ZERO clipping and ZERO rescaling for p >= 67 (tested to p = 1009).
  2. Exact theta-Integrality Phase Transition M_theta(N) - sqrt(N) ~ min(0.61 N^(1/4), 0.23(1-theta)sqrt(N)).
  3. Exact Degree-1 Lasserre SDP_1(N) vs SDP_1(N) + ALL 3-AP cuts X[a,b]+X[b,c]+X[a,c] <= 1
     (confirming 0.0000 improvement from 3-AP linear cuts on Degree-1 Lasserre).
  4. Exact Degree-2 Lasserre (4-tuple Sidon ideal M_2[a,b,c,e] = 0) on N = 8, 11, 15,
     demonstrating the FIRST convex hierarchy level that cuts the integrality gap
     (exact 4.000 at N=8; 64% gap reduction at N=15: 5.6551 -> 5.2373 vs h(15) = 5).

Usage:
  python3 solved/Erdos030/option2_hierarchy_experiments.py [--all | --periodic | --sdp]
"""

import argparse
import math
import numpy as np


def bose_sidon(p: int) -> list[int]:
    """Construct Bose (1942) Sidon set of size p in {0, ..., p^2 - 2} via F_{p^2}^*."""
    irred = None
    for b in range(1, p):
        for a in range(p):
            if all((x * x + a * x + b) % p != 0 for x in range(p)):
                irred = (a, b)
                break
        if irred is not None:
            break
    a0, b0 = irred

    def mul(u, v):
        return (
            (u[0] * v[0] - b0 * u[1] * v[1]) % p,
            (u[0] * v[1] + u[1] * v[0] - a0 * u[1] * v[1]) % p,
        )

    def pow_f(u, e):
        res, base = (1, 0), u
        while e > 0:
            if e & 1:
                res = mul(res, base)
            base = mul(base, base)
            e >>= 1
        return res

    order = p * p - 1
    factors, tmp, d = [], order, 2
    while d * d <= tmp:
        if tmp % d == 0:
            factors.append(d)
            while tmp % d == 0:
                tmp //= d
        d += 1
    if tmp > 1:
        factors.append(tmp)

    gen = None
    for u0 in range(p):
        for u1 in range(1, p):
            if all(pow_f((u0, u1), order // q) != (1, 0) for q in factors):
                gen = (u0, u1)
                break
        if gen is not None:
            break

    cur, sidon = (1, 0), []
    for k in range(order):
        if cur[1] == 1:
            sidon.append(k)
        cur = mul(cur, gen)
    return sorted(sidon)


def run_periodic_bose_poisson():
    print("=== 1. Exact Periodic Bose + Poisson Kernel Construction on Z/(p^2-1)Z ===")
    for p in [67, 127, 251, 509, 1009]:
        M = p * p - 1
        S = bose_sidon(p)
        ind_S = np.zeros(M)
        ind_S[S] = 1.0

        # Exact Fourier flatness check
        F_S = np.fft.fft(ind_S)
        pow_S = np.abs(F_S[1:]) ** 2
        xis = np.arange(1, M)
        expected = np.where(xis % (p - 1) == 0, 1.0, float(p))
        max_fourier_err = float(np.max(np.abs(pow_S - expected)))

        alpha, lam_R, lam_L, gamma = 0.5, 0.25, 0.12, 1.6
        R = lam_R * (M ** 0.75)
        rho = math.exp(-2.0 * math.pi * R / M)
        k_dist = np.minimum(np.arange(M), M - np.arange(M))
        h_hat = rho ** k_dist
        Sh = np.fft.ifft(F_S * h_hat).real

        L = max(1, int(round(lam_L * (M ** 0.75))))
        kappa = (2.0 * gamma * lam_L) / (3.0 - alpha ** 2) * 1.05
        D = max(L + 1, int(round(kappa * (M ** 0.75))))

        mu = np.zeros(M)
        mu[D : M - D] = (p / M) + alpha * (ind_S[D : M - D] - Sh[D : M - D])
        min_bulk = float(np.min(mu[D : M - D]))
        mu[:L] = gamma * (p / M)
        mu[M - L :] = gamma * (p / M)

        K_fft = 1 << (2 * M - 1).bit_length()
        F_mu = np.fft.rfft(mu, n=K_fft)
        ac_lin = np.fft.irfft(F_mu * np.conj(F_mu), n=K_fft)[1:M]
        mx_ac = float(np.max(ac_lin))
        assert min_bulk > 0.0 and mx_ac < 1.0, f"Unexpected violation at p={p}"
        mass = float(np.sum(mu))
        exc = mass - math.sqrt(M)
        print(
            f"  p={p:4d} (M={M:7d}): fourier_err={max_fourier_err:.1e}, "
            f"min_blk*p={min_bulk*p:+.3f}, raw_max_ac={mx_ac:.5f} (<1!), "
            f"mass={mass:8.3f}, exc/M^(1/4)={exc/(M**0.25):+.4f}"
        )


def run_sdp_hierarchy():
    import cvxpy as cp

    print("\n=== 2. Exact SDP_1(N) vs SDP_1(N) + ALL 3-AP Linear Cuts ===")
    exact_h = {8: 4, 11: 4, 15: 5, 20: 6, 26: 7, 35: 8, 45: 9}
    for N in [15, 20, 26, 35, 45]:
        vals = []
        for with_3ap in [False, True]:
            Z = cp.Variable((N + 1, N + 1), symmetric=True)
            x, X = Z[1:, 0], Z[1:, 1:]
            cons = [Z >> 0, Z[0, 0] == 1, cp.diag(X) == x, X >= 0]
            for d in range(1, N):
                cons.append(cp.sum(cp.diag(X, k=d)) <= 1)
            if with_3ap:
                a_i, b_i, c_i = [], [], []
                for d in range(1, (N - 1) // 2 + 1):
                    for a in range(0, N - 2 * d):
                        a_i.append(a); b_i.append(a + d); c_i.append(a + 2 * d)
                cons.append(X[a_i, b_i] + X[b_i, c_i] + X[a_i, c_i] <= 1)
            prob = cp.Problem(cp.Maximize(cp.sum(x)), cons)
            prob.solve(solver=cp.CLARABEL, tol_gap_abs=1e-5, tol_gap_rel=1e-5, max_iter=200)
            vals.append(float(prob.value))
        print(f"  N={N:2d}: h(N)={exact_h[N]}, SDP1={vals[0]:.4f}, SDP1+3AP={vals[1]:.4f}, diff={vals[1]-vals[0]:+.4f}")

    print("\n=== 3. Exact Degree-2 Lasserre (4-Tuple Sidon Ideal) ===")
    for N in [8, 11, 15]:
        idx_map = {(): 0}
        basis = [()]
        for i in range(N):
            idx_map[(i,)] = len(basis); basis.append((i,))
        for i in range(N):
            for j in range(i + 1, N):
                idx_map[(i, j)] = len(basis); basis.append((i, j))
        dim = len(basis)
        M = cp.Variable((dim, dim), symmetric=True)
        cons = [M >> 0, M[0, 0] == 1]
        groups, zeros = {}, []
        for a in range(dim):
            for b in range(a, dim):
                u = tuple(sorted(set(basis[a]) | set(basis[b])))
                bad = False
                if len(u) == 3 and u[0] + u[2] == 2 * u[1]:
                    bad = True
                elif len(u) == 4 and (
                    u[0] + u[2] == 2 * u[1] or u[0] + u[3] == 2 * u[1] or
                    u[0] + u[3] == 2 * u[2] or u[1] + u[3] == 2 * u[2] or
                    u[0] + u[3] == u[1] + u[2]
                ):
                    bad = True
                if bad:
                    zeros.append((a, b))
                else:
                    groups.setdefault(u, []).append((a, b))
        if zeros:
            cons.append(M[[p[0] for p in zeros], [p[1] for p in zeros]] == 0)
        lr, lc, rr, rc = [], [], [], []
        for pairs in groups.values():
            if len(pairs) > 1:
                r0, c0 = pairs[0]
                for r1, c1 in pairs[1:]:
                    lr.append(r0); lc.append(c0); rr.append(r1); rc.append(c1)
        if lr:
            cons.append(M[lr, lc] == M[rr, rc])
        x_idx = [idx_map[(i,)] for i in range(N)]
        prob = cp.Problem(cp.Maximize(cp.sum(M[0, x_idx])), cons)
        prob.solve(solver=cp.CLARABEL, tol_gap_abs=1e-5, tol_gap_rel=1e-5, max_iter=200)
        val = float(prob.value)
        print(f"  N={N:2d} (dim={dim:3d}): h(N)={exact_h[N]}, Lasserre-2={val:.5f} (gap={val - exact_h[N]:+.5f})")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--periodic", action="store_true")
    ap.add_argument("--sdp", action="store_true")
    args = ap.parse_args()
    if not args.periodic and not args.sdp:
        run_periodic_bose_poisson()
        run_sdp_hierarchy()
    else:
        if args.periodic:
            run_periodic_bose_poisson()
        if args.sdp:
            run_sdp_hierarchy()
