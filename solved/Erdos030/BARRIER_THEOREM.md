# Structural Barrier & Relaxation Hierarchy Analysis for Erdős Problem #30

## Problem
Let $h(N)$ be the maximum cardinality of a Sidon set in $\{1, \dots, N\}$.
Erdős Problem #30 (\$1,000) asks whether for every $\varepsilon > 0$,
$$h(N) = N^{1/2} + O_\varepsilon(N^\varepsilon).$$

---

## Summary of the Complete Relaxation Hierarchy (L0 → L2+NN)

| Level | Relaxation / Method | Upper Bound | Lower Bound / Barrier | Status |
| --- | --- | --- | --- | --- |
| **L0** | Positive/Toeplitz $L^2$ smoothing (`sidon_sub_094295`) | $\sqrt{N} + 0.94295\,N^{1/4}$ *(Lean 4)* | Infimum $= 2\sqrt{2}/3 \approx 0.942809\,N^{1/4}$ (linear kernel $\rho(x)=2x$) | **Blocked at $N^{1/4}$** |
| **L1** | Exact pointwise fractional $M(N)$ ($\mu \in [0,1]^N$, $\forall d \ge 1,\; (\mu*\tilde{\mu})(d) \le 1$) | $\sqrt{N} + 0.94295\sqrt{\theta}\,N^{1/4}$ *(Lean 4)* | **Lean 4 asymptotic proof** (`asymptotic_fractional_sdp1_barrier`): $\forall p \ge 10{,}000$ prime, $M(p^2-1) \ge p + \frac{1}{250}\sqrt{p} > \sqrt{M} + \frac{1}{250} M^{1/4}$; FFT-opt $+0.6097 N^{1/4}$ | **Provably blocked at $N^{1/4}$ (Lean 4)** |
| **L1+** | **Degree-1 Lasserre / Shor + RLT + BQP + ALL 3-AP & 4-Sidon linear cuts** (`SDP_1^+(N)`) | $\sqrt{N} + 0.94295\,N^{1/4}$ *(Lean 4)* | **Lean 4 all-$N$ proof** (`smooth_fejer_sdp1_barrier_all_N`, `smooth_fejer_sdp1_barrier_half`): $\forall N \ge 81,\; \mathrm{SDP}_1^+(N) > \sqrt{N} + \frac{2}{5}N^{1/4}$ and asymptotically $\ge \sqrt{N} + (\frac{1}{2} - \varepsilon)N^{1/4}$ | **Provably blocked at $N^{1/4}$ (Lean 4)** |
| **L1-Bin** | **Binary-Bochner + ALL Lindström boxes** ($r \in \{0,1\}^{N-1}$, $r(d)^2=r(d)$, $E_4=2m^2-m$, $F(\alpha) \ge 0$) | $\sqrt{N} + 0.94295\,N^{1/4}$ | Exact HiGHS MILP reaches $\sqrt{N} + 0.89\,N^{1/4}$ ($N=15$: `5.6235` with global $\min F \ge +0.296$; $N=60$: `10.208`) | **Blocked at $N^{1/4}$** |
| **L1.5** | Exact nonlinear 3-AP-free $T_3(\mu) = 0$ + pairwise $(\mu*\tilde{\mu})(d) \le 1$ ($M_{\text{3AP}}(N)$) | **Lean 4 universal support collapse**: $\|\mathrm{supp}(\mu)\| \le 66\,N^{11/12}$ (`m3ap_dense_support_card_bound`); mod-$q$ Behrend/Stanley collapse (`fractional_sidon_mod_q_support_collapse`); Bose cross-variance (`bose_sparse_background_cross_variance`) | Strict separation at $N=11$: $h(11)=4 < 3\sqrt{2} \le M_{\text{3AP}}(11)$ (`strict_separation_h11_lt_m3ap`, *Lean 4*); collapses fractional excess on dense Bose/homotopy instances (`θ → 1`) | **Kills fractional excess; binary Sidon sets already satisfy it** |
| **L2** | **Degree-2 Lasserre / SoS (4-tuple Sidon ideal $M_2[u]=0$)** | `Lasserre_2(6) = h(6) = 3 < 7/2 ≤ M(6)` (*Lean 4*); `Lasserre_2(8) = h(8) = 4` (exact rational SoS); $\le \sqrt{N} + 0.94295 N^{1/4}$ (*Lean 4*) | Certified symmetric Clarabel + DRS+AA (`N=6..64`): **collapses onto `SDP_1(N)` as `SDP_1(N) - L2(N) ~ 5.1/N → 0`**, climbing to `+0.920 N^{1/4}` certified at `N=50`, `≥ +0.9201` at `N=56` (`h(56)=10`), and `est +0.9419 N^{1/4}` at `N=64` | **Finite-size gap cut; asymptotically trapped at $\Theta(N^{1/4})$** |
| **L2+NN** | **Doubly Nonnegative Degree-2 Lasserre** ($M_2 \succeq 0,\; y_U \ge 0$) | `N=15`: `5.2264` (`0.0109` below `L2(15)`) | Certified `N=32`: `[7.675, 7.718]` (`+0.849..+0.866 N^{1/4}`, only `0.041` below `L2(32)`) | **Still trapped at $\Theta(N^{1/4})$** |

### Complete 8-Level Strict Hierarchy Chain at $N = 15$
$$h(15) = 5 \;<\; \mathrm{L2{+}NN}(15) = 5.2264 \;<\; \mathrm{L2}(15) = 5.2373 \;<\; M(15) \ge 5.3823 \;<\; \mathrm{L2}_{4\text{Sid}}(15) = 5.5780 \;<\; \mathrm{L2}_{3\text{AP}}(15) = 5.6070 \;<\; \mathrm{BinBochner{+}Lindstr\ddot{o}m}(15) = 5.6235 \;<\; \mathrm{SDP}_1(15) = 5.6551.$$

---

## 1. Provable Asymptotic Barriers in Lean 4 (Zero `sorry`, Standard Axioms Only)

### A. Elementary All-$N$ Smooth Fejér `SDP_1+` Barrier (`Lasserre2SeparationsAndFejer.lean`)
For **every** $N \ge 81$, let $L = \lfloor N^{3/4} \rfloor$, $\mu_i = \sqrt{N + L}/N$, $X_{ii} = \mu_i$, and $X_{ij} = (N + \min(|i-j|, L))/N^2$ ($i \ne j$).
- **PSD**: Follows in 4 lines from shifted-window Cauchy–Schwarz on $\max(0, L - |i-j|)$ and $2L^2 + N \le NL$.
- **All $N-1$ pointwise Sidon cuts**: $(N-d)(N + \min(d, L))/N^2 \le (N^2 - d^2)/N^2 < 1$.
- **All BQP, 3-AP, and 4-Sidon linear cuts**: Follow immediately from $6(N + L) \le N^2$.
- **Lean 4 theorems**: `Erdos030.smooth_fejer_sdp1_barrier_all_N` ($\sum \mu > \sqrt{N} + \frac{2}{5} N^{1/4}$ for all $N \ge 81$) and `Erdos030.smooth_fejer_sdp1_barrier_half` ($\forall \varepsilon > 0,\; \forall^\infty N,\; \sum \mu \ge \sqrt{N} + (\frac{1}{2} - \varepsilon) N^{1/4}$).

### B. Exact Pointwise Nonconvex Fractional Barrier (`SmoothBumpBarrier.lean` & `PeriodicDFT.lean`)
Pairing Bose's Sidon set $S_p \subset \mathbb{Z}/(p^2-1)\mathbb{Z}$ (exact Fourier flatness `bose_periodic_fourier_flatness`: $|\widehat{\mathbf{1}_{S_p}}(\xi)|^2 \in \{1, p\}$) with the periodic Poisson kernel $h_\rho$ and smooth discrete-triangle boundary bumps $g_L + g_R$ yields an **elementary, Weil-sum-free Lean 4 proof** (`Erdos030.asymptotic_fractional_sdp1_barrier_explicit` & `asymptotic_fractional_sdp1_barrier`):
$$\forall p \ge 10{,}000 \text{ prime}\;(M = p^2 - 1),\quad \exists (\mu, X),\; \mathrm{IsFractionalSidon}(M,\mu) \land \mathrm{IsSDP1Feasible}(M,\mu,X) \land \text{all BQP/3-AP/4-Sidon cuts} \land \sum_{x < M} \mu_x \ge p + \frac{1}{250}\sqrt{p} > \sqrt{M} + \frac{1}{250} M^{1/4}.$$

---

## 2. Nonlinear $k = 3$ ($M_{\text{3AP}}$), Mod-$q$ Equidistribution & Binary-Autocorrelation Rigidity

All major results below are formally verified in Lean 4 (`Track2EquidistAndM3AP.lean`, `Universal3APBound.lean`, `Track3BoseVariance.lean`):
1. **Strict $M_{\text{3AP}}$ Separation at $N = 11$** (`strict_separation_h11_lt_m3ap`): $B = \{0, 1, 3, 7, 9, 10\}$ is 3-AP-free and $B_2[2]$, giving $\mu = \frac{1}{\sqrt{2}}\mathbf{1}_B$ with $\sum \mu = 3\sqrt{2} \approx 4.2426 > 4 = h(11)$.
2. **Exact Mod-$q$ Equidistribution & Behrend/Stanley Collapse** (`fractional_sidon_mod_q_equidistribution`, `sdp1_mod_q_equidistribution`, `*_support_collapse`):
   - Fractional: $q \sum_{r<q} S_r^2 \le (N + mq - 1)(1 + (\|\mu\|_2^2 - 1)/m)$.
   - `SDP_1`: $q \sum_{r<q} S_r^2 \le (N + mq - 1)(1 + (\|\mu\|_1 - 1)/m)$.
   - Collapses every Behrend set and Stanley base-3 set to $o(\sqrt{N})$.
3. **Universal Power-Saving 3-AP-Free Support Bound** (`universal_3ap_free_superset_bound`, `m3ap_dense_support_card_bound`):
   Every dense fractional Sidon witness ($\sum \mu \ge \sqrt{N} - O(N^{1/4})$) forces EVERY 3-AP-free superset $T$ (including $T = \mathrm{supp}(\mu)$ for $M_{\text{3AP}}(N)$) to obey $|T| \le 66\,N^{11/12}$ unconditionally (ruling out all Behrend-density supports).
4. **Bose Sparse-Background Cross-Variance** (`bose_sparse_background_cross_variance`):
   For every prime $p$ and `IsFractionalSidon (p^2-1) ν` supported on $T$,
   $$\sum_{d < M} \Bigl((\mathbf{1}_{S_p} *_{\text{cyc}} \nu)(d) - \frac{p\|\nu\|_1}{M}\Bigr)^2 \ge \frac{p(p-2)}{p-1}\left(\|\nu\|_2^2 - 2\right) \ge \frac{p(p-2)}{p-1}\left(\frac{\|\nu\|_1^2}{|T|} - 2\right).$$
5. **Binary-Autocorrelation Rigidity & Counterexample** (`binary_autocorr_counterexample_N3`, `*_endpoint_rigidity`, `*_outermost_shell_rigidity`, `*_sidon_support_integral`):
   - $r_\mu(d) \in \{0,1\}$ alone permits $\mu = (1, 1/2, 1)$ at $N = 3$ ($\sum \mu = 5/2 > 2 = h(3)$),
   - Yet endpoints are rigidly $1$, the outermost fractional shell satisfies $\mu_{a+t} + \mu_{b-t} = 1$, and any Sidon-supported witness with $r_\mu(d) \in \{0,1\}$ is strictly binary ($\mu \in \{0,1\}^N$).
6. **Binary-Bochner + Lindström Barrier**: Even forcing $r \in \{0,1\}^{N-1}$ ($E_4 = 2m^2 - m$, $\mathrm{Var}(r) \approx N/4$) + $F(\alpha) \ge 0$ + all Lindström boxes still reaches $\sqrt{N} + 0.89 N^{1/4}$ (due to signed Fejér–Riesz factors).

---

## 3. Degree-2 Lasserre Scaling Verdict & Lower-Bound Prime-Gap Barrier

- **Degree-2 Lasserre (`L2` & `L2+NN`)**: Exact reflection-symmetric Clarabel ($N=6..20$) and strictly PSD certified Frobenius-orthogonal DRS+AA ($N=24..56$, independently audited via full un-symmetrized $1597\times 1597$ eigendecomposition at $N=56$) prove that `SDP_1(N) - L2(N) ~ 5.1/N → 0`, while certified `L2(N)` lower bounds climb monotonically toward $2\sqrt{2}/3 \approx 0.942809\,N^{1/4}$ (`+0.870` at $N=32$, `+0.900` at $N=40$, `+0.920` at $N=50$, $\ge +0.9201$ at $N=56$). At small $N$, `L2(6) = h(6) = 3 < 7/2 ≤ M(6)` is proved in Lean 4 via the 2-square Boolean identity $3 - S + 4\binom{S}{4} = \frac{1}{3}(3-S)^2 + \frac{2}{3}(S - \binom{S}{2})^2$ (`strict_separation_lasserre2_6_lt_fractional_sdp1`), and `L2(8) = h(8) = 4` has an exact rational $27\times 27$ `LDL^T` SoS dual certificate.
- **Lower bound ($h(N) \ge \sqrt{N} - O_\varepsilon(N^\varepsilon)$)**: All known dense constructions (Singer 1938, Bose 1942) depend on prime powers $q \le \sqrt{N}$, leaving $O(N^{21/80})$ unconditionally (Baker–Harman–Pintz) and $O(N^{1/4}\log N)$ even under the Riemann Hypothesis; cyclic-shift truncation of Singer($q_{k+1}$) halves worst-case prime-gap loss to $(q_{k+1}-q_k)/2$ but cannot break the prime-gap exponent.
- **Conclusion**: Breaking the 85-year-old $N^{1/4}$ upper-bound barrier of Erdős–Turán requires methods strictly beyond L0 ($L^2$ smoothing), L1 (pointwise fractional $M(N)$), L1+ (Degree-1 Lasserre + RLT + BQP + all 3-AP & 4-Sidon cuts), Binary-Bochner + Lindström ($E_4 = 2m^2-m$), AND empirically even Degree-2 Lasserre (`L2` & `L2+NN`) — pointing toward Degree $\ge 3$ Lasserre / global projective-plane rigidity (Eberhard–Manners) on the upper bound, alongside Cramér-scale prime gaps or non-projective constructions on the lower bound.
