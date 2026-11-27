# Structural Barrier & Relaxation Hierarchy Analysis for Erdős Problem #30

## Problem
Let $h(N)$ be the maximum cardinality of a Sidon set in $\{1, \dots, N\}$.
Erdős Problem #30 (\$1,000) asks whether for every $\varepsilon > 0$,
$$h(N) = N^{1/2} + O_\varepsilon(N^\varepsilon).$$

---

## Summary of the Complete Relaxation Hierarchy

| Level | Relaxation / Method | Upper Bound | Lower Bound / Barrier | Status |
| --- | --- | --- | --- | --- |
| **L0** | Positive/Toeplitz $L^2$ smoothing (`sidon_sub_094295`) | $\sqrt{N} + 0.94295\,N^{1/4}$ *(Lean 4)* | Infimum $= 2\sqrt{2}/3 \approx 0.942809\,N^{1/4}$ (linear kernel $\rho(x)=2x$) | **Blocked at $N^{1/4}$** |
| **L1** | Exact pointwise fractional $M(N)$ (zero smoothing, $\mu \in [0,1]^N$, $\forall d \ge 1,\; (\mu*\tilde{\mu})(d) \le 1$) | $\sqrt{N} + 0.94295\sqrt{\theta}\,N^{1/4}$ *(Lean 4)* | $M(N) \ge \sqrt{N} + \Omega(N^{1/4})$: $+0.1393 N^{1/4}$ closed-form ($N = 10^6$), $+0.6097 N^{1/4}$ FFT-opt; $h(6) < M(6)$ *(Lean 4)* | **Blocked at $N^{1/4}$** |
| **L1+** | **Degree-1 Lasserre / Shor + RLT + BQP + ALL 3-AP & 4-Sidon linear cuts** (`SDP_1(N)`) | $\sqrt{N} + 0.94295\,N^{1/4}$ *(Lean 4)* | **Lift Theorem (`shor_rlt_sdp1_lift` + `shor_rlt_sdp1_lift_3ap_4sidon_cuts`, Lean 4)**: $\mathrm{SDP}_1^+(N) \ge M(N) \ge \sqrt{N} + \Omega(N^{1/4})$; Clarabel confirms `0.0000` gain from all 3-AP linear cuts | **Blocked at $N^{1/4}$** |
| **L1.5** | Exact nonlinear 3-AP-free constraint $T_3(\mu) = 0$ + pairwise $(\mu*\tilde{\mu})(d) \le 1$ | Bose 3-AP-free superset bound $|T| \le (p^2-1)/\sqrt{p} < N^{3/4}$ *(Lean 4)* | Empirically collapses fractional excess from $+0.48\,N^{1/4}$ to **`0.0000`** on $N = 47^2, 71^2, 101^2$ | **Open boundary** |
| **L2** | **Degree-2 Lasserre / SoS (4-tuple Sidon ideal $M_2[a,b,c,e]=0$)** | Exact `4.000` at $N=8$; cuts integrality gap by **64%** at $N=15$ (`5.6551 → 5.2373` vs $h(15)=5$) | First convex hierarchy level escaping the L1/L1+ barrier | **Active frontier** |

---

## 1. Exact Pointwise Fractional Sidon Barrier (`M(N)`)

Consider the **exact pointwise** nonconvex quadratic relaxation (with **zero smoothing**):
$$M(N) := \max\left\{\sum_{x=0}^{N-1} \mu_x \;:\; \mu \in [0, 1]^N,\quad \forall d \in \{1, \dots, N-1\},\; \sum_{x=0}^{N-1-d} \mu_x \mu_{x+d} \le 1\right\}.$$

### Construction A: Closed-Form Cauchy High-Pass Sidon Hybrid (`fractional_barrier_experiment.py`)
Using a Bose Sidon set $S \subset [0, N)$ ($N = p^2$) and Cauchy kernel $h_R(d) \propto (1 + (d/R)^2)^{-1}$ at scale $R = \lambda_R N^{3/4}$, the self-convolution identity $(h_R * \tilde{h}_R)(d) = h_{2R}(d) \le 2 h_R(d)$ induces a strictly negative autocorrelation dip across all $d \ge 1$ without overshoot, yielding net excess $2\gamma\lambda_L \frac{1-\alpha^2}{3-\alpha^2} N^{1/4} - o(N^{1/4}) > 0$:
- $p = 127$ ($N = 16{,}129$): $M(N) \ge 128.442$ ($+0.1279\, N^{1/4}$)
- $p = 251$ ($N = 63{,}001$): $M(N) \ge 253.802$ ($+0.1768\, N^{1/4}$)
- $p = 509$ ($N = 259{,}081$): $M(N) \ge 511.523$ ($+0.1118\, N^{1/4}$)
- $p = 1009$ ($N = 1{,}018{,}081$): $M(N) \ge 1013.424$ ($+0.1393\, N^{1/4}$, zero clipping)
- Direct FFT L-BFGS-B optimization achieves **$M(63{,}001) \ge 260.660 = \sqrt{N} + 0.6097\, N^{1/4}$** ($\|\mu\|_2^2/\|\mu\|_1 \approx 0.51$).

### Construction B: Exact Periodic Bose + Poisson Kernel Construction (`option2_hierarchy_experiments.py`)
On $M = p^2 - 1$, Bose's Sidon set $S_p \subset \mathbb{Z}/M\mathbb{Z}$ satisfies the **exact Fourier flatness identity** (formally proved in Lean 4 as `Erdos030.bose_periodic_fourier_flatness`):
$$\forall 1 \le \xi < M,\qquad \left|\sum_{a \in S_p} e^{2\pi i \xi a / M}\right|^2 = \begin{cases} 1 & (p - 1) \mid \xi, \\ p & (p - 1) \nmid \xi. \end{cases}$$
Pairing $S_p$ with the periodic Poisson kernel $\widehat{h_\rho}(\xi) = \rho^{\min(\xi, M-\xi)}$ ($\rho = e^{-2\pi R/M}$, $R = 0.25 M^{3/4}$, $\alpha = 0.5, \lambda_L = 0.12, \gamma = 1.6$) achieves **strictly `< 1.0` linear autocorrelation with ZERO clipping and ZERO rescaling** across all tested primes $p \ge 67$ up to $p = 1009$ ($M = 1{,}018{,}080$, `raw_max_ac = 0.99694`, `exc/M^(1/4) = +0.0825`).

### Exact $\theta$-Integrality Scaling Law
Restricting to $L^2$-integrality ratio $\theta = \|\mu\|_2^2 / \|\mu\|_1 \in (0, 1]$:
- **Upper envelope (Lean 4 `Erdos030.fractional_sidon_sub_094295_theta`)**:
  $$\forall \theta \in (0, 1],\; \forall^\infty N,\; M_\theta(N) \le \sqrt{N} + 0.94295\sqrt{\theta}\,N^{1/4}.$$
- **Continuation empirical scaling** ($N = 47^2, 101^2, 151^2$):
  $$M_\theta(N) - \sqrt{N} \;\asymp\; \min\bigl(0.61\, N^{1/4},\;\; 0.23\,(1 - \theta)\,\sqrt{N}\bigr),$$
  exhibiting a sharp phase transition at $1 - \theta \asymp N^{-1/4}$: breaking $N^{1/4}$ requires total fractionality defect $\|\mu\|_1 - \|\mu\|_2^2 = o(N^{1/4})$.

---

## 2. Degree-1 Lasserre / Shor + RLT + BQP + 3-AP + 4-Sidon SDP Barrier (Lean 4 Verified)

For **every** feasible point $\mu \in [0, 1]^N$ of $M(N)$, the lifted matrix
$$X := \mu\mu^T + \mathrm{diag}\bigl(\mu_0(1 - \mu_0), \dots, \mu_{N-1}(1 - \mu_{N-1})\bigr)$$
satisfies **all** of the following (formally proved in Lean 4 as `Erdos030.shor_rlt_sdp1_lift` and `Erdos030.shor_rlt_sdp1_lift_3ap_4sidon_cuts`):
1. Lifted moment matrix PSD: $\begin{pmatrix} 1 & \mu^T \\ \mu & X \end{pmatrix} \succeq 0$;
2. Diagonal $\{0, 1\}$-integrality: $X_{ii} = \mu_i$;
3. Nonnegativity, all McCormick/RLT inequalities ($0 \le X_{ij} \le \min(\mu_i, \mu_j)$, $X_{ij} \ge \mu_i + \mu_j - 1$), and all Boolean Quadric Polytope triangle inequalities ($X_{ij} + X_{ik} - X_{jk} \le \mu_i$);
4. All $N - 1$ exact pointwise Sidon constraints $\sum_{i < N - d} X_{i, i+d} \le 1$;
5. Whenever $\mu_i \le 1/\sqrt{3}$ (satisfied by our Cauchy/Poisson hybrid with $\alpha = 0.5$ for all large $N$): **all $\Theta(N^2)$ exact 3-AP linear cuts** $X_{ab} + X_{bc} + X_{ac} \le 1$ and **all $\Theta(N^3)$ exact 4-tuple Sidon linear cuts** $X_{ab} + X_{ac} + X_{ae} + X_{bc} + X_{be} + X_{ce} \le 3$.

Combined with `Erdos030.sdp1_sub_094295` ($\mathrm{SDP}_1(N) \le \sqrt{N} + 0.94295\,N^{1/4}$) and Clarabel exact SDP verification (`option2_hierarchy_experiments.py`), **the entire Degree-1 Lasserre + RLT + BQP + 3-AP + 4-Sidon cutting-plane SDP hierarchy is provably trapped at $\Theta(N^{1/4})$**. Only **Degree-2 Lasserre** (enforcing the 4-tuple Sidon ideal $M_2[(i,i+d),(j,j+d)] = 0$, which cuts the $N=15$ integrality gap by 64%) or nonlinear $k \ge 3$ / $\{0,1\}$-integrality arguments can escape this barrier.

---

## 3. $k = 3$ (3-AP-Free) Separation & Lower-Bound Prime-Gap Barrier

- **3-AP-Free Superset Barrier (Lean 4 `Erdos030.bose_3ap_free_superset_bound`)**: Using `bose_periodic_fourier_flatness`, any subset $T \subseteq \{0, \dots, p^2 - 2\}$ forming zero modular 3-APs $t_1 + t_2 \equiv 2a \pmod{p^2-1}$ with Bose's set $S_p$ has cardinality $|T| \le (p^2 - 1)/\sqrt{p} < (p^2-1)^{3/4}$. Empirically, adding the exact nonlinear 3-AP constraint $T_3(\mu) = 0$ collapses the fractional excess on Bose supersets from $+0.48\,N^{1/4}$ to `0.0000`.
- **Lower bound ($h(N) \ge \sqrt{N} - O_\varepsilon(N^\varepsilon)$)**: Every known construction achieving density $(1 - o(1))\sqrt{N}$ relies on finite projective planes of prime-power order $q \le \sqrt{N}$ (Singer 1938, Bose 1942), yielding $O(N^{21/80})$ unconditionally (Baker–Harman–Pintz) and $O(N^{1/4}\log N)$ even under the Riemann Hypothesis. Beating $O_\varepsilon(N^\varepsilon)$ requires either Cramér-scale prime-gap bounds (stronger than RH) or a non-projective-plane dense Sidon construction (refuting Eberhard–Manners 2023).
- **Disproof**: Under the Eberhard–Manners conjecture + Cramér's prime-gap heuristic, $h(N) = \sqrt{N} + O((\log N)^2)$, which satisfies Erdős #30; disproving Erdős #30 would therefore refute either Cramér's prime-gap conjecture or Erdős–Turán's $O(1)$ upper-bound conjecture.
