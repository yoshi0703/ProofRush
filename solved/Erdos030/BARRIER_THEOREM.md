# Structural Barrier Analysis for Erdős Problem #30

## Problem
Let $h(N)$ be the maximum cardinality of a Sidon set in $\{1, \dots, N\}$.
Erdős Problem #30 (\$1,000) asks whether for every $\varepsilon > 0$,
$$h(N) = N^{1/2} + O_\varepsilon(N^\varepsilon).$$

---

## 1. Exact Pointwise Fractional Sidon Barrier (New Structural Result)

Every known upper-bound proof for $h(N)$ — Erdős–Turán (1941), Lindström (1969), Balogh–Füredi–Roy (2023), O'Bryant (2022), Carter–Hunter–O'Bryant (2025), Hou–Zhao (Sep 2026), Carter–O'Bryant–Tao (Oct 2026), and our Lean-verified $0.94295 N^{1/4}$ theorem — passes through the pairwise autocorrelation bound $r_{A-A}(d) \le 1$ ($d \ne 0$) and box bounds $0 \le \mathbf{1}_A(x) \le 1$.

Consider the **exact pointwise** nonconvex quadratic relaxation (with **zero smoothing**):
$$M(N) := \max\left\{\sum_{x=0}^{N-1} \mu_x \;:\; \mu \in [0, 1]^N,\quad \forall d \in \{1, \dots, N-1\},\; \sum_{x=0}^{N-1-d} \mu_x \mu_{x+d} \le 1\right\}.$$

Clearly $h(N) \le M(N)$ for all $N$. Previous barrier theorems (e.g., Carter–O'Bryant–Tao Theorem 5.2, $\sqrt{\alpha\beta} > 1/\sqrt{2}$, and the $2\sqrt{2}/3$ smoothing limit) only ruled out **smoothed** linear/convex $L^2$ bounds. One might ask whether keeping all $N - 1$ exact pointwise constraints $(\mu * \tilde{\mu})(d) \le 1$ already forces $M(N) = \sqrt{N} + o(N^{1/4})$.

### Finding: NO — $M(N) \ge \sqrt{N} + \Omega(N^{1/4})$!

Define the **Cauchy High-Pass Sidon Hybrid** on $N = p^2$ using a Bose/Singer Sidon set $S \subset [0, N)$ and the Cauchy kernel $h_R(d) \propto \bigl(1 + (d/R)^2\bigr)^{-1}$ at scale $R = \lambda_R N^{3/4}$:
$$\mu(x) := \begin{cases}
\dfrac{\gamma}{\sqrt{N}} & x \in [0, L) \cup [N - L, N), \\[6pt]
0 & x \in [L, D) \cup [N - D, N - L), \\[6pt]
\dfrac{1}{\sqrt{N}} + \alpha\bigl(\mathbf{1}_{S_{\mathrm{mid}}} - \mathbf{1}_{S_{\mathrm{mid}}} * h_R\bigr)(x) & x \in [D, N - D),
\end{cases}$$
where $L = \lambda_L N^{3/4}$, $D = \kappa N^{3/4}$ ($\kappa = \frac{2\gamma\lambda_L}{3 - \alpha^2}$), and $\alpha \in (0, 1)$.

### Why It Works (Key Fourier Mechanism)
1. **Zero bulk mass loss**: $\sum (\mathbf{1}_{S_{\mathrm{mid}}} - \mathbf{1}_{S_{\mathrm{mid}}} * h_R) = 0$, so the bulk carries full density $1/\sqrt{N}$ on $[D, N - D)$.
2. **Automatic positivity**: By Singer/Bose Fourier flatness ($|\widehat{\mathbf{1}_S}(\xi)| = \sqrt{q}$), $(\mathbf{1}_S * h_R)(x) = N^{-1/2}(1 + O(1/(\pi \lambda_R)))$ uniformly, keeping $\mu \ge 0$ everywhere on $[D, N-D)$.
3. **Zero-overshoot Cauchy autocorrelation dip**: Because the convolution of two Cauchy kernels satisfies $(h_R * \tilde{h}_R)(d) = h_{2R}(d) \le 2 h_R(d)$ **pointwise for every $d \in \mathbb{Z}$**, the diagonal term $\sqrt{N}\delta_0$ of $\mathbf{1}_S * \tilde{\mathbf{1}}_S$ induces a strictly negative dip
   $$-\alpha^2\sqrt{N}\bigl(2 h_R(d) - h_{2R}(d)\bigr) = -\frac{\alpha^2}{\pi \lambda_R N^{1/4}}\left(\frac{2}{1 + (d/R)^2} - \frac{1/2}{1 + (d/(2R))^2}\right) < 0$$
   for every $d \ge 1$, creating $O(N^{-1/4})$ free autocorrelation headroom at $1 \le d \le L$ to absorb the endpoint spikes $2\gamma^2\lambda_L N^{-1/4}$ without any overshoot at $d > L$.
4. **Net mass excess**: Setting $\kappa = \frac{2\gamma\lambda_L}{3 - \alpha^2}$ balances spike–bulk cross-correlation against the geometric moat slack $(3 - \alpha^2)\kappa N^{-1/4}$, yielding strictly positive net mass gain
   $$\sum_{x=0}^{N-1} \mu_x - \sqrt{N} = 2\gamma\lambda_L \cdot \frac{1 - \alpha^2}{3 - \alpha^2}\, N^{1/4} - o(N^{1/4}) > 0.$$

### Empirical Verification (`fractional_barrier_experiment.py`)
- Closed-form formula ($\alpha = 0.5, \lambda_R = \lambda_L = 0.15, \gamma = 1.5$) with exact FFT verification across all $1 \le d < N$:
  - $p = 127$ ($N = 16{,}129$): $M(N) \ge 128.442$ ($+0.1279\, N^{1/4}$)
  - $p = 251$ ($N = 63{,}001$): $M(N) \ge 253.802$ ($+0.1768\, N^{1/4}$)
  - $p = 509$ ($N = 259{,}081$): $M(N) \ge 511.523$ ($+0.1118\, N^{1/4}$)
  - $p = 1009$ ($N = 1{,}018{,}081$): $M(N) \ge 1013.424$ ($+0.1393\, N^{1/4}$, zero clipping)
- Direct FFT L-BFGS-B optimization from Bose Sidon sets achieves **$M(63{,}001) \ge 260.660 = \sqrt{N} + 0.6097\, N^{1/4}$** with $\|\mu\|_2^2 / \|\mu\|_1 \approx 0.51$.

### Consequence for Solving Erdős #30
Any proof that breaks the $N^{1/4}$ exponent on the upper bound **must** break out of the $[0, 1]^N$ pairwise-autocorrelation relaxation by genuinely exploiting **$\{0, 1\}$-integrality** ($\|\mu\|_2^2 = \|\mu\|_1$, where $(1 - \alpha^2)/(3 - \alpha^2) \to 0$) or **higher-order ($k \ge 3$) additive/algebraic structure**.

---

## 2. Lower-Bound & Disproof Obstructions

- **Lower bound ($h(N) \ge \sqrt{N} - O_\varepsilon(N^\varepsilon)$)**: Every known construction achieving density $(1 - o(1))\sqrt{N}$ relies on finite projective planes of prime-power order $q \le \sqrt{N}$ (Singer 1938, Bose 1942), yielding $O(N^{21/80})$ unconditionally (Baker–Harman–Pintz) and $O(N^{1/4}\log N)$ even under the Riemann Hypothesis. Beating $O_\varepsilon(N^\varepsilon)$ requires either Cramér-scale prime-gap bounds (stronger than RH) or a non-projective-plane dense Sidon construction (refuting the Eberhard–Manners 2023 conjecture).
- **Disproof**: Under the Eberhard–Manners conjecture + Cramér's prime-gap heuristic, $h(N) = \sqrt{N} + O((\log N)^2)$, which satisfies Erdős #30; disproving Erdős #30 would therefore refute either Cramér's prime-gap conjecture or Erdős–Turán's $O(1)$ upper-bound conjecture.
