# Erdős Problem #30 — Antigravity Remote Agents Autonomous Handoff

This document enables a fresh **Antigravity Remote Agents** cloud VM session on `yoshi0703/ProofRush` to seamlessly resume the Option 2 deep attack on Erdős Problem #30 without redoing any completed work.

## 1. Current Verified State (Already on `main`)

- **Problem**: Erdős Problem #30 (`https://www.erdosproblems.com/30`, \$1,000): $\forall \varepsilon > 0,\; h(N) = N^{1/2} + O_\varepsilon(N^\varepsilon)$.
- **Audited Statement**: `Formal/Problems/Erdos030/Statement.lean`
  - **LOCKED SHA-256**: `3b2f86d3ed3e5c57f709a36adbe1ebbaa84252bae4b8b4a0b25333f3d0dba9f8`
  - **NEVER modify `Statement.lean`**. On a fresh cloud VM, restore the lock file before running `verify_gate.sh`:
    ```bash
    mkdir -p state/locks
    printf '%s\n' '3b2f86d3ed3e5c57f709a36adbe1ebbaa84252bae4b8b4a0b25333f3d0dba9f8' > state/locks/Erdos030.sha256
    ```
- **Already Lean 4 Verified (10 theorems in `Formal/Problems/Erdos030/Solution.lean`, standard axioms only, 0 `sorry`)**:
  - `Erdos030.sidon_sub_094295` ($\forall^\infty N,\; h(N) \le \sqrt{N} + 0.94295\,N^{1/4}$, beating Hou–Zhao Sep 2026 `0.94349` and Carter–O'Bryant–Tao Oct 2026 `0.94304`)
  - `Erdos030.asymmetric_kernel_transfer`
  - `Erdos030.sidon_sub_0949`, `Erdos030.kernel_transfer_single`
  - `Erdos030.lindstrom_theorem`, `Erdos030.erdos_turan_theorem`, `Erdos030.balogh_furedi_roy_theorem`, `Erdos030.obryant_theorem`, `Erdos030.carter_hunter_obryant_theorem`, `Erdos030.bose_lower_bound_theorem`

## 2. Cloud VM Fast Bootstrap (Do NOT Compile Mathlib From Source!)

```bash
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"
cd Formal && lake exe cache get && lake build Problems.Erdos030.Statement Problems.Erdos030.Solution
cd ..
python3 scripts/state_ctl.py init
mkdir -p state/locks
printf '%s\n' '3b2f86d3ed3e5c57f709a36adbe1ebbaa84252bae4b8b4a0b25333f3d0dba9f8' > state/locks/Erdos030.sha256
```

## 3. New Discoveries Ready to Push to Proof / Formalization (Option 2 Frontier)

### Discovery A: Shor / RLT / Boolean-Quadric Degree-1 Lasserre SDP Barrier (4-Line Algebraic Lift)
For ANY $\mu \in [0, 1]^N$ feasible for the exact pointwise quadratic Sidon relaxation $M(N)$ ($\forall 1 \le d < N,\; \sum_{x < N - d} \mu_x \mu_{x+d} \le 1$), the matrix
$$X := \mu\mu^T + \mathrm{diag}\bigl(\mu_0(1-\mu_0), \dots, \mu_{N-1}(1-\mu_{N-1})\bigr)$$
is **strictly feasible** for the full Degree-1 Lasserre / Shor + RLT + Boolean Quadric Polytope SDP (`SDP_1(N)`):
- $\begin{pmatrix} 1 & \mu^T \\ \mu & X \end{pmatrix} = \begin{pmatrix} 1 \\ \mu \end{pmatrix}\begin{pmatrix} 1 & \mu^T \end{pmatrix} + \begin{pmatrix} 0 & 0 \\ 0 & \mathrm{diag}(\mu(1-\mu)) \end{pmatrix} \succeq 0$,
- $\mathrm{diag}(X) = \mu$, $0 \le X_{ij} \le \min(\mu_i, \mu_j)$, $X_{ij} \ge \mu_i + \mu_j - 1$,
- $\forall 1 \le d < N,\; \sum_{i < N - d} X_{i, i+d} = \sum_{i < N - d} \mu_i \mu_{i+d} \le 1$.
Therefore $\mathrm{SDP}_1(N) \ge M(N) \ge \sqrt{N} + c_0 N^{1/4}$: **neither pairwise autocorrelation nor Degree-1 Lasserre / Shor SDP can break the $N^{1/4}$ exponent**.

### Discovery B: Exact Periodic Bose + Poisson Kernel Construction (Lean 4 Blueprint)
For every prime $p$ and $M = p^2 - 1$, Bose's set $S_p \subset \mathbb{Z}/M\mathbb{Z}$ (`|S_p| = p`, already constructed in `Solution.lean`) satisfies the **exact** periodic difference identity:
- $r^{\text{mod}}_{S_p - S_p}(0) = p$, $r^{\text{mod}}_{S_p - S_p}(d) = 0$ if $(p+1)\mid d$ ($d \ne 0$), and $r^{\text{mod}}_{S_p - S_p}(d) = 1$ otherwise.
- Hence for ALL $1 \le \xi < M$, $|\widehat{\mathbf{1}_{S_p}}(\xi)|^2 = 1$ if $(p-1)\mid\xi$, else $p$ ($\le p$ everywhere!).
- With the periodic Poisson kernel $\widehat{h_\rho}(\xi) = \rho^{\min(\xi, M-\xi)}$ ($\rho = e^{-2\pi R / M}$, $R = 0.25 M^{3/4}$), $2 h_\rho(d) - h_{\rho^2}(d) > 0$ holds pointwise for all $d$, and setting $\mu(x) = \frac{p}{M} + \alpha(\mathbf{1}_{S_p} - \mathbf{1}_{S_p} *_{\text{mod}} h_\rho)(x)$ on $[D, M-D)$ and $\gamma \frac{p}{M}$ on $[0, L) \cup [M-L, M)$ ($\alpha=0.5, \lambda_R=0.25, \lambda_L=0.12, \gamma=1.6$) achieves **strictly `< 1.0` linear autocorrelation with ZERO clipping and ZERO rescaling** across all tested primes $p \in \{67, 127, 251, 509, 1009\}$ (`raw_ac = 0.99694`, `exc/M^(1/4) = +0.0825` at $p = 1009$).
- **Key analytic step remaining for a full asymptotic Lean 4 proof**: bounding the sliding-window discrepancy $\max_d |S_p \cap [d, d + L)| - pL/M|$ below $\lambda_L\sqrt{p}$ (naive $\ell^1$-Fourier gives $\sqrt{p}$, whereas empirical max discrepancy scales as $\approx 1.7\,p^{1/4}$ via Weil/character sums or higher-moment / non-Bose construction).

### Discovery C: Exact $\theta$-Integrality Scaling Law & $k=3$ (3-AP-Free) / $k=4$ Separation
1. **$\theta$-Integrality phase transition** ($\theta = \|\mu\|_2^2 / \|\mu\|_1$):
   Across $N = 47^2, 101^2, 151^2$, continuation L-BFGS-B shows
   $$M_\theta(N) - \sqrt{N} \asymp \min\bigl(0.61\, N^{1/4},\; 0.23\,(1 - \theta)\,\sqrt{N}\bigr),$$
   with phase transition at $1 - \theta \asymp N^{-1/4}$ (matching the analytic upper bound $\|\mu\|_1 \le \sqrt{N} + 0.94295 \sqrt{\|\mu\|_2^2} + o(N^{1/4})$ at small $\theta$, and collapsing linearly as $\theta \to 1^-$).
2. **Exact 3-AP-free constraint ($k = 3$)** $T_3(\mu) = \sum_{x < y,\; 2y-x < N} \mu_x \mu_y \mu_{2y-x} = 0$:
   - **3-line Fourier theorem**: For ANY 3-AP-free superset $B = S_p \cup T$ of Bose's set $S_p$, $|T| \le N^{3/4}$ (by $\sum \mathbf{1}_{t_1+t_2=2a} = 0$ and $|\widehat{\mathbf{1}_{S_p}}(2\xi)| \le \sqrt{p}$).
   - Empirically on $N = 47^2, 71^2, 101^2$, adding $T_3(\mu) = 0$ collapses the fractional excess from $+0.48\,N^{1/4}$ all the way to **`0.0000`**!
3. **4-tuple Sidon constraint ($k = 4$ / Degree-2 Lasserre)**:
   $Q_4(\mu) := \sum_{d=1}^{N-1}\bigl((\sum_x \mu_x \mu_{x+d})^2 - \sum_x \mu_x^2 \mu_{x+d}^2\bigr) = 0$ characterizes Sidon support exactly.

## 4. Concrete Priority Research Tasks for Remote Agents

1. **Attack 1 (Breaking $N^{1/4}$ via $k=3$ / $k=4$ / $\{0,1\}$-Integrality)**:
   - Rigorously determine whether $M_{\text{3AP}}(N) = \sqrt{N} + o(N^{1/4})$ or whether a structured 3-AP-free fractional measure still beats $\sqrt{N} + c N^{1/4}$.
   - Investigate **Degree-2 Lasserre / Sum-of-Squares** ($Q_4 = 0$, $r(d)^2 = r(d)$, $L^4$ additive energy) and **$\{0,1\}$-integrality** ($\|\mu\|_2^2 = \|\mu\|_1$) to test whether any convex/SoS certificate breaks the $N^{1/4}$ exponent on the upper bound.
   - Explore the **lower-bound side** ($h(N) \ge \sqrt{N} - O_\varepsilon(N^\varepsilon)$): analyze whether non-projective-plane constructions or prime-power refinements can improve upon Bose/Singer + Baker–Harman–Pintz ($O(N^{21/80})$).
2. **Attack 2 (Lean 4 Formal Verification of the New Theorems in `Solution.lean`)**:
   - Formalize & pass `./scripts/verify_gate.sh` (standard axioms only, 0 `sorry`) on:
     1. `Erdos030.fractional_sidon_upper_bound` (generalizing `sidon_sub_094295` to arbitrary $\mu \ge 0$ with $\|\mu\|_2^2$ dependence),
     2. `Erdos030.bose_periodic_fourier_flatness` ($|\widehat{\mathbf{1}_{S_p}}(\xi)|^2 \le p$ for all $1 \le \xi < p^2 - 1$),
     3. `Erdos030.bose_3ap_free_superset_bound` ($|T| \le N^{3/4}$ for any 3-AP-free superset $S_p \cup T$),
     4. `Erdos030.shor_rlt_sdp1_lift` (lifting any feasible fractional Sidon witness $\mu$ into the full Shor + RLT + BQP Degree-1 Lasserre SDP),
     5. Concrete/asymptotic `Erdos030.exact_pointwise_fractional_barrier` & `Erdos030.shor_rlt_sdp1_barrier`.
3. **Strict Anti-Reward-Hacking & Git Hygiene**:
   - NEVER weaken or edit `Statement.lean` (SHA-256 locked).
   - NEVER use `sorry`, custom `axiom`, `unsafe`, `@[implemented_by]`, `@[extern]`, or `native_decide`.
   - NEVER falsely claim `Erdos30Conjecture` is solved unless `verify_gate.sh` passes on `Erdos030.Erdos30Conjecture` itself.
   - Commit results on a dedicated branch (e.g. `research/erdos030-option2`) under author `ProofRush <research@proofrush.invalid>` without leaking personal paths or secrets.
