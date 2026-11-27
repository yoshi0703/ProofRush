# Erdős Problem #30 — Verified Frontier Bounds & Structural Barrier Report

- **Source**: https://www.erdosproblems.com/30 (`$1,000` Erdős–Turán Conjecture, Tier B)
- **Statement SHA-256**: `3b2f86d3ed3e5c57f709a36adbe1ebbaa84252bae4b8b4a0b25333f3d0dba9f8`
- **Overall Conjecture Status (`Erdos30Conjecture`)**: **OPEN** (honestly retained as `in_progress` with all provable obstructions logged in `state/dead_ends.md`; no false claim or statement weakening).

## Lean 4 Formally Verified Theorems (10 Theorems, All Passed `verify_gate.sh`)

All 10 theorems below compiled with **0 `sorry`**, **0 banned bypass primitives**, **0-byte modification to `Statement.lean`**, and **standard axioms only** (`propext`, `Classical.choice`, `Quot.sound`):

| Theorem | Statement | Significance |
| --- | --- | --- |
| `Erdos030.sidon_sub_094295` | $\forall^\infty N,\; h(N) \le \sqrt{N} + 0.94295\,N^{1/4}$ | **Frontier Lean-verified bound** via asymmetric linear kernel $p_i = (2i+1)/48^2$ ($m=48, L=4$, $\sqrt{ab} = 0.94294036\ldots < 0.94295$), strictly sharper than Hou–Zhao (Sep 2026, `0.94349`) and Carter–O'Bryant–Tao (Oct 2026, `0.94304`), within $1.31 \times 10^{-4}$ of the exact smoothing limit $2\sqrt{2}/3 \approx 0.942809$ |
| `Erdos030.asymmetric_kernel_transfer` | General discrete asymmetric one-sided kernel–boundary transfer theorem | Reusable Lean 4 formalization removing the right boundary ($b_R = 0$) and kernel symmetry restriction |
| `Erdos030.sidon_sub_0949` | $\forall^\infty N,\; h(N) \le \sqrt{N} + 0.949\,N^{1/4}$ | Pure Lean-kernel certified 16-bin symmetric rational kernel ($\sqrt{ab} = 0.9486568\ldots < 0.949$) |
| `Erdos030.kernel_transfer_single` | General discrete symmetric kernel–boundary smoothing transfer theorem | Reusable Lean 4 formalization of the discrete $L^2$ symmetric smoothing framework |
| `Erdos030.carter_hunter_obryant_theorem` | $\exists C,\; \forall^\infty N,\; h(N) \le \sqrt{N} + 0.98183\,N^{1/4} + C$ | Closes `erdos_30.variants.carter_hunter_obryant` (`sorry` in `formal-conjectures`) |
| `Erdos030.obryant_theorem` | $\forall^\infty N,\; h(N) \le \sqrt{N} + 0.99703\,N^{1/4}$ | Closes `erdos_30.variants.obryant` (`sorry` in `formal-conjectures`) |
| `Erdos030.balogh_furedi_roy_theorem` | $\forall^\infty N,\; h(N) \le \sqrt{N} + 0.998\,N^{1/4}$ | Closes `erdos_30.variants.balogh_furedi_roy` (`sorry` in `formal-conjectures`) |
| `Erdos030.lindstrom_theorem` | $\forall N \in \mathbb{N},\; h(N) \le \sqrt{N} + N^{1/4} + 1$ | Closes `erdos_30.variants.lindstrom` (`sorry` in `formal-conjectures`) |
| `Erdos030.erdos_turan_theorem` | $\exists C,\; \forall^\infty N,\; h(N) \le \sqrt{N} + C N^{1/4}$ | Closes `erdos_30.variants.erdos_turan` (`sorry` in `formal-conjectures`) |
| `Erdos030.bose_lower_bound_theorem` | $\forall p$ prime, $p \le h(p^2 - 1)$ | Formalized Bose (1942) finite-field Sidon construction in $\mathbb{F}_{p^2}^\times$ |

## Structural Barriers Blocking Full Resolution of `Erdos30Conjecture`

See [`BARRIER_THEOREM.md`](./BARRIER_THEOREM.md) and [`fractional_barrier_experiment.py`](./fractional_barrier_experiment.py) for the complete analysis and reproducible numerical verification:

1. **Exact Pointwise Fractional Sidon Barrier (New Structural Result)**:
   Even keeping **all $N-1$ unsmoothed pointwise inequalities** $\sum_x \mu_x \mu_{x+d} \le 1$ ($1 \le d < N$) with $\mu \in [0, 1]^N$, the **Cauchy High-Pass Sidon Hybrid** construction proves $M(N) \ge \sqrt{N} + \Omega(N^{1/4})$:
   - Analytically / closed-form verified up to $p = 1009$ ($N = 1{,}018{,}081$): $M(N) \ge \sqrt{N} + 0.1393\,N^{1/4}$ (zero clipping, exact FFT check over all $1 \le d < N$).
   - Direct FFT L-BFGS-B optimization at $p = 251$ ($N = 63{,}001$): $M(63{,}001) \ge 260.660 = \sqrt{N} + 0.6097\,N^{1/4}$.
   - **Implication**: No upper-bound method relying solely on pairwise autocorrelation $r_{A-A}(d) \le 1$ and $[0,1]^N$ box constraints (even nonconvex & unsmoothed) can break the $N^{1/4}$ exponent; any proof of $h(N) \le \sqrt{N} + o(N^{1/4})$ must genuinely exploit $\{0,1\}$-integrality ($\|\mu\|_2^2 = \|\mu\|_1$) or higher-order ($k \ge 3$) structure.
2. **Smoothing Barrier ($2\sqrt{2}/3 \approx 0.942809$)**:
   Linear/convex $L^2$ smoothing hits an exact infimum at $2\sqrt{2}/3 \approx 0.942809$ (realized asymptotically by the linear kernel $\rho(x) = 2x$, which our `sidon_sub_094295` approaches within $1.31 \times 10^{-4}$), and Carter–O'Bryant–Tao (Oct 2026, arXiv:2610.36207) prove every WT-triple satisfies $\sqrt{\alpha\beta} > 1/\sqrt{2} \approx 0.7071$.
3. **Lower-Bound Prime-Gap / RH Barrier**:
   `Erdos30Conjecture` requires the two-sided bound $|h(N) - \sqrt{N}| = O_\varepsilon(N^\varepsilon)$. All known dense Sidon constructions (Singer 1938, Bose 1942) depend on prime powers $q \le \sqrt{N}$, leaving a prime-gap deficit $O(N^{21/80})$ unconditionally (Baker–Harman–Pintz) and $O(N^{1/4}\log N)$ even assuming the Riemann Hypothesis.

## Reproducible Artifacts

- [`certificate_asym_m48_L4.py`](./certificate_asym_m48_L4.py) — Exact `fractions.Fraction` verification of the $m=48, L=4$ asymmetric certificate ($\sqrt{ab} = 0.94294036\ldots < 0.94295$).
- [`certificate_m16_L2.py`](./certificate_m16_L2.py) — Exact `fractions.Fraction` verification of the $m=16, L=2$ symmetric certificate ($\sqrt{ab} = 0.9486568\ldots < 0.949$).
- [`BARRIER_THEOREM.md`](./BARRIER_THEOREM.md) & [`fractional_barrier_experiment.py`](./fractional_barrier_experiment.py) — Cauchy High-Pass Sidon Hybrid barrier analysis and FFT verification up to $N = 1{,}018{,}081$.
- [`verification_log.txt`](./verification_log.txt) — Exact `./scripts/verify_gate.sh` outputs for all 10 Lean 4 theorems.
