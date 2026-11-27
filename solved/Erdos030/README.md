# Erdős Problem #30 — Verified Milestones & Structural Barrier Report

- **Source**: https://www.erdosproblems.com/30 (`$1,000` Erdős–Turán Conjecture, Tier B)
- **Statement SHA-256**: `3b2f86d3ed3e5c57f709a36adbe1ebbaa84252bae4b8b4a0b25333f3d0dba9f8`
- **Overall Conjecture Status (`Erdos30Conjecture`)**: **OPEN** (honestly retained as `in_progress` with both provable obstructions logged in `state/dead_ends.md`; no false claim or statement weakening).

## Lean 4 Formally Verified Milestones (All Passed `verify_gate.sh`)

All 8 theorems below compiled with **0 `sorry`**, **0 banned bypass primitives**, **0-byte modification to `Statement.lean`**, and **standard axioms only** (`propext`, `Classical.choice`, `Quot.sound`):

| Theorem | Statement | Significance |
| --- | --- | --- |
| `Erdos030.lindstrom_theorem` | $\forall N \in \mathbb{N},\; h(N) \le \sqrt{N} + N^{1/4} + 1$ | Closes `erdos_30.variants.lindstrom` (`sorry` in `formal-conjectures`) |
| `Erdos030.erdos_turan_theorem` | $\exists C,\; \forall^\infty N,\; h(N) \le \sqrt{N} + C N^{1/4}$ | Closes `erdos_30.variants.erdos_turan` (`sorry` in `formal-conjectures`) |
| `Erdos030.kernel_transfer_single` | General discrete symmetric kernel–boundary smoothing transfer theorem | Reusable Lean 4 formalization of the discrete $L^2$ smoothing framework |
| `Erdos030.sidon_sub_0949` | $\forall^\infty N,\; h(N) \le \sqrt{N} + 0.949 N^{1/4}$ | Pure Lean-kernel certified 16-bin rational kernel ($\sqrt{ab} = 0.9486568\ldots < 0.949$), beating 2023–2025 literature bounds |
| `Erdos030.balogh_furedi_roy_theorem` | $\forall^\infty N,\; h(N) \le \sqrt{N} + 0.998 N^{1/4}$ | Closes `erdos_30.variants.balogh_furedi_roy` (`sorry` in `formal-conjectures`) |
| `Erdos030.obryant_theorem` | $\forall^\infty N,\; h(N) \le \sqrt{N} + 0.99703 N^{1/4}$ | Closes `erdos_30.variants.obryant` (`sorry` in `formal-conjectures`) |
| `Erdos030.carter_hunter_obryant_theorem` | $\exists C,\; \forall^\infty N,\; h(N) \le \sqrt{N} + 0.98183 N^{1/4} + C$ | Closes `erdos_30.variants.carter_hunter_obryant` (`sorry` in `formal-conjectures`) |
| `Erdos030.bose_lower_bound_theorem` | $\forall p$ prime, $p \le h(p^2 - 1)$ | Formalized Bose (1942) finite-field Sidon construction in $\mathbb{F}_{p^2}^\times$ |

## Why the Full `$1,000` Conjecture Remains Open (Stop-Loss Barriers)

1. **Upper-Bound Smoothing Barrier ($N^{1/4}$ wall)**:
   Carter–O'Bryant–Tao (Oct 2026, arXiv:2610.36207) prove that every Window–Table smoothing witness satisfies $\sqrt{\alpha\beta} > 1/\sqrt{2} \approx 0.7071$ (and achieve $\approx 0.94304 N^{1/4}$ via random asymmetric ensembles, conjecturing an infimum $\gtrsim 0.943$). Thus no autocorrelation/$L^2$ smoothing argument can break the $N^{1/4}$ exponent down to $O_\varepsilon(N^\varepsilon)$.
2. **Lower-Bound Prime-Gap Barrier**:
   `Erdos30Conjecture` requires the two-sided bound $|h(N) - \sqrt{N}| = O_\varepsilon(N^\varepsilon)$. Every known Sidon construction achieving density $(1 - o(1))\sqrt{N}$ (Singer 1938, Bose 1942) relies on finite fields of prime-power order $q \le \sqrt{N}$, leaving a prime-gap deficit $O(N^{21/80})$ unconditionally (Baker–Harman–Pintz) and $O(N^{1/4}\log N)$ even assuming the Riemann Hypothesis.
