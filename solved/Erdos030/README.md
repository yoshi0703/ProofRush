# Erdős Problem #30 — Verified Frontier Bounds & Structural Barrier Report

- **Source**: https://www.erdosproblems.com/30 (`$1,000` Erdős–Turán Conjecture, Tier B)
- **Statement SHA-256**: `3b2f86d3ed3e5c57f709a36adbe1ebbaa84252bae4b8b4a0b25333f3d0dba9f8`
- **Overall Conjecture Status (`Erdos30Conjecture`)**: **OPEN** (honestly retained as `in_progress` with all provable obstructions logged in `state/dead_ends.md`; no false claim or statement weakening).

## Lean 4 Formally Verified Theorems (20 Results, All Passed `verify_gate.sh`)

All 20 theorems/lemmas below compiled with **0 `sorry`**, **0 banned bypass primitives**, **0-byte modification to `Statement.lean`**, and **standard axioms only** (`propext`, `Classical.choice`, `Quot.sound`):

### Part I: Frontier Asymptotic Bounds & Classical Milestones (10 Theorems)

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

### Part II: Option 2 Convex / Fractional / Higher-Order Barrier Theorems (10 Results)

| Theorem / Lemma | Statement | Significance |
| --- | --- | --- |
| `Erdos030.shor_rlt_sdp1_lift` | Every `IsFractionalSidon N μ` lifts via $X = \mu\mu^T + \mathrm{diag}(\mu(1-\mu))$ into `IsSDP1Feasible N μ X` + all BQP triangle inequalities | Proves full Degree-1 Lasserre / Shor + RLT + BQP SDP satisfies $\mathrm{SDP}_1(N) \ge M(N)$ |
| `Erdos030.shor_rlt_sdp1_lift_3ap_4sidon_cuts` | Under $\mu_i \le 1/\sqrt{3}$, the lifted $X$ ALSO satisfies all $\Theta(N^2)$ exact 3-AP cuts and all $\Theta(N^3)$ exact 4-Sidon cuts | Proves adding ALL 3-AP & 4-Sidon linear cuts to `SDP_1(N)` still fails to break the $N^{1/4}$ barrier |
| `Erdos030.fractional_sidon_sub_094295_theta` | $\forall \theta \in (0, 1],\; \forall^\infty N,\; M_\theta(N) \le \sqrt{N} + 0.94295\sqrt{\theta}\,N^{1/4}$ | Exact $\theta$-integrality upper envelope ($\|\mu\|_2^2 \le \theta\|\mu\|_1$) |
| `Erdos030.sdp1_sub_094295` | $\forall^\infty N,\; \mathrm{SDP}_1(N) \le \sqrt{N} + 0.94295\,N^{1/4}$ | Matching upper bound for the full Degree-1 Lasserre / Shor + RLT SDP |
| `Erdos030.fractional_energy_upper_bound` | Discrete smoothed energy bound for arbitrary `IsFractionalSidon N μ` | Core energy transfer lemma connecting pointwise fractional autocorrelation to asymmetric kernels |
| `Erdos030.sdp1_energy_upper_bound` | Discrete smoothed energy bound for arbitrary `IsSDP1Feasible N x X` | Core energy transfer lemma for matrix moment relaxations `SDP_1(N)` |
| `Erdos030.strict_separation_h6_lt_fractional_sdp1` | $(h(6) : \mathbb{R}) < 16/5 = \sum \mu_i$ for a joint witness of `IsFractionalSidon 6` and `IsSDP1Feasible 6` | Machine-checked strict separation $h(6) \le 3 < 3.2 \le M(6) \le \mathrm{SDP}_1(6)$ |
| `Erdos030.bose_modular_difference_set` | Exact modular difference multiplicity $r^{\text{mod}}_{S_p - S_p}(d) \in \{0, 1, p\}$ on $\mathbb{Z}/(p^2 - 1)\mathbb{Z}$ | Exact relative difference-set theorem for Bose's Sidon set $S_p$ |
| `Erdos030.bose_periodic_fourier_flatness` | $\forall 1 \le \xi < p^2 - 1,\; \|\widehat{\mathbf{1}_{S_p}}(\xi)\|^2 = 1$ if $(p-1)\mid\xi$, else $p$ | Exact Fourier spectrum flatness of Bose's Sidon set powering the periodic barrier & 3-AP analysis |
| `Erdos030.bose_3ap_free_superset_bound` | Any $T \subseteq \{0,\dots,p^2-2\}$ with no modular 3-AP $t_1 + t_2 \equiv 2a$ ($a \in S_p$) has $|T| \le (p^2-1)/\sqrt{p}$ | First formal $k=3$ (3-AP-free) superset obstruction on Bose's set, explaining why nonlinear $T_3(\mu)=0$ collapses excess |

## Complete Relaxation Hierarchy & Structural Barriers

See [`BARRIER_THEOREM.md`](./BARRIER_THEOREM.md), [`fractional_barrier_experiment.py`](./fractional_barrier_experiment.py), and [`option2_hierarchy_experiments.py`](./option2_hierarchy_experiments.py):

1. **L0 (Positive / Toeplitz $L^2$ Smoothing)**: Exact infimum $2\sqrt{2}/3 \approx 0.942809\,N^{1/4}$ (approached within $1.31\times 10^{-4}$ by `sidon_sub_094295`); signed/infinite-support PSD Toeplitz kernels do not beat $2\sqrt{2}/3$.
2. **L1 (Exact Pointwise Fractional $M(N)$)**: $\sqrt{N} + \Omega(N^{1/4}) \le M(N) \le \sqrt{N} + 0.94295\,N^{1/4}$.
   - Closed-form Cauchy hybrid (`fractional_barrier_experiment.py`): $+0.1393\,N^{1/4}$ at $N = 1{,}018{,}081$ (zero clipping); FFT L-BFGS-B reaches $+0.6097\,N^{1/4}$ at $N = 63{,}001$.
   - Periodic Bose + Poisson construction (`option2_hierarchy_experiments.py`): zero clipping & zero rescaling (`raw_max_ac = 0.99694 < 1.0`, `+0.0825 M^(1/4)` at $M = 1{,}018{,}080$).
   - $\theta$-Integrality phase transition: $M_\theta(N) - \sqrt{N} \asymp \min(0.61\,N^{1/4},\; 0.23(1-\theta)\sqrt{N})$, requiring fractionality defect $\|\mu\|_1 - \|\mu\|_2^2 = o(N^{1/4})$ to escape.
3. **L1+ (Full Degree-1 Lasserre / Shor + RLT + BQP + ALL 3-AP & 4-Sidon Linear Cuts)**: Provably trapped at $\Theta(N^{1/4})$ by `shor_rlt_sdp1_lift` + `shor_rlt_sdp1_lift_3ap_4sidon_cuts`; Clarabel SDP confirms `0.0000` tightening from all 3-AP cuts on $N \in \{15, 20, 26, 35, 45\}$.
4. **L1.5 (Exact Nonlinear 3-AP-Free $T_3(\mu) = 0$)**: `bose_3ap_free_superset_bound` proves $|T| \le (p^2-1)/\sqrt{p} < N^{3/4}$; nonlinear $T_3(\mu)=0$ empirically collapses fractional excess on Bose supersets from $+0.48\,N^{1/4}$ to `0.0000`.
5. **L2 (Degree-2 Lasserre / 4-Tuple Sidon Ideal)**: First convex hierarchy level escaping the L1/L1+ barrier — exact `4.00000` at $N=8$ ($h(8)=4$), slashing the $N=15$ integrality gap by **64%** (`5.6551 → 5.2373` vs $h(15)=5$).
6. **Lower-Bound Prime-Gap / RH Barrier**: All known dense constructions (Singer 1938, Bose 1942) depend on prime powers $q \le \sqrt{N}$, leaving $O(N^{21/80})$ unconditionally (Baker–Harman–Pintz) and $O(N^{1/4}\log N)$ even under the Riemann Hypothesis.

## Reproducible Artifacts & Cloud Notebook

- [`certificate_asym_m48_L4.py`](./certificate_asym_m48_L4.py) — Exact `fractions.Fraction` verification of the $m=48, L=4$ asymmetric certificate ($\sqrt{ab} = 0.94294036\ldots < 0.94295$).
- [`certificate_m16_L2.py`](./certificate_m16_L2.py) — Exact `fractions.Fraction` verification of the $m=16, L=2$ symmetric certificate ($\sqrt{ab} = 0.9486568\ldots < 0.949$).
- [`BARRIER_THEOREM.md`](./BARRIER_THEOREM.md), [`fractional_barrier_experiment.py`](./fractional_barrier_experiment.py), and [`option2_hierarchy_experiments.py`](./option2_hierarchy_experiments.py) — Complete relaxation hierarchy analysis, Periodic Bose+Poisson verification, and exact Clarabel SDP_1 vs Degree-2 Lasserre experiments.
- [`../../colab/Erdos030_Deep_Attack.ipynb`](../../colab/Erdos030_Deep_Attack.ipynb) — Ready-to-run Google Colab High-RAM CPU notebook for cloud reproduction and larger-$N$ Degree-2 Lasserre scaling.
- [`verification_log.txt`](./verification_log.txt) — Exact `./scripts/verify_gate.sh` outputs for all 20 Lean 4 results.
