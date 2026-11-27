# Erdős Problem #30 — Verified Frontier Bounds & Complete Relaxation-Hierarchy Barrier Report

- **Source**: https://www.erdosproblems.com/30 (`$1,000` Erdős–Turán Conjecture, Tier B)
- **Statement SHA-256**: `3b2f86d3ed3e5c57f709a36adbe1ebbaa84252bae4b8b4a0b25333f3d0dba9f8`
- **Overall Conjecture Status (`Erdos30Conjecture`)**: **OPEN** (honestly retained as `in_progress` with all provable obstructions logged in `state/dead_ends.md`; zero false claim or statement weakening).

## Lean 4 Formally Verified Theorems (49 Results, All Passed Kernel Audit)

All **49 theorems/lemmas** across `Formal/Problems/Erdos030/` compiled with **0 `sorry`**, **0 banned bypass primitives**, **0-byte modification to `Statement.lean`**, and **standard axioms only** (`propext`, `Classical.choice`, `Quot.sound`) — exact kernel logs in [`verification_log.txt`](./verification_log.txt):

### Part I: Frontier Asymptotic Bounds & Classical Milestones (10 Results — `Solution.lean` Sections 1–7)

| Theorem | Statement | Significance |
| --- | --- | --- |
| `Erdos030.sidon_sub_094295` | $\forall^\infty N,\; h(N) \le \sqrt{N} + 0.94295\,N^{1/4}$ | **Frontier Lean-verified bound** ($m=48, L=4$ asymmetric linear kernel, $\sqrt{ab} = 0.94294036\ldots$), sharper than Hou–Zhao (Sep 2026, `0.94349`) and Carter–O'Bryant–Tao (Oct 2026, `0.94304`), within $1.31\times 10^{-4}$ of $2\sqrt{2}/3$ |
| `Erdos030.asymmetric_kernel_transfer` | General discrete asymmetric one-sided kernel–boundary transfer | Removes right boundary ($b_R=0$) and symmetry restriction |
| `Erdos030.sidon_sub_0949` & `kernel_transfer_single` | $\forall^\infty N,\; h(N) \le \sqrt{N} + 0.949\,N^{1/4}$ & symmetric transfer | 16-bin pure Lean-kernel certified symmetric certificate |
| `Erdos030.carter_hunter_obryant_theorem`, `obryant_theorem`, `balogh_furedi_roy_theorem`, `lindstrom_theorem`, `erdos_turan_theorem` | Classical & recent upper bounds ($1, 0.998, 0.99703, 0.98183$) | Closes all 5 `formal-conjectures` Erdős #30 upper-bound variants |
| `Erdos030.bose_lower_bound_theorem` | $\forall p$ prime, $p \le h(p^2 - 1)$ | Formalized Bose (1942) finite-field Sidon construction in $\mathbb{F}_{p^2}^\times$ |

### Part II: Option 2 Convex / Fractional / Bose-Fourier Infrastructure (10 Results — `Solution.lean` Sections 8–9)

- `shor_rlt_sdp1_lift` & `shor_rlt_sdp1_lift_3ap_4sidon_cuts` — Exact lifting of any `IsFractionalSidon` vector $\mu \in [0,1]^N$ into `IsSDP1Feasible` + all BQP + (for $\mu_i \le 1/\sqrt{3}$) all $\Theta(N^2)$ 3-AP & $\Theta(N^3)$ 4-Sidon linear cuts.
- `fractional_energy_upper_bound`, `sdp1_energy_upper_bound`, `fractional_sidon_sub_094295_theta` ($\sqrt{N} + 0.94295\sqrt{\theta}\,N^{1/4}$), `sdp1_sub_094295`, `strict_separation_h6_lt_fractional_sdp1`.
- `bose_modular_difference_set`, `bose_periodic_fourier_flatness` ($|\widehat{\mathbf{1}_{S_p}}(\xi)|^2 \in \{1, p\}$), `bose_3ap_free_superset_bound` ($|T| \le (p^2-1)/\sqrt{p}$).

### Part III: Milestone 1 — Asymptotic Fractional/SDP Barrier & Degree-2 Lasserre Formalization (7 Results — `PeriodicDFT.lean`, `SmoothBumpBarrier.lean`, `Lasserre2.lean`)

- `asymptotic_fractional_sdp1_barrier_explicit` & `asymptotic_fractional_sdp1_barrier`: **Full asymptotic Lean 4 proof** (elementary smooth-bump Periodic Bose + Poisson, zero Weil sums) that for every prime $p \ge 10{,}000$ ($M = p^2-1$), there exist $(\mu, X)$ feasible for `IsFractionalSidon`, `IsSDP1Feasible`, all BQP + 3-AP + 4-Sidon linear cuts with $\sum \mu \ge p + \frac{1}{250}\sqrt{p} > \sqrt{M} + \frac{1}{250} M^{1/4}$.
- `exists_lasserre2_achieving_h`, `h_le_of_lasserre2_bound`, `lasserre2_implies_sdp1_with_cuts`, `lasserre2_dual_sos_bound`, `lasserre2_sub_094295`: Complete Degree-2 Lasserre / 4-tuple Sidon ideal formalization, exact soundness, projection to `SDP_1+`, and dual SoS certificate soundness.

### Part IV: Milestone 2 — General $k=3$ ($M_{\text{3AP}}$), Mod-$q$ Collapse & Binary-Autocorrelation Rigidity (15 Results — `Track2EquidistAndM3AP.lean`, `Universal3APBound.lean`, `Track3BoseVariance.lean`)

- `h_11_eq_4` & `strict_separation_h11_lt_m3ap`: Strict nonlinear $M_{\text{3AP}}$ separation $h(11) = 4 < 3\sqrt{2} \le M_{\text{3AP}}(11)$.
- `fractional_sidon_mod_q_equidistribution`, `sdp1_mod_q_equidistribution`, `fractional_sidon_mod_q_support_collapse`, `sdp1_mod_q_support_collapse`: Exact mod-$q$ equidistribution collapsing all Behrend and Stanley base-3 supports to $o(\sqrt{N})$.
- `universal_3ap_free_superset_from_U`, `universal_3ap_free_superset_bound`, `m3ap_dense_support_card_bound`: Universal power-saving bound $|T| \le 66\,N^{11/12}$ for EVERY 3-AP-free superset of any dense Sidon set or dense $M_{\text{3AP}}(N)$ witness.
- `bose_sparse_background_cross_variance`: Exact Parseval cross-variance obstruction $\ge \frac{p(p-2)}{p-1}(\|\nu\|_2^2 - 2)$ on Bose's set.
- `h_3_eq_2`, `binary_autocorr_counterexample_N3`, `binary_autocorr_endpoint_rigidity`, `binary_autocorr_outermost_shell_rigidity`, `binary_autocorr_sidon_support_integral`: Complete binary-autocorrelation rigidity structure theorem and $N=3$ counterexample $\mu = (1, 1/2, 1)$.

### Part V: Milestone 3 — Degree-2 Lasserre Separation & Elementary All-$N$ Smooth Fejér `SDP_1+` Barrier (7 Results — `Lasserre2SeparationsAndFejer.lean`)

- `h_6_eq_3`, `lasserre2_bound_3_plus_4_P4`, `lasserre2_le_3_of_h_le_3`, `lasserre2_6_le_3`, `strict_separation_lasserre2_6_lt_fractional_sdp1`: Closed-form 2-square Boolean SoS identity proving $\mathrm{Lasserre}_2(6) = h(6) = 3 < 7/2 \le M(6) \le \mathrm{SDP}_1(6)$.
- `smooth_fejer_sdp1_barrier_all_N` & `smooth_fejer_sdp1_barrier_half`: **Elementary all-$N$ barrier** (zero primes, zero Bose, zero Fourier) proving $\mathrm{SDP}_1^+(N) > \sqrt{N} + \frac{2}{5} N^{1/4}$ for ALL $N \ge 81$, and $\ge \sqrt{N} + (\frac{1}{2} - \varepsilon) N^{1/4}$ for every $\varepsilon > 0$ and all sufficiently large $N$.

## Reproducible Artifacts & Cloud Notebook

- [`BARRIER_THEOREM.md`](./BARRIER_THEOREM.md) — Complete L0 → L1 → L1+ → L1-Bin → L1.5 → L2 → L2+NN hierarchy analysis & certified Degree-2 Lasserre scaling (`N=6..56`).
- [`certificate_asym_m48_L4.py`](./certificate_asym_m48_L4.py) & [`certificate_m16_L2.py`](./certificate_m16_L2.py) — Exact `fractions.Fraction` verifications of the Lean 4 rational certificates.
- [`fractional_barrier_experiment.py`](./fractional_barrier_experiment.py) & [`option2_hierarchy_experiments.py`](./option2_hierarchy_experiments.py) — Cauchy High-Pass hybrid, Periodic Bose+Poisson, and Clarabel `SDP_1` vs Degree-2 Lasserre experiments.
- [`../../colab/Erdos030_Deep_Attack.ipynb`](../../colab/Erdos030_Deep_Attack.ipynb) — Google Colab High-RAM CPU reproduction notebook.
- [`verification_log.txt`](./verification_log.txt) — Exact kernel `#print axioms` verification outputs for all 49 Lean 4 results.
