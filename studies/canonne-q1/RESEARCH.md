# Research record

On 27 November 2026 Yoshiaki Otsuka directed ProofRush to prioritize Canonne's first COLT 2024 open problem. He requested concurrent work on a statistic that pools multiple probability groups, adaptive allocation of observations, and different lower-bound constructions. He required the original statistical experiment and the original distance, an unconditional proof, a separate formal check, and an honest account of priority. He authorized publication of a complete result and submission to the prize sponsor. [Original problem](https://proceedings.mlr.press/v247/canonne24a/canonne24a.pdf#page=4)

## How the proof changed

Earlier work in this project gave bounds for a fixed number of diffuse bins and for worst-case reference distributions. Their constants or their optimization over the reference left the instance question open. Bucketing rare probabilities and testing each group separately introduces losses. A count of all draws from the tail also misses transfers between labels with the same total tail mass. These observations motivated retaining both the tail's mass and its overlap with the alternative. [Earlier project](../exact-radius-identity/README.md) · [Testing construction](paper/paper-upper.tex)

The upper-bound investigation pooled a clipped linear score and coincidences between two independent batches. The head uses a weighted quadratic statistic, with a separate count for head versus tail. We considered allocating observations after learning which probabilities carry the change. A group selected adaptively cannot be sampled on demand in the specified i.i.d. model. The proof uses predetermined batches of ordinary draws. It achieves uniform bounds with this allocation.

For the lower bound we tried to transfer hard conditional-head instances into the full experiment while changing which tail labels are visible. The successful reduction uses the same randomized channel under both inputs. An empirical distribution on pilot labels gives the observation law, and estimates of its collisions and overlap control the two errors in the reduction. Signed perturbations of the head and a separate head-versus-tail perturbation give necessary conditions for every successful test. A clipped moment handles the range near distance one. The final comparison is deterministic. Multiplying the sample count converts the necessary crossing into the sufficient crossing at the same distance. [Pilot construction](paper/paper-pilots.tex) · [Lower bound](paper/paper-headlower.tex) · [Dilation lemma](paper/paper.tex)

Coarsening a countably infinite alphabet raises two further issues. A test must work simultaneously against all the alternatives, and merging a tail can hide a deficit. A lifting channel, compactness of the space of tests, and pointwise convergence of expectations give an exact equivalence at each fixed integer budget. This yields the uniform countable theorem. A separate argument in the manuscript derives the eventually stable direct formula. [Countable proof](paper/paper-countable.tex) · [Formal projection equivalence](lean/CountableBridge.lean)

## Evidence and chronology

All times below are UTC on 27 November 2026.

| Time | Recorded event |
| --- | --- |
| 02:06:27 | Start of the question-specific accounting interval following the research direction. Earlier work on the surrounding problems is described separately. |
| 03:30:12 | A new-source build and an isolated Rust kernel accepted the finite-domain proof. |
| 03:36:54 | The same checks passed with the countable theorem and the tail radical formula, comprising 23,933 declarations. |
| 03:47:39 | The release build checked five targets, including the bounded finite evaluation, across 80 local modules. The Rust kernel accepted 23,975 declarations. |

The release receipt records Lean 4.36.0, the exact Mathlib revision, the source digest of each module, the export digest, the checker digest, and the use of macOS Seatbelt. The only exported axioms were propositional extensionality, quotient soundness, and classical choice. The Linux workflow builds the independent checker from its pinned Rust source. [Release receipt](verification/kernel.json) · [Workflow](../../.github/workflows/verify.yml)

The arithmetic implementation passed 1,500 randomized rational comparisons and 75 exponent checks. Two subprocess regressions exercise integer input and output beyond Python's default decimal-conversion limit. Runs also exercised equal-mass multiplicities up to $2^{1000}$. A separate reviewer compared 5,538 cases with an independent scan. For 34 one-sided Bernoulli instances an exact randomized Neyman–Pearson calculation determined the true minimum budget. The ratio of the rounded formula to this minimum ranged from $16/17$ to $8$ on these examples. The theorem derives its uniform constants independently of these computations. [Reproducible checks](experiments/check_closed_rate.py) · [Bernoulli calculation](experiments/check_bernoulli.py) · [Adversarial review](verification/statement-review.md)

## Models, resources and review

Yoshiaki Otsuka selected and prioritized the question and specified the research and release criteria. The lead Codex agent, GPT-6.2 Astra at maximum reasoning effort, integrated the statistical construction, formal proof, manuscript and replay. Three GPT-6.2 Sol agents, one at medium effort and two at high effort, worked on the upper test and arithmetic evaluation, the pilot channel and countable lifting, and the head bounds and finite evaluation. Separate GPT-6.2 Astra and GPT-6.2 Sol agents, both at high effort, reviewed statement fidelity and mathematical edge cases, and the prior literature and prize conditions, respectively. The mathematical review led to fixes in the CLI's integer handling and in the manuscript's references. [Statement review](verification/statement-review.md) · [Literature review](verification/priority-review.md)

Local computation used an Apple M3 Pro with 11 CPU cores and 18 GiB of memory. Model inference used the existing Codex subscription with no additional paid model API. The recorded model counters include repeated cached input. A counter increase is an observable accounting event, and an exact billable call count and task-specific monetary cost were unavailable. The first 90 minutes and 32 seconds have a saved snapshot with 1,161 counter increases, 263,323,870 total tokens, 260,664,192 cached input tokens and 727,072 output tokens. The versioned release also records usage up to publication. [Accounting methodology and per-role snapshot](verification/usage.json) · [Versioned release](https://github.com/yoshi0703/ProofRush/releases/tag/canonne-q1-v1.0.0)

The priority search includes the original papers, work on separation radii, the 2026 Zipfian special case, and recent AI research indexes. We found no publicly inspectable earlier theorem covering all nulls at the specified distance. One gated research dataset lists runs on this exact question. Its public index gives no question-specific result. External human review and prize adjudication remain pending. [Priority review and sources](verification/priority-review.md)
