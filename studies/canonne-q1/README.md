# Instance-optimal identity testing at the specified total variation distance

Clément Canonne's first open question at COLT 2024 asks for the number of independent observations needed to test equality to a known discrete distribution. The answer may depend on the reference law and the specified distance, and the paper asks for accuracy up to universal multiplicative constants. [Original question and prize, §5](https://proceedings.mlr.press/v247/canonne24a/canonne24a.pdf#page=4)

Let $N_q(e)$ be the least number of draws from an unknown distribution $p$ that suffice to distinguish $p=q$ from every $p$ with total variation distance strictly greater than $e$. Each error probability must be at most one third. Our theorem gives a functional $\Phi(q,e)$ and positive universal constants $L,U$ such that

$$
\Phi(q,e)\le L N_q(e),\qquad N_q(e)\le U\Phi(q,e).
$$

Both bounds hold at the given $e$, including $e=1$ and instances with an empty alternative. They cover all finite reference laws, including zero-mass labels on the declared alphabet, and laws on a countably infinite alphabet. For finite rational input, an equivalent formula can be evaluated in polynomial bit time even when equal probabilities are listed together with binary multiplicities. This gives a proposed resolution of Question 1. External human review and the original author's prize decision are pending. [English paper](paper/paper.pdf) · [Main Lean theorem](lean/QuestionOne.lean) · [Rational evaluator](experiments/closed_rate.py)

## How the functional works

Order the reference probabilities. Keep the smallest number of largest atoms whose complement has mass at most $e$. If this complement has mass $w$, a distribution is a strict alternative exactly when its deficit on the retained atoms exceeds $e-w$ plus its overlap with the reference on the complement. This identity couples the two parts of the distribution at the specified distance.

A weighted statistic tests discrepancies among the retained atoms. A split-sample score and a collision statistic pool observations across the remaining probabilities. For the lower bound, we construct a randomized observation channel with shared pilot lists under the two hypotheses. This measures how much tail overlap a difficult alternative can retain while evading detection. A deterministic comparison then tightens the upper and lower bounds by increasing the sample count. Near the maximum distance a separate clipped moment determines the answer. As one consequence, for one atom of mass $1-w$ and $k$ equal atoms of total mass $w$, the answer at $e=w$ is of order $k^{2/5}/w$, uniformly for $0<w\le1/2$ and $k\ge2$. [Definitions and proofs](paper/paper.tex) · [Finite theorem](lean/FiniteResolution.lean) · [Countable theorem](lean/CountableResolution.lean)

## What was verified

Lean proves the statistical theorem against all randomized tests on ordered independent observations. It also proves equality between the finite profile and a bounded list of radical comparisons on explicitly enumerated rational input. The manuscript gives the bit-complexity proof for a rounded formula, implemented in Python, and the eventual agreement of the direct countable formula with the finite projections. Randomized examples and exact two-label calculations separately check the evaluator. [Bounded comparisons](lean/SuccinctBound.lean) · [Kernel receipt and source hashes](verification/kernel.json) · [Implementation checks](verification/computational-check.txt) · [Exact two-label results](verification/bernoulli.json)

Research was directed by Yoshiaki Otsuka. Codex agents developed and checked the proofs, wrote the Lean and Python code, and prepared the manuscript. The finite and countably infinite statistical conclusions first passed independent kernel verification together at 03:36 UTC on 27 November 2026. Research dates, models, attribution, computational resources and the priority search are recorded separately. [Research log](RESEARCH.md) · [Statement review](verification/statement-review.md) · [Priority review](verification/priority-review.md) · [How to cite](CITATION.cff)

## Reproduce the result

From the repository root, run the statistical checks using Python 3.11 or later. The example describes 17 labels, with the last 16 each having probability $1/64$. The returned integer estimates the optimal sample count within universal factors.

```sh
python3 -B studies/canonne-q1/experiments/closed_rate.py studies/canonne-q1/experiments/example.json
python3 -B studies/canonne-q1/experiments/check_closed_rate.py
python3 -B studies/canonne-q1/experiments/check_bernoulli.py
```

To check the proof from source with Bash, Git, Python, and Elan, run the following commands from the root. The independent checker shipped with Lean is used by default. To pin the Rust checker to the source build used in our receipt, follow the repository's Rust build instructions and pass its binary using `--nanoda /path/to/nanoda_bin`. On Linux, the public workflow additionally runs this binary without network access in a read-only Docker container. [Checker and sandbox instructions](../../lean/README.md) · [Public Linux workflow](../../.github/workflows/verify.yml)

```bash
root="$PWD"
scratch="$(mktemp -d)"
elan toolchain install "$(cat "$root/lean/lean-toolchain")"
git clone --depth 1 --branch v4.36.0 https://github.com/leanprover-community/mathlib4.git "$scratch/mathlib"
(
  cd "$scratch/mathlib"
  modules="$(awk '$1 == "import" && $2 ~ /^Mathlib[.]/ {print $2}' "$root"/studies/canonne-q1/lean/*.lean | sort -u)"
  lake exe cache get $modules
)
python3 -B studies/canonne-q1/verify.py --mathlib "$scratch/mathlib" --run-dir "$scratch/checked"
cat "$scratch/checked/nanoda.txt"
```

The verifier rebuilds the local modules, runs Lean's replay, exports the proof terms, and checks their axiom inventory before invoking the Rust kernel. It records the hashes and the isolation mode in `report.json`. To rebuild the manuscript, run `tectonic paper.tex` in `studies/canonne-q1/paper`. The LaTeX sources include the bibliography. [Verification script](verify.py) · [Project license](../../LICENSE)
