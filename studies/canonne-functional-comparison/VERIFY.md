# Reproducing Canonne's functional comparison

Canonne's equation (4) asks for bounds between a truncated quasinorm and the inverse level of a Peetre functional. The original post fixes the radii, the entire retained boundary atom, the removal of the largest entry, and the level of inversion. The COLT paper uses twice the radius in its BCG normalization. The proof and the formal model use the 2019 convention throughout. [Original equation and definitions](https://mathoverflow.net/questions/332062/) · [COLT question 2](https://proceedings.mlr.press/v247/canonne24a/canonne24a.pdf#page=4) · [English paper](paper.pdf)

## Theorems

| Result | Where to inspect it |
| --- | --- |
| A law is a nonnegative decreasing sequence with sum one. The infimum defining $K$ allows signed $\ell_1+\ell_2$ decompositions. Finite laws embed by padding with zeros. | [Model](lean/Model.lean) |
| A clipped multiple of the probability vector realizes the inverse at each interior level. The level characterizes a unique nonnegative parameter. | [Attainment](lean/Peetre.lean) · [Uniqueness](lean/Level.lean) |
| The chosen cutoff is the least prefix with discarded mass at most the tolerance. The power sum omits exactly the first atom. | [Canonical cutoff](lean/Cutoff.lean) |
| Every sorted law and every $0<s<e<1$ satisfy the two-radius theorem. Substituting the source radii $9e,e,e/32$ gives both sides of equation (4), with constants $1$ and $39/31$. The export also checks the strictly positive parameter convention and the point-mass example from the original discussion. | [Lower estimate](lean/Lower.lean) · [Upper estimate](lean/Upper.lean) · [Canonical theorem and source equation](lean/Source.lean) · [Kernel record](verification/comparison.json) |
| The best universal multiplier of the lower bound is $1$. The smallest nonnegative multiplier of the upper radius-gap term is $1/4$. Both statements quantify over the same canonical cutoff as the source theorem. | [Uniform examples](lean/Uniform.lean) · [Upper sharpness examples](lean/Sharp.lean) · [Canonical constants](lean/Extremal.lean) · [Kernel record](verification/extremal.json) |
| For every fixed $0<e<1$ and every real threshold $A$, some finite law has $e<F(e)<1$ and $D(e)>A$. Thus measuring both quantities at the same tolerance cannot give a universal upper bound even on the class $F(e)<1$. | [Construction](lean/SameRadius.lean) · [Kernel record](verification/extremal.json) |

The paper also proves sharpness and the same-radius obstruction under an arbitrarily small prescribed positive ceiling on the norm of the probability law. Its three-block and split-head proofs give those restrictions. The formally checked extremal statements quantify over unrestricted sorted probability laws. The coefficient $1/4$ belongs to the stronger radius-gap inequality in this work. The number $39/31$ is an explicit sufficient constant in the 2019 display.

## Running the checks

Run the following from the repository root with Python 3.11 or later. The arithmetic check is deterministic, uses standard-library rational arithmetic and tests the discrete cutoff convention. Its output counts the finite laws, exact-boundary cases and the countably infinite example.

~~~sh
python3 -B studies/canonne-functional-comparison/check.py
~~~

Use Lean 4.36.0, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` and nanoda `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`. Build nanoda as described in the repository instructions. Set `MATHLIB_DIR` to the pinned Mathlib checkout and `NANODA_BIN` to the rebuilt Rust executable. The first command fetches the compiled dependencies needed for this particular study. Each verification run uses a fresh output directory. [Tool installation](../../lean/README.md) · [Linux workflow](../../.github/workflows/verify.yml)

~~~bash
proof_dir="$PWD/studies/canonne-functional-comparison"
modules=$(awk '$1 == "import" && $2 ~ /^Mathlib[.]/ {print $2}' "$proof_dir"/lean/*.lean | sort -u)
(cd "$MATHLIB_DIR" && lake exe cache get $modules)
evidence=$(mktemp -d)
for bundle in comparison extremal; do
  python3 "$proof_dir/verify.py" --bundle "$bundle" --mathlib "$MATHLIB_DIR" \
    --nanoda "$NANODA_BIN" --run-dir "$evidence/$bundle"
done
~~~

The runner rebuilds each module with warnings treated as errors, checks it with `leanchecker`, exports the named theorems and their dependencies, audits the axiom inventory, and passes the export to nanoda. It accepts only `propext`, `Quot.sound`, and `Classical.choice`. The local Rust runs disabled networking and excluded the source and Mathlib directories. The Linux workflow runs the separately rebuilt checker in a read-only container without network access. The local comparison export contains 19,298 declarations and the local extremal export contains 19,622. They share dependencies. Two optional bundles reproduce the individual [upper sharpness](verification/sharpness.json) and [uniform lower sharpness](verification/uniform.json) checks with `--bundle sharpness` and `--bundle uniform`.

Build the paper from this study directory with `tectonic paper.tex`. The source includes a small licensed font subset for the director's name. [TeX source](paper.tex) · [Research and priority search](RESEARCH.md) · [Independent mathematical review](independent-review.md)
