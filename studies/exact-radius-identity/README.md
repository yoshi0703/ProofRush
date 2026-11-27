# Identity testing at the specified total variation distance

The two preprints use the ordinary distance equal to half the sum of absolute probability differences. Fix an explicitly known law on a finite alphabet and draw independent observations from an unknown law. The papers ask how many observations distinguish equality from separation at a prescribed distance.

| Preprint | Reference and error criterion | Result |
|---|---|---|
| [Exact-radius identity testing for fixed-mass diffuse bins](diffuse-bins.pdf) · [LaTeX](diffuse-bins.tex) | A singleton head and a fixed number of bins, with fixed positive masses. Within each bin the sum of squared conditional atom masses is at most a fixed constant divided by bin size. Worst-case alternative, error at most one third. | Matching upper and lower orders for every strict radius. At a suffix mass the transition involves both adjacent bin sizes. Known references can share maximum atom, Shannon entropy and any specified finite list of positive power sums while having unboundedly different costs at the same radius. |
| [High-confidence identity testing near maximum total variation](worst-case.pdf) · [LaTeX](worst-case.tex) | Worst case over all known references on a given alphabet. Both error probabilities are at most a specified positive level no greater than one third. | Matching orders throughout the radius interval between zero and one, with a separate high-confidence regime near distance one. In particular, at distance at least one minus one quarter of the reciprocal alphabet size, one observation suffices for every null at error one third. The lower-bound claim as printed in Theorem 2 of ICALP 2018 fails in this range. |

The general COLT 2024 Question 1 asks for a succinct characterization for *each* reference. The first paper treats a reference class and rules out one family of summaries. The second retains only the alphabet size when maximizing over references. Both are working preprints awaiting external review. [Canonne's question and AUD 200 offer](https://proceedings.mlr.press/v247/canonne24a/canonne24a.pdf#page=4) · [ICALP 2018, Definition 1 and Theorem 2](https://drops.dagstuhl.de/storage/00lipics/lipics-vol107-icalp2018/LIPIcs.ICALP.2018.41/LIPIcs.ICALP.2018.41.pdf#page=3)

## Reproduce the finite calculations

From the repository root, use Python 3.10 or later. Both programs use only the standard library and evaluate exact finite probabilities.

~~~sh
python3 -B studies/exact-radius-identity/check_priors.py
python3 -B studies/exact-radius-identity/check_endpoint.py
~~~

The first program verifies the six ordered-sample comparisons for two nonflat examples. The second checks the observed-histogram algorithm against exhaustive subsets, clone splitting, repeat-count inequalities, two lower-bound constructions and integer boundaries. Counts printed by the programs describe finite checks. The asymptotic bounds are proved in the papers.

## Reproduce the kernel checks

Use the [repository build instructions](../../REPRODUCE.md) to install the pinned Lean 4.36.0, Mathlib and the Rust kernel nanoda. With the matching Lean tools on the path and Mathlib dependencies cached, run each bundle in a new output directory. On Linux supply the pinned Docker image used in the [verification workflow](../../.github/workflows/verify.yml) with the option `--docker-image`. On macOS the wrapper isolates the Rust checker with Seatbelt.

~~~sh
for bundle in endpoint diffuse; do
  python3 studies/exact-radius-identity/verify.py --bundle "$bundle" \
    --mathlib /absolute/path/to/mathlib \
    --nanoda /absolute/path/to/nanoda/target/release/nanoda_bin \
    --run-dir "/tmp/exact-radius-$bundle"
done
~~~

The endpoint bundle proves the half-L1 identity, both error guarantees for the one-observation test under inclusive soundness and the existence of a strictly positive null with an alternative at equality. The diffuse bundle proves the deficit identity, comparison with the coarse observation, and the warm-set mass and size estimates. The independent checker accepted 8,885 and 9,080 declarations respectively, using only the three standard Lean foundations. The remaining minimax proofs, stochastic estimates and exact finite-moment construction are analytic. [Endpoint Lean](lean/EndpointOne.lean) · [Endpoint kernel report](verification/endpoint-one.json) · [Diffuse Lean](lean/DiffuseTV.lean) · [Diffuse kernel report](verification/diffuse.json)

Build the manuscripts by running `tectonic diffuse-bins.tex` and `tectonic worst-case.tex` in this directory. The author's Japanese name uses the small font subset already distributed in the sibling Canonne study. [Research record, prior work and roles](RESEARCH.md)
