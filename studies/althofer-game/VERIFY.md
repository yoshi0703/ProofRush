# Reproducing the forced-outcome constructions

Althöfer's game starts on a positive odd integer. Each player freely chooses a sign, forms \(3n\pm1\), and removes every factor of two. The mover reaching 1 wins immediately. The mathematical results supply finite winning strategies for specified positions. The €500 sponsor question concerns every starting value under optimal play. [Sponsor and rules](https://althofer.de/collatz-prizes.html) · [Manuscript](paper.pdf) · [Research and prior work](RESEARCH.md)

## Integer experiments

From the ProofRush root run the scripts with Python 3.11 or later. They use only the Python standard library.

~~~sh
python3 -B studies/althofer-game/replay/check.py --limit 5000000
python3 -B studies/althofer-game/replay/audit.py
python3 -B studies/althofer-game/replay/diamond_checks.py
~~~

The first script compares the closed-form classification with literal legal moves on every odd start through five million. It also checks bounded strategy witnesses in 546 valuation/residue classes. The second implementation checks the four-ply examples, congruences and a bounded-horizon obstruction. The third constructs actual integer witnesses for every inverse word of length at most two and every residue modulo nine. It enforces the desired final residue by lifting the losing seed one ternary digit at a time. The proof in the paper gives the unbounded results.

## Independent proof checking

Use the pinned Lean 4.36.0 compiler, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, and the Rust kernel nanoda `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`. The workflow fetches the required compiled Mathlib imports. Each output directory below must be new. [Installation](../../lean/README.md) · [Hosted workflow](../../.github/workflows/verify.yml)

~~~sh
for bundle in moves diamonds seeds words; do
  python3 studies/althofer-game/verify.py --bundle "$bundle" \
    --mathlib /path/to/mathlib4 --nanoda /path/to/nanoda_bin \
    --run-dir "/path/to/new-check-$bundle"
done
~~~

The checker rebuilds the source, invokes Lean's module checker, audits the export and asks nanoda to verify the named theorems and all their dependencies. The recorded runs allowed only `propext`, `Quot.sound` and `Classical.choice`. Overlapping exports have separate declaration counts.

| Mathematical coverage | Sources | Local independent verdict |
| --- | --- | ---: |
| Existence and uniqueness of the normalized moves, classification in both directions for every integer start, and four strictly increasing infinite families of two-ply losses | [GameTwo](lean/GameTwo.lean) | [3,228 declarations](verification/game-two.json) |
| Correspondence between two-ply definitions, incompatibility of opposite finite strategies, the two inverse constructions preserving forced loss and the predecessor constructing a forced win | [Diamonds](lean/Diamonds.lean) | [3,268 declarations](verification/diamonds.json) |
| In every residue class modulo every power of three, explicit two-ply losing starts above every specified integer bound | [Seeds](lean/Seeds.lean) | [2,947 declarations](verification/seeds.json) |
| For each finite word, ternary residue and lower size bound, a seed and an integer path with a forced-loss endpoint, or a path to the appropriate child of a forced win | [Words](lean/Words.lean) | [3,339 declarations](verification/words.json) |

The Hausdorff-dimension bound concerns the 2-adic closures of sets of certified integer positions. The Lean word theorem supplies the actual integer witnesses for every finite prefix. Passing to the infinite 2-adic limit and computing the Hausdorff dimension are mathematical proofs in the manuscript. The manuscript also supplies the argument about classes specified by a 2-adic valuation and a ternary residue, and the explicit four-ply examples. The numerical checks support the constructions within their stated ranges. External scholarly review is pending.

Build the English PDF with Tectonic and a font containing the project initiator's name.

~~~sh
tectonic studies/althofer-game/paper.tex
~~~
