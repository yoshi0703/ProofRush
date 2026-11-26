# Reproducing the partial results on Shallit's Hankel problem

Shallit's 2014 question fixes the four integer values and the substitution that generates their sequence. A matrix of order $n$ starting at offset $s$ has entry $a_{s+i+j}$ in row $i$, column $j$, with zero-based indices. The question asks whether every such matrix is nonsingular. The original £50 offer appears on slide 35. The author describes the integer case as unresolved in a 2026 update. These partial results have not been submitted for the award or externally peer reviewed. [Original question](https://cs.uwaterloo.ca/~shallit/Talks/bc4.pdf#page=35) · [Author's update](https://cs.uwaterloo.ca/~shallit/talks.html) · [English paper](paper.pdf)

| What the study establishes | Evidence |
| --- | --- |
| Every shift and every order through 4,096 have nonzero integer determinant. All 10,485,862,400 matrices contained in the first 204,800 terms were nonzero modulo $2^{61}-1$. Every factor needed through order 4,096 occurs in that prefix. | [Modular calculation](replay/hankel.cpp) · [Exact integer cross-check](replay/cross_check.py) |
| For every shift and every positive integer $R$, there is a nonsingular order strictly above $R$ and at most $13R$. The proof applies over the rationals and over any field of characteristic zero or at least five. | [Concrete automatic word and overlap proof](lean/Word.lean) · [Moment and determinant argument](lean/NormalIndex.lean) · [Source sequence and final statements](lean/FactorCode.lean) · [Independent kernel record](verification/interval.json) |
| At every order $n$ and shift $s$, rational rank $r$ satisfies $43r>13n$. This stronger rank bound has a written proof and a finite exact certificate. Two implementations tested the 48,384 substitution-block cases. One used binary elimination and the other closed all its rank cases modulo three. | [Certificate](replay/rank_bounds.py) · [Independent implementation](replay/independent_rank.py) · [Mathematical audit](independent-review.md) |

The bounded-gap proof, including its finite transition and factor counts, was rebuilt in Lean 4.36.0 and independently verified by nanoda over 9,774 exported declarations. The allowed foundations were `propext`, `Quot.sound` and `Classical.choice`. The full rational-rank proof and the large determinant scan are documented separately from this kernel export. A qualitative lower bound linear in $n$ also follows from earlier work on primitive substitutions. The quantitative coefficient and its proof are described in the paper and the independent audit. [Research record](RESEARCH.md)

## Exact calculations

From the repository root, use a C++17 compiler with 128-bit integer support and Python 3.11 or later. The Python scripts use the standard library. The computation on the first 204,800 terms used about 61 seconds on an Apple M3 Pro.

~~~bash
replay=studies/shallit-hankel/replay
out=$(mktemp -d)
c++ -O3 -std=c++17 -Wall -Wextra -Werror "$replay/hankel.cpp" -o "$out/hankel"
"$out/hankel" 204800
python3 -B "$replay/cross_check.py" --hankel "$out/hankel"
python3 -B "$replay/rank_bounds.py"
python3 -B "$replay/independent_rank.py"
python3 -B "$replay/independent_small.py"
~~~

The count and modular checksum of the full scan are reproduced below.

~~~text
length=204800 count=10485862400 checksum=320903234180241819 modulus=2305843009213693951
~~~

The first independent integer cross-check uses Bareiss elimination on all 420 matrices in a 40-term prefix and 128 additional samples. The small-order cross-check verifies primality, maps the substitution factors to matrix windows, and checks 186,624 order/pair/offset combinations through order 81. Two auxiliary scripts reproduce the overlap-transition tables and the tests for finite-field obstructions to a single-prime proof. [Overlap tables](replay/overlap.py) · [Modular obstructions](replay/rank_bounds_check.py)

## Clean kernel replay

Use Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` and nanoda `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`. After following the installation instructions, set `MATHLIB_DIR` to the pinned Mathlib checkout and `NANODA_BIN` to the compiled Rust executable. [Tool installation](../../lean/README.md) · [Hosted checks](../../.github/workflows/verify.yml)

~~~bash
proof_dir="$PWD/studies/shallit-hankel"
modules=$(awk '$1 == "import" && $2 ~ /^Mathlib[.]/ {print $2}' "$proof_dir"/lean/*.lean | sort -u)
(cd "$MATHLIB_DIR" && lake exe cache get $modules)
out=$(mktemp -d)
python3 "$proof_dir/verify.py" --mathlib "$MATHLIB_DIR" --nanoda "$NANODA_BIN" --run-dir "$out/interval"
~~~

The replay compiles each source with warnings as errors, checks the compiled modules, exports the four named theorems with their dependencies, audits the permitted axioms, and runs the separate Rust checker. The hosted version performs the final step in a read-only Linux container without networking. Run Tectonic on the TeX file from the study directory to regenerate the English PDF. [TeX source](paper.tex)
