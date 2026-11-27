# Covering grid edges with the boundaries of side-two squares

At CCCG 2025, Takumi Shiota asked for the complexity of covering the entire edge set of a given unit grid graph with exactly $k$ overlapping side-two square boundaries. We prove that the decision problem is NP-complete. The proof also treats a list in which placements may repeat and a budget of at most $k$ distinct placements. [Original Question 4](https://cccg-wads-2025.eecs.yorku.ca/CCCG_2025_Open_Problems.pdf#page=3) · [English paper](paper/paper.pdf)

The construction starts with a bendless orthogonal drawing of a planar graph of maximum degree three, a known NP-hard class for Vertex Cover. Five fixed configurations of square centers convert the drawing into a unit edge set. Some squares must be selected. The optional squares lie along odd paths between the original vertices. An edge of each path forces at least one of its two endpoint squares. For path lengths $2r_e+1$, the minimum number of squares is the number of forced squares plus $\sum_e r_e$ plus the original graph's vertex-cover number. [Source hardness theorem](https://doi.org/10.1137/20M1336412) · [Tables of the five configurations](paper/cores.tex)

## Verification scope

Lean proves that each decision answer agrees with the source answer for every valid normalized drawing and budget. It proves the eight-vertex induced boundary description, the correctness of the distinct and repeated certificate predicates on arbitrary target instances, and polynomial output bounds. The paper gives the bit-encoding running-time arguments and uses the published hardness of the source class. The Python program implements the geometric construction. Its cross-checks reconstruct admissible squares and covering constraints from the emitted unit edges. External specialist review is pending. [Top-level Lean equivalences](lean/ShiotaQuestionFour.lean) · [Certificate predicates](lean/GridCertificates.lean) · [Kernel receipt](verification/kernel.json) · [Independent source and priority review](verification/priority-review.md) · [Research record](RESEARCH.md)

## Reproduce the construction

Run these commands with Python 3.10 or later from the repository root. The first rechecks the 605 central neighborhoods and the 28 wire neighborhoods. The second verifies 144 complete drawings.

~~~sh
study=studies/shiota-square-cover
python3 -B "$study/experiments/check_stencils.py"
python3 -B "$study/experiments/check_uniform.py"
python3 -B "$study/experiments/square_cover.py" "$study/experiments/example.json" > /tmp/shiota-grid-example.json
~~~

An input contains a vertex list of integer coordinate pairs, a list of edges as zero-based vertex-index pairs, and a nonnegative source budget. The example is a five-cycle drawn along the boundary of a rectangle with one collinear vertex. Each emitted unit edge is given by a triple $(a,x,y)$. For $a=0$ it runs one unit right from $(x,y)$. For $a=1$ it runs one unit up. The output also gives the exact target budget.

The optional SAT test enumerates the optimal original cover independently, then verifies satisfiability at the predicted target optimum and unsatisfiability at one below it whenever that budget is nonnegative. Its input clauses are reconstructed directly from output grid edges. Install the pinned Python SAT package in an isolated environment to reproduce it. [Recorded replay totals](verification/replay-sat.json)

~~~sh
python3 -m venv /tmp/shiota-sat-venv
/tmp/shiota-sat-venv/bin/python -m pip install 'python-sat==1.8.dev24'
/tmp/shiota-sat-venv/bin/python -B studies/shiota-square-cover/experiments/check_uniform.py --sat
~~~

## Rebuild the proof and the manuscript

From the repository root, use Bash, Git, Python and Elan. The script checks the pinned Lean and Mathlib revisions and rebuilds the 35 local modules in dependency order. It invokes Lean's proof replay, exports the named theorems and their dependencies, rejects undeclared axioms outside the three standard Lean foundations, and invokes the independent Rust kernel. To use the recorded Rust revision, follow the build instructions and pass the binary with the option shown below. [Rust build and isolation instructions](../../lean/README.md) · [Theorem targets and build order](verify.py)

~~~bash
root="$PWD"
scratch="$(mktemp -d)"
elan toolchain install "$(cat "$root/lean/lean-toolchain")"
git clone --depth 1 --branch v4.36.0 https://github.com/leanprover-community/mathlib4.git "$scratch/mathlib"
(
  cd "$scratch/mathlib"
  modules="$(awk '$1 == "import" && $2 ~ /^Mathlib[.]/ {print $2}' "$root"/studies/shiota-square-cover/lean/*.lean | sort -u)"
  lake exe cache get $modules
)
python3 -B studies/shiota-square-cover/verify.py --mathlib "$scratch/mathlib" --run-dir "$scratch/checked"
cat "$scratch/checked/nanoda.txt"
~~~

The optional argument is `--nanoda /path/to/nanoda_bin`. Run `tectonic paper.tex` in `studies/shiota-square-cover/paper` to typeset the paper, including its configuration tables and bibliography.
