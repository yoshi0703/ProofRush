# Reproducing the spelling-identified BPE result

## The finite witness

Use Python 3.10 or later. These commands run from the repository root and use only the standard library.

```sh
python3 studies/string-identified-bpe/verify_witness.py
python3 studies/string-identified-bpe/verify_unique_greedy.py
python3 studies/string-identified-bpe/check_family.py
python3 studies/string-identified-bpe/check_scope.py
```

The first script computes maximum full and partial utility independently for all budgets from zero through four. It obtains 0, 1, 3, 6 and 10, and checks every greedy choice in the two displayed histories. The second verifies a single unweighted input with a unique maximizing pair at each step, with greedy utility 170 against a comparator of 404. The third checks both the maximizing pair types and the doubling comparator for 465 pairs of parameters with budgets through 30. [Finite witness](verification/independent-replay.txt) · [Unique greedy run](verification/unique-greedy-replay.txt) · [General family experiment](verification/family.txt)

The fourth command isolates initialization and ranking on the same 64 characters. [Practical scope and library replays](SCOPE.md)

The source authors' independent implementation accepts the same token sequence. The following optional replay checks the downloaded supplement against its expected SHA-256 digest before invoking its original partial-merge optimizer.

```sh
check_dir="$(mktemp -d)"
curl -fsSL 'https://zenodo.org/records/24451469/files/tight-constant-supplement.zip?download=1' -o "$check_dir/supplement.zip"
python3 studies/string-identified-bpe/replay_author.py "$check_dir/supplement.zip"
```

The finite counterexample uses arbitrary string-valued initial tokens in the source's non-unique-decoding examples and checker. The input consists of fourteen such tokens spelling 64 copies of one character. The source interpretation, prior counterexamples and practical restrictions are considered in the [semantic review](verification/source-review.md). [Original authors' replay](verification/author-replay.txt)

## Lean and an independent kernel

The following Bash commands install the pinned toolchain and Mathlib, build the Rust checker from its pinned sources, and check all six bundles from a fresh local build directory. Git, Python, Elan, Rustup and a C linker must be installed. The first build downloads public dependencies.

```bash
set -euo pipefail
study="$PWD/studies/string-identified-bpe"
check_dir="$(mktemp -d)"
export ELAN_TOOLCHAIN=leanprover/lean4:v4.36.0
elan toolchain install "$ELAN_TOOLCHAIN"
git clone --quiet --depth 1 --branch v4.36.0 https://github.com/leanprover-community/mathlib4.git "$check_dir/mathlib"
test "$(git -C "$check_dir/mathlib" rev-parse HEAD)" = fc4f59e577feb1a4956671bc04ac18aaaf8cd842
(
  cd "$check_dir/mathlib"
  modules=$(awk '$1 == "import" && $2 ~ /^Mathlib[.]/ {print $2}' "$study"/lean/*.lean | sort -u)
  lake exe cache get $modules
)
git init --quiet "$check_dir/nanoda"
git -C "$check_dir/nanoda" fetch --quiet --depth 1 https://github.com/ammkrn/nanoda_lib.git 0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929
git -C "$check_dir/nanoda" checkout --quiet --detach FETCH_HEAD
rustup toolchain install 1.97.1 --profile minimal
cargo +1.97.1 build --locked --release --manifest-path "$check_dir/nanoda/Cargo.toml"
python3 "$study/verify.py" --mathlib "$check_dir/mathlib" \
  --nanoda "$check_dir/nanoda/target/release/nanoda_bin" --run-dir "$check_dir/verified"
```

The verifier builds each bundle with Lean 4.36.0, invokes leanchecker, exports the specified theorems and their dependencies, audits the axiom names, and asks the independent nanoda kernel to check the proof terms. Only the Lean foundations `propext`, `Quot.sound` and `Classical.choice` are permitted. The records name the exact targets and give the source, export and binary hashes. Counts for the six bundles overlap. The public Linux workflow builds the checker independently and runs it inside an unprivileged, read-only Docker container without network access. [Workflow](../../.github/workflows/verify.yml)

| Bundle | Independently checked claim | Local record |
|---|---|---|
| Six-phase | End-to-end single-word one-sixth upper bound for the original construction, including source-domain conditions, every tie, and the actual optimum. | [Kernel report](verification/six-phase.json) |
| Diamond | Exact worst-case limit zero under both rankings, existence of complete runs, single-word domain and finite bound. | [Kernel report](verification/diamond.json) |
| Finite | Negation of the proposed universal bound for the original partial-rule optimum, actual ambiguity of the input, and the two greedy/comparator histories. | [Kernel report](verification/finite.json) |
| Forced | Private rows force a greedy rule under every tie order, and the four-merge inequality fails at every integer weight parameter at least six. | [Kernel report](verification/forced.json) |
| Phases | Incidence bound at every possible positive gap in the six periodic schedules, and a conditional quantitative bound arbitrarily close to one sixth. | [Kernel report](verification/phases.json) |
| Comparator | The doubling rules save exactly one token per active row per step. The sum over arbitrary seeds and schedules gives the stated comparator utility for every budget. | [Kernel report](verification/comparator.json) |

The new six-phase bundle connects the original row adjacency counts, each full comparator step, private rules and the separator encoding to the single input word. For all integers 4 ≤ L ≤ k it proves the paper's finite inequality against the actual optimum. For every positive rational ε it supplies one L and a threshold K such that for every k ≥ K all greedy runs save at most (1/6 + ε) times the optimum. Lean also proves the word has nonempty spellings and ambiguous actual factors. Version 3.0.0 contained component proofs of this family. [Original family theorem](lean/OriginalSix.lean) · [v3.0.0 verification scope](https://github.com/yoshi0703/ProofRush/blob/v3.0.0/studies/string-identified-bpe/VERIFY.md)

## The zero limit under both rankings

The two final Lean theorems quantify over all sufficiently large budgets. The definition of the objective takes the best complete greedy execution on each input, then the infimum over genuinely ambiguous words with nonempty atoms and positive optimum. The independent checker receives the complete terms for both limits and the explicit strict inequality below 1/6. The limit proof uses a partial comparator, which is exactly what the source permits. The manuscript proves the displayed comparator can also run in full. The one-letter recoding is checked separately. [Theorem statements](lean/DiamondResult.lean) · [Objective and its quantifiers](lean/LimitRatio.lean) · [Kernel report](verification/diamond.json)

The following commands reproduce the integer construction, both pair rankings, and the independent one-letter replay. The final command uses length arithmetic and streams the hash of the underlying characters. It does not allocate a 159 MB input word. The smaller test directly expands the token strings and visits every spent subset.

```sh
python3 studies/string-identified-bpe/check_diamond.py
python3 studies/string-identified-bpe/check_unary_diamond.py --m 2 --literal --all-subsets
python3 studies/string-identified-bpe/check_unary_diamond.py --m 13
```

## Rebuilding the manuscript

Run Tectonic from the repository root. The PDF uses ordinary LaTeX math and a Japanese font for the project initiator's name. The source checks for Noto Sans CJK JP, Hiragino Sans, then Harano Aji Mincho. PDF byte hashes can differ with fonts and engine versions.

```sh
tectonic --outdir studies/string-identified-bpe studies/string-identified-bpe/paper.tex
```
