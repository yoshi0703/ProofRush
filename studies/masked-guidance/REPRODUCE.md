# Reproduction

From the root of this repository, run the exact demonstrations with stock Python 3.10 or newer. No package installation, random seed, training data or GPU is required.

~~~sh
python3 studies/masked-guidance/experiment.py
python3 studies/masked-guidance/leading_terms.py
~~~

The first script sums the paths ending at each positive-target word for each permutation of its coordinates. Its two-dimensional check independently computes the source paper's tilted, normalized conditional fibers. The three-bit and ternary product outputs include a six-decimal interval certified by integer division. In the second script a rational number represents the exponential base and another rational number represents the asymptotic coefficient. It checks the subset recurrence against exhaustive minimization and the limiting chain.

## Lean and the second kernel

The pinned toolchain is Lean 4.36.0 (commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9) and Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842. Nanoda is independently implemented in Rust; the pinned commit is 0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929. The workflow gives exact installation commands including the Linux Lean archive checksum and Rust toolchain. [Pinned workflow](../../.github/workflows/verify.yml) · [General verifier](../../lean/verify.py)

On a machine with this Lean release on PATH, start at the repository root and choose fresh dependency/output directories. The following is a Bash example with Git, Lake and Rust installed. Use locally appropriate paths.

~~~bash
set -eu
repo="$PWD"
deps="$(mktemp -d)"
git clone --quiet --depth 1 --branch v4.36.0 https://github.com/leanprover-community/mathlib4.git "$deps/mathlib"
test "$(git -C "$deps/mathlib" rev-parse HEAD)" = fc4f59e577feb1a4956671bc04ac18aaaf8cd842
(
  cd "$deps/mathlib"
  modules=$(awk '$1=="import" && $2 ~ /^Mathlib[.]/ {print $2}' "$repo"/studies/masked-guidance/lean/*.lean | sort -u)
  lake exe cache get $modules
)
git init --quiet "$deps/nanoda"
git -C "$deps/nanoda" fetch --quiet --depth 1 https://github.com/ammkrn/nanoda_lib.git 0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929
git -C "$deps/nanoda" checkout --quiet --detach FETCH_HEAD
test "$(git -C "$deps/nanoda" rev-parse HEAD)" = 0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929
cargo +1.97.1 build --locked --release --manifest-path "$deps/nanoda/Cargo.toml"
python3 studies/masked-guidance/verify.py --mathlib "$deps/mathlib" \
  --nanoda "$deps/nanoda/target/release/nanoda_bin" --run-dir "$deps/checks"
~~~

Each bundle gets a fresh directory. The verifier copies only the listed local Lean source files into it, rebuilds each module with warnings as errors, replays the modules with leanchecker, prints axioms, and exports the named theorems with their dependencies. It checks the actual export for missing targets or additional axioms. Nanoda then reads the export in a separate process. The hosted Linux workflow uses Docker with no network, no privileges and read-only proof and checker mounts. On macOS the local runner uses Seatbelt. Output includes source and export hashes, the Lean version, the external verifier's verdict, and the two transcripts. Counts of declarations in different bundles overlap.

## Paper

Run Tectonic on the TeX source to produce the paper. The prose and proof can also be read directly in the checked-in PDF.

~~~sh
tectonic studies/masked-guidance/paper.tex
~~~
