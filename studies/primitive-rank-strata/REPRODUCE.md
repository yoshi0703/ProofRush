# Reproduce the primitive-word refutation

Run the commands in Bash from the repository root at the release tag, or from the root of the extracted replay archive. The archive supplies the same study sources and common verifier as the tag. It also contains the already exported kernel proof. [Versioned release](https://github.com/yoshi0703/ProofRush/releases/tag/primitive-rank-strata-v1.0.0)

## Independent kernel replay

Python 3, Git, Elan and Rust/Cargo are required to rebuild from source. The released theorem was checked with Lean 4.36.0, Mathlib at `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` and nanoda at `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`. The runner checks the actual Lean and Mathlib revisions. [Source hashes and targets](verification/report.json)

~~~bash
study="$PWD/studies/primitive-rank-strata"
build_dir="$(mktemp -d)"
elan toolchain install leanprover/lean4:v4.36.0
git clone --depth 1 --branch v4.36.0 https://github.com/leanprover-community/mathlib4.git "$build_dir/mathlib"
(
  cd "$build_dir/mathlib"
  test "$(git rev-parse HEAD)" = fc4f59e577feb1a4956671bc04ac18aaaf8cd842
  awk '$1 == "import" && $2 ~ /^Mathlib[.]/ {print $2}' "$study"/lean/*.lean |
    sort -u | xargs lake exe cache get
)
git clone https://github.com/ammkrn/nanoda_lib.git "$build_dir/nanoda"
git -C "$build_dir/nanoda" checkout --detach 0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929
cargo build --manifest-path "$build_dir/nanoda/Cargo.toml" \
  --target-dir "$build_dir/nanoda/target" --locked --release
python3 "$study/verify.py" --mathlib "$build_dir/mathlib" \
  --nanoda "$build_dir/nanoda/target/release/nanoda_bin" \
  --run-dir "$build_dir/rebuilt"
~~~

This compiles seven modules in a fresh directory, runs Lean's separate module checker, exports the ten named results, checks the axiom declarations and runs the Rust kernel. The local receipt records macOS Seatbelt with file writes, network access and reads from the proof sources and built Mathlib tree denied during the Rust step. In the repository's Linux workflow the kernel runs in a read-only container. [Lean transcript](verification/lean.txt) · [Independent verdict](verification/nanoda.txt)

For a shorter replay with the above Rust binary alone, change to the archive's `kernel-export` directory, verify the digest in the receipt, and check the export.

~~~bash
(
  cd kernel-export
  python3 -c 'import hashlib, json, pathlib; p=pathlib.Path("proof.ndjson"); record=json.loads(pathlib.Path("../studies/primitive-rank-strata/verification/report.json").read_text()); assert hashlib.sha256(p.read_bytes()).hexdigest() == record["export_sha256"]'
  "$build_dir/nanoda/target/release/nanoda_bin" check.json
)
~~~

## Mathematical statement

The main target is `Kasonyi105.page328_intersection`. Its domain is the 105 exponents of the word with consecutive blocks consisting of one `a` and some number of `b` letters. It uses a decoder for the paper's exponent-set operation on the primitive slice, precisely the coprimality condition on the cyclic boxes, and both period conditions of stratification. The separate target `Kasonyi105.existential_rank_refutation` tests the weaker nonvanishing quantifier. [Literal statement](lean/PublishedConjecture.lean) · [Source Definition 10 and conjecture](https://publi.math.unideb.hu/paper/1506/download/10_5486_PMD_2010_4680.pdf#page=13)

The three `KasonyiGrid` targets state the minimum support bound, its equality cases and attainment on finite rectangular integer arrays. The paper transfers this calculation to all cyclic prime-power slices and uses the classical bounded-language characterization for its sublanguage theorem. [Grid targets](lean/GridSupport.lean) · [Proof and references](paper/paper.pdf)

## Finite experiments and paper

The two deterministic Python programs use the standard library. The first reproduces the paper's 30-block example and the cyclic witnesses. The second checks sparse directions, signed boxes and literal word powers across 16 parameter pairs.

~~~bash
study="$PWD/studies/primitive-rank-strata"
python3 -B "$study/experiments/check_literal_boxes.py"
python3 -B "$study/experiments/check_strata.py" > "$build_dir/boxes.json"
cmp "$build_dir/boxes.json" "$study/verification/finite-checks.json"
(cd "$study/paper" && SOURCE_DATE_EPOCH=1795737600 tectonic paper.tex)
~~~

The study's English paper and the font needed to print the research director's name are included. [Font provenance and license](paper/fonts/README.md)
