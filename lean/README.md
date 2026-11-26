# Verifying the counterexample

The witness is a connected simple graph on 14 vertices. Every vertex has degree 3, the diameter is 8, and the vertex clique cover number is 6. The proofs use Mathlib's shortest-walk metric and the chromatic number of the complement. [Lean proof](RegularCliqueCover.lean) · [GraphCalc definition](https://graphcalc.readthedocs.io/en/stable/_modules/graphcalc/graphs/invariants/classics.html#vertex_clique_cover_number)

The proof establishes both `RegularCliqueCover.refutes_5ed263d5`, for the printed claim, and `RegularCliqueCover.refutes_5ed263d5_on_domain`, for graphs on which the catalogue evaluates diameter. The latter theorem uses the proved connectedness of the witness. The independently transcribed propositions are in [CliqueCoverStatement.lean](CliqueCoverStatement.lean). [Original catalogue entry](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L2530) · [Author's evaluation wrapper](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/pipeline/invariants_graphcalc.py#L184)

## Run from a fresh checkout

Run these commands in Bash from the repository root with Git, Python 3 and [Elan](https://github.com/leanprover/elan) on your PATH. They create the dependencies and evidence in a temporary directory and print the location of the results.

```bash
proof_dir="$PWD/lean"
check_dir="$(mktemp -d)"
elan toolchain install "$(cat "$proof_dir/lean-toolchain")"
git clone --depth 1 --branch v4.36.0 \
  https://github.com/leanprover-community/mathlib4.git "$check_dir/mathlib"
(
  cd "$check_dir/mathlib"
  lake exe cache get Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex \
    Mathlib.Combinatorics.SimpleGraph.Diam Mathlib.Data.Fin.VecNotation
)
python3 experiments/counterexample.py
python3 "$proof_dir/verify.py" --mathlib "$check_dir/mathlib" \
  --run-dir "$check_dir/checked-proof"
```

The verifier checks the pinned Lean and Mathlib revisions, the digest of the source claim, and the exact types of both conclusions. It compiles the two source modules in a fresh directory, invokes Lean's kernel replay, exports both theorems with their transitive dependencies, and checks both target names and the axiom inventory. The independent Rust kernel [nanoda](https://github.com/ammkrn/nanoda_lib) checks the exported proof. The three permitted foundational axioms are `propext`, `Quot.sound`, and `Classical.choice`.

The recorded run accepted 7,184 declarations. The report contains the source, export and verifier hashes. [Recorded report](verification.json) · [Lean audit](lean-audit.txt) · [Rust kernel audit](nanoda-audit.txt)

## Independent checker built from source

The default command uses the nanoda executable distributed with Lean. To build the same source revision as the recorded run, install Rust and Cargo and continue in the shell above.

```bash
git clone https://github.com/ammkrn/nanoda_lib.git "$check_dir/nanoda"
git -C "$check_dir/nanoda" checkout --detach 0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929
cargo build --manifest-path "$check_dir/nanoda/Cargo.toml" \
  --target-dir "$check_dir/nanoda/target" --locked --release
python3 "$proof_dir/verify.py" --mathlib "$check_dir/mathlib" \
  --nanoda "$check_dir/nanoda/target/release/nanoda_bin" \
  --run-dir "$check_dir/checked-source-kernel"
```

The [Verify workflow](../.github/workflows/verify.yml) builds the Rust checker on Ubuntu with Rust 1.97.1. It runs the checker as an unprivileged user in a read-only Docker container with networking disabled. Only the checker binary and the directory containing the proof export and checker configuration are mounted. For local verification, macOS uses Seatbelt, Linux uses bubblewrap when installed, and other environments use a separate process with a clean environment. Each report records the isolation actually used.
