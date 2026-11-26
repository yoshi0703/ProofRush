# Reproducing the attention dimension bounds

The formal entry points are `AttentionJoint.joint_dimension` and `AttentionJoint.logarithmic_dimension`. They compare the least positive sufficient value dimension for every input length with an explicit binomial threshold. The quantifiers range over strict polynomial thresholds on bit vectors whose sign depends only on Hamming weight. The learned heads and readout may depend on the target. The underlying softmax operation uses arbitrary positive ratios and is evaluated on normalized Hamming weights. The lower obstruction allows either sign at zero. [Model and quantifiers](lean/JointDimension.lean) · [Kernel report](verification/joint.json)

Set up the published Lean 4.36.0 compiler, Mathlib revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, and nanoda revision `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` as described in the [repository reproduction instructions](../../REPRODUCE.md). The Mathlib checkout must contain the compiled imports used by these sources. From that checkout on Bash on Linux, the following installs the required cache entries; supply the absolute path to the ProofRush checkout as `PROOFRUSH`.

```sh
mapfile -t imports < <(awk '$1 == "import" && $2 ~ /^Mathlib[.]/ {print $2}' "$PROOFRUSH"/studies/attention-value-dimension/lean/*.lean | sort -u)
lake exe cache get "${imports[@]}"
```

From the ProofRush root, run these commands with the pinned Lean on the path. The argument to `--run-dir` must name a new directory.

```sh
python3 studies/attention-value-dimension/check_bounds.py
python3 studies/attention-value-dimension/rank_example.py
python3 studies/attention-value-dimension/verify.py \
  --mathlib /path/to/mathlib4 --nanoda /path/to/nanoda_bin \
  --run-dir /path/to/new-verification-directory
```

On Linux use the pinned Docker image and the additional `--docker-image` argument shown in the [published workflow](../../.github/workflows/verify.yml). The verifier rebuilds the 21 study modules from source, runs Lean's module checker, audits the actual NDJSON export, and replays it in nanoda with the proof sources, the compilation directory, Mathlib and network inaccessible. The checker permits only `propext`, `Quot.sound` and `Classical.choice`. Each report lists proof targets, source hashes, export digest and verifier digest. [Lower branch](verification/lower.json) · [Shared radix branch](verification/upper.json)

The main bidirectional order bound and the logarithmic regime bound have end-to-end formal proofs. The independent Warren counting argument and the sharper projective-curve upper bound are proved in the manuscript using the cited literature. The matrix-rank script certifies a single finite example using exact integer operations modulo a prime. The compiled paper can be reproduced with `tectonic studies/attention-value-dimension/paper.tex`, with a Japanese font available for the project director's name. [Manuscript](paper.tex)
