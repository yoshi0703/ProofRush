# Reproducing the result

## Graph invariants

From the repository root run the following with Python 3.8 or later. The program uses only the standard library.

```sh
python3 experiments/counterexample.py
```

It constructs a 21-edge cubic graph on 14 labeled vertices. Floyd–Warshall computes its distance matrix, and an exact recursion over all possible clique parts computes its minimum clique partition size. The output contains diameter 8, distance 8 from vertex 2 to 11, and vertex clique cover number 6. It also validates the six explicit cliques and the six independent vertices. [Saved output](verification/witness.json)

## Formal proof

Use the commands in [lean/README.md](lean/README.md) for a clean installation with pinned Lean 4.36.0 and Mathlib. They build both Lean source modules in a newly created directory, replay them with leanchecker, export the two theorem declarations and their dependencies, and check the export with the independent Rust kernel nanoda. The instructions include a source build of the independent kernel. [Machine-readable record](lean/verification.json) · [GitHub-hosted recipe](.github/workflows/verify.yml)

## Manuscript

With [Tectonic](https://tectonic-typesetting.github.io/) on your PATH, run the command below from the repository root. The first build may download standard TeX packages. It writes the manuscript to paper/paper.pdf. The illustration is drawn directly from the labeled edge set by TikZ. PDF metadata can vary with the typesetting environment. [TeX source](paper/paper.tex)

```sh
tectonic --outdir paper paper/paper.tex
```
