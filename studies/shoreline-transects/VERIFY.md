# Reproducing the shoreline survey results

The paper uses independent numerical calculations, a design-based mathematical proof, and public archive observations. Each supports a different part of the result. [English manuscript](paper.pdf) · [Research chronology](RESEARCH.md) · [Sources and priority](PRIOR-ART.md)

## Survey records and numerical results

From the repository root, run the following with CPython 3.11 or later. The first command rebuilds both cohort reports offline from released aggregates and compares them with checksums from the original, separate analyses. The second computes the endpoint probabilities. The third calculates the bias certificates, and the last two check the two-stage formula and the claimed sampling moments.

~~~sh
python3 -B studies/shoreline-transects/replay/reproduce.py
python3 -B studies/shoreline-transects/replay/rounding.py
python3 -B studies/shoreline-transects/replay/identification.py
python3 -B studies/shoreline-transects/replay/finite_design.py
python3 -B studies/shoreline-transects/replay/robust.py --exact
~~~

The source ZIPs are downloadable from NOAA. The release includes hashes, site-selection rules, counts and statistical summaries. The live export can differ at the byte level even when it gives the same numerical results. The replay documentation covers both the frozen and live paths. [Data and replay](replay/README.md) · [NOAA Marine Debris Monitoring and Assessment Project](https://marinedebris.noaa.gov/our-work/monitoring/marine-debris-monitoring-and-assessment-project)

## Design theorems

Install Lean 4.36.0, Mathlib revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` and nanoda revision `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`. Fetch the Mathlib cache for the imports in the three study modules. The commands used on Linux are in the repository workflow. [Toolchain setup](../../lean/README.md) · [Hosted recipe](../../.github/workflows/verify.yml)

~~~sh
python3 studies/shoreline-transects/verify.py \
  --mathlib /path/to/mathlib4 --nanoda /path/to/nanoda_bin \
  --run-dir /path/to/new-output-directory
~~~

The script rebuilds each source, runs Lean's module checker, checks each named theorem in the export, rejects nonstandard axioms and replays the declarations using the independent Rust kernel. In the recorded local run, a macOS Seatbelt sandbox denied the kernel network access and access to the proof sources, compiled project and Mathlib. Each bundle used only `Classical.choice`, `Quot.sound` and `propext`. The independent exports have overlapping dependencies.

| Bundle | Statements checked | Declarations in the export |
| --- | --- | ---: |
| [Four-strip model](verification/kernel.json) | All 96 rounded raw draws, the three endpoint-count laws and inclusion probabilities, the impossibility of a common unbiased estimator from unordered labels and counts, sharp bounds and attaining weights for three calibration classes | 9,157 |
| [General finite designs](verification/calibration.json) | For every family of designs on finite sample and label spaces, a common unbiased estimator of a linear population target exists exactly when sample- and label-specific weights satisfy the simultaneous inclusion equations | 7,300 |

The four-strip model conditions on the number of sampled endpoints and uses uniform sampling within the strata. The published proof and an independent enumeration connect the stipulated sampling rules to those conditional laws. The paper derives the two-stratum rank criterion and the passage from randomized estimators to their conditional means. Real-world selector use, external validity and scholarly priority require empirical and bibliographic evidence. [Four-strip source](lean/Shoreline.lean) · [Sharp calibration](lean/EndpointBias.lean) · [General construction](lean/LinearEstimator.lean)

Build the working paper with Tectonic and a font containing the project initiator's Japanese name.

~~~sh
tectonic studies/shoreline-transects/paper.tex
~~~
