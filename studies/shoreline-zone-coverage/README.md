# When a partial beach count reverses the direction of change

The [three-page research note](paper.pdf) reanalyses actual litter removals from South Africa and independently examines seasonal data from Italy. Five of 17 consecutive South African changes reversed sign on restricting counts to the upper zone. At Spina the recorded autumn-to-winter full count rose by 74 while the count inland of the swash fell by 41–47, allowing for rounding. The two studies define different cross-shore boundaries.

A separate analysis concerns period totals. Counting all upper catches and a random subset of labeled lower catches at each South African site reaches a 95% joint success fraction at a 20% error tolerance with nine of 19 lower counts, given the historical catches. The design requires all field removals to continue. Neither the probability nor the budget is transferable to other campaigns without further evidence. This secondary study is awaiting external review.

## Reproduce the field and design analyses

From the repository root with Python 3.10 or later, run

~~~sh
python3 -B studies/shoreline-zone-coverage/replay/check.py --out /tmp/shoreline-zone-results.json
~~~

The replay uses only the standard library. It verifies the three compressed archive inputs against their uncompressed byte counts and SHA-256 digests, independently reconstructs the South African counts with Python item categories and with SQL, enumerates all audit assignments, and bounds the Adriatic swash counts using the published tables. Use the optional flag \`--live\` to download and verify the same inputs from the original providers. The JSON contains the underlying daily and seasonal comparisons, the sensitivity to material totals and the site-wise audit results at three error tolerances. [Source manifest](data/manifest.json)

## Reproduce the formal checks

Use the repository's [pinned Lean and independent kernel setup](../../REPRODUCE.md). With the matching Mathlib and nanoda builds available, run

~~~sh
python3 studies/shoreline-zone-coverage/verify.py --mathlib /path/to/mathlib \
  --nanoda /path/to/nanoda_bin --run-dir /tmp/shoreline-zone-kernel
~~~

The run directory must be new. The Lean source encodes one draw per labeled subset of dates. It enumerates the exact success fractions from the 19 published-analysis lower-zone inputs, proves which allocations of up to nine meet the 95% criterion, proves the correction-factor lower bound for real multipliers and checks the Spina count inequality. The relation between source files and the 19 numbers is independently replayed in Python, as are the density-rounding intervals in Italy. The original field counts and the study design's applicability are empirical inputs. [Lean statements](lean/SurveyAudit.lean) · [Independent kernel report](verification/kernel.json)

Build the paper from the repository root with \`tectonic -X compile studies/shoreline-zone-coverage/paper.tex\`. The source references the existing repository font subset for the project director's name.

## Data attribution

- Cefas Marine Litter Team et al. (2020), *CLiP South Africa Marine Litter Accumulation Study (Cefas-UKZN) 2019*, Cefas, UK, V3, DOI 10.14466/CefasDataHub.95. Contains public sector information licensed under the Open Government Licence v3.0. The two original unmodified CSVs are losslessly compressed in the archive. [Official dataset and licence](https://www.cefas.co.uk/data-and-publications/dois/clip-south-africa-marine-litter-accumulation-study-cefas-ukzn-2019/) · [OGL v3.0](https://www.nationalarchives.gov.uk/doc/open-government-licence/version/3/)
- Joana Buoninsegni, Giorgio Anfuso, Francisco Asensio-Montesinos, Elena Marrocchino and Carmela Vaccaro (2025), *The Seasonal and Cross-Shore Distribution of Beach Litter Along Four Sites on the Northern Adriatic Coast (Ferrara, Italy)*, Water 17, 2173, DOI 10.3390/w17152173. The publisher's unmodified JATS XML is compressed in the archive under CC BY 4.0. New derived tables and interpretation are by the ProofRush team. [Article](https://www.mdpi.com/2073-4441/17/15/2173) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)

The research log records the roles of the field teams, the project director and the models. [Research log and limitations](RESEARCH.md)
