# Reproduce the shoreline-transect analysis

Run the following from the repository root with CPython 3.11 or later. The scripts use the Python standard library.

## Frozen replay

```sh
python3 -B studies/shoreline-transects/replay/reproduce.py
python3 -B studies/shoreline-transects/replay/reproduce.py --json
```

The first command is the quick offline verification. The second prints both complete numerical reports, the pilot’s consecutive-pair flow and the site-level total for complete repeats. The program checks the SHA-256 of both frozen input files and verifies the reconstructed reports against hashes from the independent original analyses. Report hashes use UTF-8 JSON with sorted keys, no insignificant whitespace, and the original numerical values. Source ZIP hashes are recorded separately.

The full offline checks include the quick replay plus these exact arithmetic scripts.

```sh
python3 -B studies/shoreline-transects/replay/rounding.py
python3 -B studies/shoreline-transects/replay/identification.py
python3 -B studies/shoreline-transects/replay/finite_design.py
python3 -B studies/shoreline-transects/replay/robust.py --exact
```

The released data contain numerical summaries needed for the reported estimands, site-level bootstrap and sample flows. The pilot bootstrap inputs are ordered site-level means and visit counts with no site identifier in those arrays. Selected public numeric site IDs in the manifest and certain site-level totals are pseudonymous and can be linked to the source registry. The release contains no copied visit or strip rows, precise coordinates, notes, names, photo references or NOAA export archives. Public download access does not establish licensing for redistribution of every contribution in the partner-submitted archive. [NOAA MDMAP public data access](https://marinedebris.noaa.gov/our-work/monitoring/marine-debris-monitoring-and-assessment-project)

## NOAA export refresh

```sh
python3 -B studies/shoreline-transects/replay/reproduce.py --refresh --check-index --json
```

This performs an anonymous, read-only export through NOAA’s public site API. It submits the frozen numeric site IDs in six batches of four for each cohort, with at most two concurrent requests. Raw responses are held in a temporary directory outside the checkout and the script emits aggregated numerical output. The optional index check compares today’s eligible roster and ranks with the original, without substituting sites. Registry updates and archive metadata can change the official responses, so both raw archive hashes and reconstructed numerical report hashes are compared separately. The frozen replay remains available offline. [NOAA data portal](https://mdmap.orr.noaa.gov/) · [MDMAP public download FAQ](https://marinedebris.noaa.gov/monitoring/shoreline-monitoring-faqs)

To verify original archives already held locally, supply a directory for each cohort, with filenames as in the manifest.

```sh
python3 -B studies/shoreline-transects/replay/reproduce.py \
  --archives /local/pilot-archives /local/holdout-archives --require-original --json
```

## Cohorts and units

The frozen site index had 152 verified United States sites listing at least eight surveys. Sites were ordered by the SHA-256 of the fixed manifest prefix plus the public site ID. The pilot used ranks 1–24 and the held-out audit used ranks 25–48. The analyses read the main-beach file, retain zero counts and group strips by site, survey ID and date.

| Flow | Pilot | Holdout |
| --- | ---: | ---: |
| Sites selected | 24 | 24 |
| Exported main-beach strip rows | 1,888 | 2,182 |
| Visits before filters | 527 | 664 |
| Excluded for protocol | 250 | 303 |
| Excluded for visit size | 11 | 1 |
| Excluded for positions or width | 3 | 1 |
| Qualifying visits | 263 | 359 |
| Contributing sites | 18 | 18 |
| Length sensitivity visits | 216 | 199 |

Eligible visits have one survey ID for a site-date across protocols, the MDMAP 2.0 protocol, four distinct starts on the 0–95 m grid, 5 m widths and four recorded nonnegative counts. Length sensitivity uses the 90–110 m metadata range. The pilot also excludes observations carrying a note flag in that sensitivity. It extracts the flag locally by a fixed pattern, and no text is carried into the summaries. The independent held-out implementation checks that all four rows meet the length band. Pilot carryover pairs use adjacency in the complete site chronology before visit eligibility is applied. From 503 adjacent pairs, 236 retain both visits, 151 are 21–42 days apart, and 130 also meet the pilot’s note and length restrictions.

Endpoint inclusion is the fraction of the two endpoint strips selected per visit, averaged across visits within a site and then across sites for the site-weighted value. Item abundance is **recorded items per strip** in the empirical report. For each candidate design, the inverse-inclusion estimator divides by the 20 potential strips. The pilot uses 4,000 site-bootstrap resamples with seed 638591 and sorted positions 100 and 3899, indexed from zero. The held-out audit uses 10,000 with seed 20261127 and positions 249 and 9749. These intervals describe variation within the sampled cohorts. The mathematical bias and variance calculations condition on the stipulated selection design and fixed strip populations. The export does not identify which rule a team actually used.
