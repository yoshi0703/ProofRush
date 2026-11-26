# Research and verification record

Prepared on 27 November 2026 JST (26 November 2026 UTC). The ProofRush research team presents a partial result for the fixed four-integer word in Shallit's BCTCS 2014 Open Problem 9. The original slide reports a prefix check of length 800 and lists a £50 offer for the full result. Its present claim rules and availability were not independently confirmed. No prize claim or submission to the author or a journal was made. External peer review is pending.

## Three results and their evidence

| Claim | Evidence | Scope |
|---|---|---|
| All shifts are nonsingular for every order 1–4,096 | Exact computation of the Hankel table modulo \(2^{61}-1\), with a substitution proof that the prefix covers every needed factor | Finite order range, unbounded shift |
| Every shift and integer \(R\ge1\) has a nonsingular order in \((R,13R]\) | Proof from overlap-freeness, factor complexity and the first failed monic recurrence, formalized in Lean and independently kernel-checked | All shifts, all \(R\), fields of characteristic zero or at least five |
| \(43\,\operatorname{rank}_{\mathbb Q}H_n(s)>13n\) | Mathematical proof reducing the rank inequality to exact finite checks on substitution factors | All shifts and orders over \(\mathbb Q\). This bound is outside the Lean proof |

None of these results settles full nonsingularity at every order.

## Reproduction and checks

- Prefix replay. A warning-enabled C++17 build of [the prefix checker](replay/hankel.cpp) verified all 10,485,862,400 matrices contained in the first 204,800 letters. The final checksum is 320903234180241819 modulo 2305843009213693951. The coordinator's rerun took 61.39 seconds on the local Apple M3 Pro. The Lucas–Lehmer primality check and independent Bareiss checks are in [cross_check.py](replay/cross_check.py). The nine adjacent pairs and the block coverage argument extend the order-4,096 result to every shift.
- Finite rank certificate. [rank_bounds.py](replay/rank_bounds.py) replayed 48,384 pair-offset checks across 20 order parameters. It also verified 186,624 pair-offset checks for orders 1–81. [independent_rank.py](replay/independent_rank.py) used separately implemented elimination over \(\mathbb F_3\) and verified the same 48,384 cases. Across the 21,420 distinct factors counted by parameter, 15,693 had an unequal-successor witness, 2,285 had an unequal-predecessor witness, and 3,442 had a ternary rank witness. A further local replay enumerated those distinct factors directly from the covering prefixes using binary elimination and agreed. [independent_small.py](replay/independent_small.py) separately checked the all-shift orders 1–81.
- Independent review of the analytic rank proof. The reviewed chain covers propagation of a dependence in the leading block, the count of linearly independent residual vectors with distinct first nonzero positions, reversal after removing initial zero coefficients, block-code injectivity, and the bound \((K(u)+1)B-1\) for containing \(K(u)\) aligned blocks. The exact scalar inequality \(13(K(u)+1)\le86(u-1)\) was checked for every table entry. No gap affecting the stated bound was found.
- Formal interval result. The proof modules [Word](lean/Word.lean), [NormalIndex](lean/NormalIndex.lean), and [FactorCode](lean/FactorCode.lean) use Lean 4.36.0, commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9, and Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842. The main theorem names are *ShallitFactorCode.numeric_nonsingular_interval* and *ShallitFactorCode.rational_nonsingular_interval*. The Nanoda run in macOS Seatbelt checked 9,774 exported declarations without errors. The export used propext, Classical.choice, and Quot.sound. It checks overlap-freeness and finite base factor counts as dependencies. [Small overlap replay](replay/overlap.py).
- Typesetting. Tectonic 0.17.0 uses the supplied open-font subset for the Japanese credit. The final PDF built without TeX warnings. All four rasterized pages were inspected. PDFKit confirmed they contain text and that the title-page name is searchable. [Font license](fonts/OFL.txt).

Run the arithmetic checks from the study directory:

~~~sh
clang++ -std=c++17 -O3 -Wall -Wextra -Wpedantic replay/hankel.cpp -o hankel
./hankel 204800
python3 -B replay/rank_bounds.py
python3 -B replay/independent_rank.py
python3 -B replay/independent_small.py
python3 -B replay/overlap.py
tectonic paper.tex
~~~

## Bibliographic and priority scope

The exact digits, title, problem number and historical offer were checked against [Shallit's slide 35](https://cs.uwaterloo.ca/~shallit/Talks/bc4.pdf#page=35). His [2014 BCTCS entry](https://cs.uwaterloo.ca/~shallit/talks.html) calls the integer variant unresolved and cites Cavalcante's 2026 solution to the separate three-real-value existence problem. The latter used the Dakota number wall over \(\mathbb F_9\) and a transcendental translate. Its alphabet and sequence do not give a certificate for this fixed integer word. [Dakota preprint, §§6–7](https://doi.org/10.5281/zenodo.21728308).

Qualitative uniform linear rank follows from linear recurrence of primitive aperiodic substitution words and the existence of right-special factors. [Durand–Host–Skau, §7.1](https://doi.org/10.1017/S0143385799133947). Recurrence and leading-minor structure are classical. [Iohvidov](https://doi.org/10.1070/SM1969v009n02ABEH001129) · [Bakan–Berg](https://doi.org/10.1142/9789813228887_0005). Number-wall computations and finite tiling certificates have established precedents. [Lunnon](https://cs.uwaterloo.ca/journals/JIS/VOL4/LUNNON/numbwall10.html) · [Adiceam–Nesharim–Lunnon](https://doi.org/10.1215/00127094-2020-0077). These sources and an exact-morphism search did not identify the same uniform numerical bound for this word. This limited search does not establish priority.

## Contributions

- 大束良明 (Yoshiaki Otsuka) directed the research.
- GPT-6.2-Sol at medium effort developed the initial determinant checks and nonsingular-order bound, formalized the recurrence and factor bounds, independently reviewed the larger rank result, and prepared the manuscript.
- GPT-6.2-Sol at high effort developed the stronger rank estimate and its finite checker and reviewed earlier work.
- GPT-6.1-Terra at medium effort formalized the automatic word and its overlap-freeness and independently reproduced and reviewed the quantitative rank certificate over the field of three elements.
- GPT-6.2-Astra at maximum effort coordinated the research and independent kernel audit.

The work used the existing Codex subscription, local Apple M3 Pro computation, and public source retrieval. The research round began on 26 November 2026 at 22:25:37 UTC. The local independent kernel replay finished by 23:05 UTC. The [versioned release](https://github.com/yoshi0703/ProofRush/releases/tag/shallit-hankel-v0.1.0) provides model usage through publication, including concurrent research on identity testing in the same sessions. No additional paid API was used.

SHA-256 checksums of the reviewed manuscript:

~~~text
412150d29585a7816681eddeb2c1f1d03375efc581df8704b00c21961b8db302  paper.tex
45ac554604dad793e7667649ef1b7ac111741a8da2cb8644c6e17d23489ff78d  paper.pdf
57192e1c724b0c957740836efa889dc7d7da6bbd72ceaaf90bf345f771d3ecc0  fonts/ProofRushDirectorJP.otf
~~~
