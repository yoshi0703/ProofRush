# Canonne Q2 research record

The research round began at 22:25:37 UTC. The analytical draft and its first cutoff calculations are recorded from 22:30 UTC on 26 November 2026 (27 November JST). The independent Rust replay of the original comparison finished at 22:40 UTC. This preprint is under the research direction of 大束良明 (Yoshiaki Otsuka) and has not been externally peer reviewed. No submission, prize claim, or author acknowledgement is recorded.

## Source alignment and reward

- [Canonne's MathOverflow question 332062](https://mathoverflow.net/questions/332062/relation-between-two-different-functionals-lvert-p-max-varepsilon-rve) was posted on 20 May 2019. It seeks a direct derivation of its equation (4), with changes of truncation radius by factors 9 and 32 and the baseline \(1\vee\). The retained atom at the truncation boundary is kept whole. The inverse level is \(1-e\). The sole displayed answer shows the need for an upper baseline using a point mass. The comments discuss restricting the null to have small \(\ell_2\)-norm.
- [Canonne's COLT 2024 problem statement](https://proceedings.mlr.press/v247/canonne24a.pdf) asks in Open Question 2 for a direct comparison between the truncated \(2/3\)-quasinorm and the inverse Peetre functional. Its BCG quantity uses the inverse level \(1-2e\). Section 5 offers an extra-large wombat plush toy for Q2. It gives no cash value, expiry, AI rule, or claim procedure for that offer. Continued availability is unconfirmed. The AUD 200 offer for Q1 applies to a different result about minimax sample complexity.

## Proof development

1. Use the minimum \(\ell_2\) norm among \(0\le z_i\le1\) capturing probability \(1-e\) to represent the inverse. Clipping a scaled copy of \(p\) produces an exactly optimal witness and a matching decomposition of \(p\). This construction applies on a countable domain.
2. Bound the \(\ell_{2/3}\) prefix from below by pricing its missing head mass and captured tail mass at the cutoff. Hölder gives a same-radius lower bound with coefficient one.
3. Protect the largest atom and use a power-weighted witness on the retained atoms. The elementary inequality \(x(1-x/\lambda)_+\le\lambda/4\) gives the sharp upper coefficient. A separate witness based on \((1-u)_+\le1/(4u)\) reproduced the same estimate.
4. Check sharpness by uniform and multiscale finite laws. Splitting the large head into finitely many equal atoms keeps its norm arbitrarily small as the tail size grows. A separate two-scale family keeps the same-radius truncated quasinorm bounded while its inverse norm grows.
5. Compare the original radius conventions and check cutoff equality, ties, a point mass, the inverse at zero level, and saturation at level one.

## Priority and published ingredients

The underlying \(K\)-functional duality was already stated by [Montgomery-Smith, Lemma 1](https://doi.org/10.1090/S0002-9939-1990-1013975-0). [Holmstedt](https://doi.org/10.7146/math.scand.a-10976) gives the classical interpolation estimate. [Blais, Canonne, and Gur](https://doi.org/10.1145/3305270) discuss the \(K\)-functional and related partition norms, as well as the comparison in concrete examples. Their conference version's Proposition 15 compares \(K\) itself to a head-plus-tail estimate. Its constant \(1/4\) applies to a different inequality. A multiplicative estimate for \(K\) does not automatically control its inverse at levels close to one. [Valiant and Valiant](https://doi.org/10.1137/151002526) supply the testing bounds involving the truncated quasinorm.

A targeted priority search included the exact MathOverflow problem and its cited sources, interpolation keywords, public indexed open-problem listings, and follow-up identity-testing manuscripts. It found no prior proof of both quantitative comparison inequalities in this generality. That search does not establish priority. The detailed audit, including which specific adjacent manuscripts were inspected, is in [the priority notes](prior-work.md).

## Independent checks

The independent mathematical review rederived both inequalities, matched the source's exact quantifiers and truncation conventions, and checked the two sharpness constructions and the same-radius obstruction. A separate Python program uses exact rational arithmetic on normalized integer cubes. On this input family the squares of the truncated quasinorm and of the minimum norm are rational. It found no contradiction among 1,000 reproducibly seeded finite laws, 20 exact tail-equality boundary checks and one countably infinite law with divergent untruncated \(2/3\)-power sum. The witnesses arise deterministically from the laws. No statistical experiment was used in the proof.

To reproduce the checks from this study directory, run:

~~~sh
python3 -B check.py
~~~

See also the [full independent mathematical review](independent-review.md) and [exact check source](check.py). The independent Rust kernel checked 19,298 declarations in the comparison export and 19,622 in the extremal export. The latter certifies both optimal universal constants and the obstruction at every fixed interior radius. The supplementary low-norm refinements are proved in the manuscript. [Kernel records, exact targets and reproduction commands](VERIFY.md)

## Contributions and build

- 大束良明 directed the research and set its criteria.
- GPT-6.2-Astra at maximum reasoning effort coordinated the research and developed the analytic proof, including the countable inverse-functional argument.
- GPT-6.2-Sol at medium effort independently reconstructed and reviewed the proof, verified sample laws in exact arithmetic, and prepared the preprint.
- GPT-6.1-Terra at medium effort investigated earlier literature and formalized the lower-bound steps and proofs of optimality for the two coefficients.
- GPT-6.2-Sol at high effort formalized the upper witness, source radii and unbounded same-radius example.

The human research brief asked for human-posed problems, stronger general constructions, independent proof attempts, and a priority audit. The project coordinator selected Canonne’s published problem. The research team split the work among proof construction, source comparison, formalization and adversarial review. The work used the existing Codex subscription and a local Apple M3 Pro. The versioned GitHub release includes aggregate model usage through publication. Its interval includes concurrent mathematics research by the same sessions, and the subscription provides no attributable monetary cost. [Versioned release](https://github.com/yoshi0703/ProofRush/releases/tag/canonne-functional-comparison-v0.1.0) No additional paid API was used. The archival build uses Tectonic 0.17.0. The Japanese name uses an installed CJK font or the supplied open-font subset. Build from the source directory so the relative fallback path is available.

~~~sh
tectonic paper.tex
pdfinfo paper.pdf
~~~

The final four-page PDF built without TeX warnings, passed PDFKit text checks on all four pages, and was inspected page by page after rasterization. PDFKit confirmed the title-page name 大束良明 is searchable.

SHA-256 checksums for the reviewed files:

~~~text
c6ef7996624c239bcee35c94f14de77fcee740d93b737c4c477b7fb0290fce15  paper.tex
4cdbeb2839c16a1eafd269fcf01703b97eeb536f11067b083b276173a8a675e4  paper.pdf
57192e1c724b0c957740836efa889dc7d7da6bbd72ceaaf90bf345f771d3ecc0  fonts/ProofRushDirectorJP.otf
~~~
