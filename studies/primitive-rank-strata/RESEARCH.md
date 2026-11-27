# Research record

Yoshiaki Otsuka (大束良明) directed the search for a complete solution to a human-posed academic problem and set the requirements for source fidelity, independent verification, technical significance and disclosure. The proof, implementation, automated reviews and literature investigation were developed by OpenAI Codex agents. The team has no external referee report for this preprint.

| Role | Model and reasoning setting | Work |
| --- | --- | --- |
| Coordinator | GPT-6.2 Astra, max | Identified the obstruction in the published definition, developed the general support and sublanguage arguments, built the literal binary-word bridge and integrated the paper and archive. |
| Formal proof researcher | GPT-6.2 Sol, high | Constructed the cyclic/CRT model for 105 positions and proved impossibility of a sparse-period presentation for an infinite primitive ray. |
| Independent mathematical reviewer | GPT-6.2 Sol, high | Reconstructed the proof, audited the ambiguous quantifiers and the even case, checked prime-power examples and formalized the minimum-support theorem and its equality cases on product grids. |
| Prior-art researcher | GPT-6.2 Sol, medium | Examined the author's original example, indexed corrections, earlier whole-slice theorems, the monograph preview and later primary literature. |
| Manuscript referee | GPT-6.2 Astra, max | Checked the strong and weak rank readings, provided a separate cyclic Fourier proof of the sparse-period classification, and identified textual, attribution and reference corrections. |

The team used the existing Codex environment and an Apple M3 Pro with 11 CPU cores and 18 GiB of memory for the local verification, finite experiments and manuscript build. No separately billed model API was used. The local wall-clock interval from creation of this study's research directory to the complete independent kernel receipt was 26 minutes 44 seconds on 27 November 2026, from 08:47:29 to 09:14:13 UTC. Candidate selection, prior work on the wider primitive-word problem, and subsequent release review fall outside that interval.

First we tested whether the larger primitive sets in Kászonyi's rank-one proof enforce the defining higher-rank equalities. They can contain vectors outside the exact class. Isolating one entry of a two-supported vector in an odd prime box gave the initial obstruction. Independent reconstructions then identified the antipodal exception for even sizes and a family of primitive vectors violating every proposed finite cover. A second derivation uses the first two Fourier coefficients on the cyclic index set.

The integer witnesses were checked against the ordinary binary word, including zero gaps. Weighting the three pair terms by 1, 2 and 2 gives gap sum 23; choosing multipliers congruent to 1 modulo 105 makes the letter counts coprime. The independent calculation of box signatures also reproduced the original paper's Example 2, 188,358 support-pair checks and direct proper-power tests on 64 finite words. These finite checks test the transcription and implementation. The contradiction itself covers infinitely many binary words and all finite stratifications. [Finite check record](verification/finite-checks.json) · [Explicit word constructor](lean/GapWords.lean)

The archive distinguishes the kernel-checked disproof, the general grid theorems, the written all-parameter language result, and the bounded novelty search. A cited application to Cartesian codes and the underlying Ginsburg–Spanier criteria are credited as prior results. The intermediate-rank conjecture is the single original question answered here. [Formal transcript](verification/lean.txt) · [Literature audit](research/priority.md) · [Independent referee report](research/referee.md)
