# ProofRush

## Value dimension in one softmax attention layer

Hsu and Xu asked how much value dimension is needed to classify symmetric Boolean functions with one fixed-query attention layer. With \(H\) heads and readout degree \(D\), let \(r\) be the least positive integer with \(\binom{D+r}{r}\ge HD+1\). The least universal dimension satisfies \(\min(D,r)/3\le d_*(H,D)\le\min(D,32r)\). In particular, when \(D\ge3\) and \(H\ge4^D\), some target requires at least \(D-1\) channels, and \(D\) always suffice. The joint theorem has a complete Lean proof on bit vectors, independently replayed in the Rust kernel nanoda. External peer review is pending. [English paper](studies/attention-value-dimension/paper.pdf) · [Formal theorem](studies/attention-value-dimension/lean/JointDimension.lean) · [Research record](studies/attention-value-dimension/RESEARCH.md) · [Reproduction](studies/attention-value-dimension/VERIFY.md) · [Original question](https://arxiv.org/html/2608.04243v1#S3.SS2)

## Spelling identity in byte-pair encoding

Baliga, Xie and Byju asked whether their greedy BPE guarantee extends to inputs with ambiguous initial token spellings. A 14-token example gives a negative answer at four merges. A second construction proves the exact worst-case limit is zero as the merge budget grows, even when each input receives its best greedy tie order. The result holds for both disjoint replacement counts and raw overlapping counts. At 338 merges every greedy run saves 4,732 tokens, while an explicit 338-rule comparator saves 30,758. The initial dictionary may contain arbitrary compound spellings. [English paper](studies/string-identified-bpe/paper.pdf) · [Limit theorems in Lean](studies/string-identified-bpe/lean/DiamondResult.lean) · [Independent checks and reproduction](studies/string-identified-bpe/VERIFY.md)

Starting from the 64 individual ASCII letters underlying the short counterexample, the four mathematical greedy merges save 60 tokens and attain the optimum. Starting from the fourteen prescribed tokens and counting overlapping observations, all legal greedy histories save five against an optimum of ten. Both initialization and pair ranking affect what transfers to a trainer. [Scope and two native tokenizer replays](studies/string-identified-bpe/SCOPE.md) · [Source authors’ open question](https://arxiv.org/html/2611.08671v3#S8) · [Research chronology](studies/string-identified-bpe/RESEARCH.md)

## Masked discrete diffusion

A two-bit distribution disproves the support-ordering conjecture of He, Rojas and Tao (ICLR 2026, Conjecture E.1) and the limiting-support conclusion of Proposition 3.3(2). We also prove a finite-alphabet theorem identifying which outputs survive strong guidance, a subset recurrence computing their decay exponents and coefficients, and a product construction in which arbitrarily rare class overlap becomes nearly certain. The English manuscript and formal proofs are available for independent review. External peer review is pending. [Research paper](studies/masked-guidance/paper.pdf) · [Study and reproducibility](studies/masked-guidance/README.md) · [ICLR source](https://proceedings.iclr.cc/paper_files/paper/2026/hash/a14193e9d9fb0b03af0b717de1cac8ac-Abstract-Conference.html)

## Earlier graph catalogue study

This earlier publication addresses a machine-generated inequality. It is archived and contributes zero to the programme for human-posed open research problems. The files below describe that publication. [Archived v1.0.0 release](https://github.com/yoshi0703/ProofRush/releases/tag/v1.0.0)

### A cubic counterexample to AutoGraphForge conjecture 5ed263d5

A connected 14-vertex graph with degree three at every vertex has diameter **8** and vertex clique cover number **6**. Pastorek's 2026 candidate would require its diameter to be at most **7**. The witness disproves the universal inequality. [Original candidate, line 2530](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L2530) · [Catalogue paper](https://arxiv.org/abs/2609.03478)

The graph already occurs in the 1976 cubic census and in the 2007 family of Brand, Guiduli and Imrich. The result reported here is its application to the later conjecture. Two bridges force two specified vertices to lie eight edges apart. Six cliques cover the vertices, and a six-vertex independent set proves that any cover needs at least that many cliques. The English note includes a labeled diagram and the complete proof. [1976 census](https://pure.tue.nl/ws/files/1713766/252909.pdf) · [2007 construction](https://people.cs.uchicago.edu/~laci/students/guiduli.dir/barry-brand-imrich.pdf) · [Paper PDF](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

## Verification and priority

The negative answer can also be deduced directly from the older diameter result. A diameter path in the known 42-vertex graph has 15 disjoint edges. Those two-vertex cliques and the 12 remaining singletons show that its clique cover number is at most 27, although its diameter is 29. Our formal certificate works on the smaller 14-vertex graph and computes both invariants exactly. [Brand, Guiduli and Imrich](https://people.cs.uchicago.edu/~laci/students/guiduli.dir/barry-brand-imrich.pdf)

Lean 4.36.0 and pinned Mathlib verified both the printed conjecture's negation and its negation on connected graphs, the domain where the source evaluates diameter. An independently built Rust kernel, nanoda, checked all **7,184** exported declarations. The only axioms were the three standard Lean foundations. A separate Python implementation recovered the same diameter and the optimum clique partition. [Lean proof](lean/RegularCliqueCover.lean) · [Kernel record](lean/verification.json) · [Verification ledger](verification/ledger.md) · [Successful release verification](https://github.com/yoshi0703/ProofRush/actions/runs/45869007902) · [Publication record](verification/release.json)

The original catalogue marked the inequality proposed. Our searches of source data, prior counterexamples, graph catalogues, bibliographic indexes and public proof repositories located no prior refutation of this specific candidate. This is a formally checked research note about a machine-generated graph inequality. It has not received external peer review. [Priority audit](research-logs/priority.md)

## Discovery and reproduction

The research started at **17:00:14 UTC on 26 November 2026**. The first logged witness, including its edge list, distance eight and six-clique partition, appeared at **17:14:03 UTC**. One coordinating and three parallel Codex sessions used **gpt-6.2-astra**. The human requester supplied the brief and publication conditions. The agents selected problems, found the witness, checked earlier work, formalized the result and prepared the manuscript. GitHub published version 1.0.0 at **17:35:19 UTC**, about **35 minutes 5 seconds** after the initial request. At that time the counters showed 459 model responses and 63,017,380 tokens, including 61,870,464 cached input tokens. The subscription did not expose a dollar cost per response. No additional paid API or service was invoked. [Discovery record and usage](DISCOVERY.md) · [Prompts](prompts/research-assignments.md)

To reproduce both invariant values, run `python3 experiments/counterexample.py`. The complete kernel check and PDF build are described in [REPRODUCE.md](REPRODUCE.md). The release notes record the publication time, elapsed time, commit and hosted check. [Versioned release](https://github.com/yoshi0703/ProofRush/releases/tag/v1.0.0) · [Candidate comparison](research-logs/candidates.md) · [Research decisions](research-logs/record.md) · [Sources and recent results](references/research-assets.md)
