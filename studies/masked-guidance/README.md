# When classifier-free guidance favors shared outputs in masked discrete diffusion

He, Rojas and Tao asked whether stronger guidance favors outputs exclusive to the target class, taking account of exclusivity of both words and their projections. Their problem first appeared on 12 June 2025 and was retained as Conjecture E.1 at ICLR 2026. We give a counterexample, an explicit construction with arbitrarily strong reversal, and a limiting law for the exact finite-dimensional sampler. The results concern exact scores, a fully masked start and fixed guidance strength. This research note has not received external peer review. [Original ICLR paper](https://proceedings.iclr.cc/paper_files/paper/2026/hash/a14193e9d9fb0b03af0b717de1cac8ac-Abstract-Conference.html) · [Research paper (PDF)](paper.pdf) · [TeX source](paper.tex)

| Quantity | Ordinary target | Guided mass |
|---|---:|---:|
| Shared word in the two-bit example | 3/4 | 63/80 at strength one; tends to 1 |
| Shared word in the three-bit example | 3/4 | 171/208 at strength one; tends to 1 |
| Shared event in the three-bit independent target | 2.9701% | At least 99.9790% and below 99.9791% at strength 50 |
| Shared event in the two-coordinate ternary variant | 1.99% | At least 99.9988% and below 99.9989% at strength 50 |

In the two-bit example the target produces 00 and 11 with probabilities 1/4 and 3/4. The competing class is uniform on 01, 10 and 11. A first 1 is stronger evidence of membership in the target class than a first 0. The target then forces the second token to agree with the first. As a result, guidance favors the shared word 11. This contradicts both the specified two-dimensional privacy ordering and the limiting-support conclusion of Proposition 3.3(2). Our project counts this as one research question.

For a general finite class mixture, each possible reveal has a target-class posterior. Strong guidance selects the highest-posterior next reveal, resolving ties with the target token probabilities. A word retains mass precisely when some reveal order consists entirely of maximizing choices. The sum of local log-posterior gaps also determines the exact exponential rate and leading coefficient for every positive-target word. A dynamic program computes the answer using subsets of coordinates and exact rational comparisons. The product family in the table shows that even initially rare overlap can become nearly certain. [Proofs and algorithm](paper.pdf) · [Exact algorithm](leading_terms.py)

The project used one coordinating Codex session and three research agents. The human requester set the scientific and release criteria. The research record describes the division of work, rejected ideas, independent checks and limits of the priority search. [Record](RESEARCH.md) · [Formal and computational verification](VERIFY.md) · [Reproduction](REPRODUCE.md)
