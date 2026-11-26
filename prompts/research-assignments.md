# Research instructions and roles

The original problem-finding prompt is recorded in [initial-request.txt](initial-request.txt). The requester subsequently specified a publication protocol for a checked discovery. It required an English manuscript, a clean Lean build, independent scrutiny of the statement and prior art, a public GitHub release with its PDF and a hosted proof check. Human contributions were the research objective, source suggestions, operating constraints and permission to publish qualifying results. No human supplied a candidate graph or a proof.

The following are condensed English descriptions of the actual assignments. All four sessions used Codex with gpt-6.2-astra at maximum reasoning effort. The discovery and verification sessions used the same model, with separate assignments and different computational checks.

|Session|Research instruction|
|---|---|
|Coordinator|Read the specified research assets, rank public conjectures, compare proof and counterexample routes, test candidate priority independently, and record discarded leads. Calculate both graph invariants by a separate algorithm. Audit the literal catalogue formula and the connected evaluation domain.|
|Graph research|Find a publicly posed graph problem admitting counterexample search. Check the original invariant conventions and try explicit connected witnesses. Search published papers, source commits and prior counterexamples. Provide an edge set and check numerical certificates.|
|Sequence research|Seek a separate tractable public combinatorial problem. Derive recurrences or boundary-state arguments, formalize candidate proofs and compare the results with recent public solutions.|
|Lean verification|Set up pinned Lean and Mathlib, translate the target independently, verify every claimed numerical relation, inspect axiom dependencies, and replay the exported proof with an independent kernel. Recheck the separate interpretation on connected inputs.|

The conductor adopted the division between exploration, adversarial verification and cross-round evidence retention from Cogentic. Its Appendix A specifies exact objectives and quantifiers and gives the verifier a concrete success condition. The graph task followed that pattern by fixing the original data row, both meanings of the diameter domain, and the exact inequality a witness must violate. [Cogentic, Sections 2–3 and Appendix A](https://arxiv.org/html/2609.40324v2#A1)
