# Verified statements

|Claim|Witness or independent check|
|---|---|
|The graph is a simple graph on 14 vertices and every degree is three|Finite edge relation and degree computation in `graph_cubic`|
|It is connected|Strictly descending integer distances to vertex 7 in `graph_connected`|
|Its diameter is eight|A length bound via vertex 7 and a one-Lipschitz integral labeling separating vertices 2 and 11 in `graph_diam`|
|Its vertex clique cover number is six|A six-coloring of the complement and an injection from six pairwise adjacent complement vertices into every coloring in `graph_cover`|
|The candidate fails for its printed graph class and on the connected evaluation domain|Two target negations with exact-type checks and a complete independent export audit|
|The calculation is independent of the proof code|Python constructs the graph block by block, computes all distances and minimizes the clique partition by exact subset recursion.|

The three standard Lean foundations observed in both results were propositional extensionality, classical choice and quotient soundness. The verifier rejects any other axiom in the exported dependencies. [Source](../lean/RegularCliqueCover.lean) · [Independent checker output](../lean/nanoda-audit.txt) · [Machine-readable verification](../lean/verification.json) · [Python output](witness.json)
