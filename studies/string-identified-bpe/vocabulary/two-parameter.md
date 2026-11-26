# Worst-case ratio as a function of budget and initial vocabulary

For $k,A\ge1$, fix one of the two greedy rankings. Let $\rho_{k,A}$
be the infimum of $G/U$ over its full left-to-right greedy runs on
inputs with at most $A$ distinct initial token spellings and $U>0$.
The score is token savings, and $U$ is the best utility from at most
$k$ arbitrary disjoint partial rules. Ranks count either disjoint
replacements or raw adjacencies. All merges use literal
concatenation to assign the output identity. The infimum varies
the corpus and permits adversarial ties.

**Theorem.** For either ranking, over single words, and over weighted
word tables, there are absolute constants $c,C>0$ such that
\[
 c\min\{1,\max\{k^{-1/2},k/A^2\}\}
 \ \le\ \rho_{k,A}\ \le\
 C\min\{1,\max\{k^{-1/2},k/A^2\}\}.
\]
The upper construction works for every tie-breaking. For $A\ge2$ the same order holds when the infimum is restricted to genuinely ambiguous single words and ties are chosen in greedy's favor. Its initial
and merged spellings can use a sole underlying character. Consequently
a family reaching the fastest possible decay $O(k^{-1/2})$ needs
$\Omega(k^{3/4})$ initial spelling types, and there is one using
$O(k^{3/4})$ types. If $A=O(\sqrt{k})$, the ratio is bounded away
from zero. The theorem controls the ratio up to absolute factors;
it leaves finer questions about the deficit from one in that regime.

## Lower bound

The fixed-catalogue argument at cutoff $M=2$ gives
$G/U\ge 1/(3+2A^2/k)\ge \frac15\min\{1,k/A^2\}$. The disjoint
ancestry matching argument gives $G/U\ge(28+16k/s+8s)^{-1}$ for
any positive integer $s$. With $s=\lceil\sqrt{k}\rceil$, this is at
least $1/(60\sqrt{k})$. Take the maximum of the two lower bounds.
Both arguments apply with nonnegative real weights and early
exhaustion. [Fixed-catalogue proof](../paper.pdf) and
[ancestry matching proof](../verification/forest-review.md).

## Upper bound

Fix integers $m\ge1$ and $k\ge2m^2$. Put $L=\lfloor k/(2m)\rfloor$.
There are $L$ layers and $m$ possible seeds, independent of how large
$L$ gets. We first construct a literal-spelling word table and
then serialize it without increasing the leading order of the
number of initial spelling types.

### Layer labels

Select an itinerary $g_0,\dots,g_{L-1}$ with each ordered transition
$(g_j,g_{j+1})$ distinct, and with at most $q\le\sqrt{L}+2$ symbols.
For example, set $q=\lfloor\sqrt{L-1}\rfloor+2$. Restrict an Euler
circuit in the loopless complete directed graph on $q$ vertices to
its first $L$ vertices. The graph is connected and has equal
in-degree and out-degree at every vertex, and its $q(q-1)$ edges
suffice for this restriction.

Label the underlying unary spellings by their positive lengths. Let
\[
 B=2qm+1,\qquad H_j=(j+1)B,\qquad
 U_{j,i}=g_jm+i+1,\qquad V_{j,i}=B-U_{j,i}
 \qquad(0\le i<m).
\]
Use labels $g_j\in\{0,\dots,q-1\}$. The $U$-lengths lie in
$[1,qm]$, the $V$-lengths in $[qm+1,2qm]$, and the hub lengths
are distinct multiples of $B$. The intermediate length
$H_j+U_{j,i}$ lies strictly between $H_j$ and $H_{j+1}$.

For each $(s,x,y)\in\{0,\dots,m-1\}^3$, start with the one-token
row $[H_s]$. For $j=s,\dots,L-1$ in increasing order, surround the
current row on the left with $U_{j,i_j}$ and on the right with
$V_{j,i_j}$, where $i_j=x$ for even $j$ and $i_j=y$ for odd $j$.
These $m^3$ core rows have unit weight. Equal literal rows, if any,
count with multiplicity.

The possible initial core adjacency forms are
$(U_{j+1,i_{j+1}},U_{j,i_j})$,
$(U_{s,i_s},H_s)$, $(H_s,V_{s,i_s})$, and
$(V_{j,i_j},V_{j+1,i_{j+1}})$. Their four spelling ranges are
disjoint. In the first and fourth forms an ordered pair of group
labels identifies a unique adjacent layer transition, and the
label residues recover both $x$ and $y$ because adjacent layers
have opposite parity. Only the seed varies, so the raw count of that
pair is at most $m$. The middle forms pin the seed by the hub and
one of $x,y$ by the side label, leaving at most $m$ choices for the
other. Thus **every initial core pair has raw count at most $m$**.

A comparator visits layers in increasing order. For every variant
$i$ at layer $j$, it applies $(U_{j,i},H_j)$ and then
$(H_j+U_{j,i},V_{j,i})$. Every affected row advances from hub
$H_j$ to $H_{j+1}$ using these two replacements, since $U+V=B$.
Rows whose seed lies beyond $j$ still have their distinct seed
hubs greater than $H_j$. Rows seeded by $j$ or earlier already
have $H_j$ at the beginning of stage $j$, surrounded by the
correct two side tokens. As the variants are processed, their
temporary hub lengths are distinct inside the $j$-th band,
and a completed row has $H_{j+1}$. These facts prevent an
equal label $U_{j',i}$ at a nonadjacent layer from triggering
a replacement prematurely. The comparator can use full scans
and takes $2mL\le k$ rules, giving
\[
 U\ \ge\ 2m^2\sum_{s=0}^{m-1}(L-s)
 \ =\ m^3(2L-m+1)
 \ \ge\ m^3(L+1).
\]

### Private rules and shared guards

Choose $d=\lceil\sqrt{k}\rceil$ and take any $k$ distinct ordered
pairs from a $d$-by-$d$ left/right private grid. Use disjoint sets
of $d$ left and $d$ right lengths. Their sums are distinct and avoid
all initial types and all core comparator lengths. Explicitly, for
$0\le a,b<d$, use
\[
 P_a=(a+1)T,\qquad Q_b=(b+2)(d+1)T
\]
with integer $T>(L+1)B$. Distinct residues modulo $d+1$ after
dividing by $T$ distinguish the left index in a sum; the quotient
distinguishes the right index. Add one row $[P_a,Q_b]$ of weight
$m+1$ for each selected pair. In the table each unused private
pair scores $m+1$ under both rankings and any other pair scores
at most $m$. Once a private pair is used its outputs are
single-token rows and create no adjacencies. Inductively greedy
consumes exactly the $k$ private pairs in any order. Its gain is
$G=k(m+1)$. Since $k<2m(L+1)$ and $m\ge1$,
\[
 \frac{G}{U}<\frac{2(m+1)}{m^2}\le \frac4m .
\]

For a **single word**, expand each private row into $m+1$ physical
copies and insert a guard token between each pair of adjacent
rows. Use a palette of guards instead of one distinct guard per
position. Identify a guard resource as a pair of an orientation
(left or right of the guard) and a possible neighboring visible
spelling. A core row contributes just its fixed endpoint spelling
on each end. A private row can contribute either its original
endpoint or the sum spelling reached after its private merge.
Each guard position is incident to at most four resources.

The total incidence of any resource is at most
$\Delta=\max\{m^2,d(m+1)\}$. In the core, every outer endpoint is
a side label of the last layer and fixes one variant, with the seed
and the other variant free. On the private side, each original
endpoint belongs to at most $d$ distinct private pairs and their
$m+1$ copies, while a sum spelling belongs to just one such pair.
Core and private spelling bands are disjoint.

Take a palette of $4\lfloor\Delta/m\rfloor+1$ distinct unary
guard lengths above all private sums. Assign one guard color at
a time. At any resource at most $\lfloor\Delta/m\rfloor$ colors
have been used $m$ times already, and each position has at most
four such resources. A color remains available that has been
used fewer than $m$ times at every resource incident to that
position. The resulting coloring ensures that for **every**
subset of already chosen private rules, no guard adjacency has
raw count above $m$. No private or comparator rule can consume
a guard. Consequently the single-word comparator has the same
gain as the table comparator, and every single-word greedy run
still takes only private pairs. Both assertions apply when the
comparator is permitted arbitrary partial rules, because the
certifying sequence here consists of full scans.

### Translating the construction to $A$

The number of initial types is at most
$2qm+m+2d+4\lfloor\Delta/m\rfloor+1$: the only initial hubs
are those of the $m$ seeds. Using $q\le\sqrt{L}+2$,
$L\le k/(2m)$, $d\le2\sqrt{k}$,
$m\le\sqrt{k/2}$, and $\Delta\le4m\sqrt{k}$, this is at most
$30\sqrt{km}$. This count is for the guarded **single word**.
The word-table count excludes the guard term.

When $A\ge30\sqrt{k}$ and $k\ge2$, choose
\[
 m=\min\{\lfloor\sqrt{k/2}\rfloor,\ \lfloor A^2/(900k)\rfloor\}.
\]
This gives at least one variant, satisfies the budget constraints,
uses at most $A$ initial spelling types, and yields
$\rho_{k,A}\le4/m\le\max\{8\sqrt{2}/\sqrt{k},7200k/A^2\}$.
For a class requiring genuinely ambiguous words, use the large construction when $k\ge8$ and $A\ge60\sqrt{k}$. Both floor terms defining $m$ are then at least two. The triple $[U_{0,x},H_0,V_{0,x}]$ and the singleton $[H_1]$ are two actual input factors with the same spelling. In the remaining regimes the target expression is at least $1/3600$ or $1/\sqrt{8}$, so the trivial upper bound one suffices. A word with $2^{k+1}$ copies of the initial atom $a$ followed by the atom $aa$ is genuinely ambiguous and admits $k$ positive steps: after $j$ steps a token spans at most $2^j$ original atoms. Every full greedy history is available to the partial optimum. For the broader class permitting uniquely decodable words, a long repetition of a single atom also covers $A=1$.

## Reproduction

Run `python3 vocabulary_exponent.py` in this directory. It checks
bounds for every guard resource across all possible reachable decoy
states and runs exact left-to-right scans on the serialized words
at smaller budgets, checking the raw maximum and gain at every
chosen private step along one prescribed order and the full
comparator's gain. The proof gives the all-ties result. The
two-parameter theorem and shared-guard construction are manuscript
proofs. The unrestricted inverse-square-root bound and the fixed-vocabulary single-word bound used for the lower half have complete independent kernel certificates. The upper construction with the additional simultaneous cap on initial vocabulary is proved in this supplement and independently replayed. Its full generalization in both parameters has not yet received an end-to-end kernel check. [Kernel statements](../lean/Approximation.lean) · [Independent review](JointVocabularyReview.md).
