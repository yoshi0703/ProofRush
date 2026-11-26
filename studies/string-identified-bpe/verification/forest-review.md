# Independent audit of the square-root rate

In the same literal spelling model, allow arbitrarily many initial
spellings. For integer $s\ge1$, every $k$-step greedy history with
total gain $G$, under either ranking, satisfies
$$
 U\le (28+16k/s+8s)G ,
$$
where $U$ is the gain of any comparator using at most $k$ disjoint
partial rules. Setting $s=\lceil\sqrt{k}\rceil$ gives a universal
$\Omega(k^{-1/2})$ ratio. Early exhaustion gives $G=P\ge U$.
The proof applies to nonnegative weighted word tables, with no parsing
hypothesis on initial labels.

**Matching charge.** Fix a family of disjoint original adjacency edges,
with mass $D$, using at most $q$ literal pair types. If $q=0$
then $D=0$. Otherwise, at most two as yet untouched matching edges
are touched by an actual greedy replacement, one per consumed singleton
endpoint. Every untouched edge still has both of its original tokens,
which remain adjacent. At time $t$, the actual next greedy gain is
therefore at least $(D-2G_t)/(2q)$ under either ranking: raw
maximality gives the count directly up to a factor of two, and replacement
maximality can compare with the count of a raw maximizer, or use a
disjoint matching of that type directly. Thus $D\le(2+2q/k)G$.
All mass inequalities are rowwise before applying weights.

**Comparator forest.** Attach one binary internal node to every
comparator replacement occurrence, with stage label equal to its rule
index. The forest trees are over the original leaves, in their original
order. A cherry has two leaf children, a branch node has two internal
children, and a unary node has one of each. Write $C,B,W$ for their
respective total masses. Then $U=C+B+W$ and $B\le C$, since
discarding original leaves and suppressing unary nodes gives a full
binary forest with cherries as leaves. This works per row before
weighting. Distinct cherries are disjoint original adjacency edges
and have at most $k$ types, one per stage. Thus $C\le 4G$.

Group unary nodes into maximal chains of child-linked unary nodes.
Each chain is uniquely identified by the first cherry or branch
descendant immediately below it, so their mass is at most $C+B\le2C$.
A chain absorbs new original leaves one at a time on either side
of its growing contiguous token span. The leaves attached consecutively
on the left are adjacent original positions, as are consecutive right
attachments. Interleaved opposite-side stages cannot add a position
on the side being considered. Descendants of a branch cannot interrupt
a unary chain, nor insert an original position between its same-side
attachments. Leaves attached to one chain and side cannot belong to
another chain or side.

Each nonempty side sequence accounts for one first leaf and then one
edge for each successive leaf. There are at most $4C$ first leaves by
mass. Along each side the stage labels increase strictly (replacements
of the same rule act on disjoint intervals simultaneously), so at
most $k/s$ edges per side can have a stage gap greater than $s$.
The mass of these long-gap edges is at most $4Ck/s$. The other
edges are called short-gap, and their pair types are determined
by the two stages and a left/right bit: the corresponding rule
operand on that side is the attached original atom's literal label.
There are at most $2ks$ short-gap types. On each side the short-gap
edges form disjoint paths or subpaths on the side sequence and admit
a matching of at least half their mass. This selection preserves the
bound on types, so if $E$ is all short-gap edge mass then
$E/2\le(2+4s)G$. Consequently
$$
 U=C+B+W
 \le 6C+4Ck/s+E
 \le (28+16k/s+8s)G.
$$

All arguments concern actual original leaf ancestry. A visible token
with a literal spelling equal to a preexisting atom still has the
ancestral block created by its actual replacements, and the two
arguments that use original edges refer to original leaves, rather
than visible spelling implying any particular provenance.

The model uses the paper's Appendix D literal-output rule, and admits
the comparator forest used by the fresh-model proof. The latter's
constant-factor shadow inequality relies on unique decoding when
transferred to spelling identity. The bound here uses only cherries
and adjacent same-side attachments and requires no shadow theorem.
[Baliga–Xie–Byju v3, §8 and Appendix D](https://arxiv.org/html/2611.08671v3#S8)
The fixed-alphabet companion uses short pairs counted by initial
alphabet powers and treats fresh token types in §2. These hypotheses
and the asymptotic regime are different. [Companion v3, §6](https://arxiv.org/html/2611.07346v3#S6)
