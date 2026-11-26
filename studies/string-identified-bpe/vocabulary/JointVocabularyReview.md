# Independent review: joint merge-budget and initial-vocabulary rate

Status: **no mathematical counterexample found**. The construction and the matching orders are supported by the counting argument below and by independent finite simulation; the new grouped-family upper bound is not claimed to have been kernel-verified by this review. The already established universal and bounded-vocabulary lower bounds can be cited only with their own hypotheses and proofs. The numerical implied constants below are absolute.

## Exact scope

Let R(k,A) be the infimum of G/OPT over finite input words whose initial *token spellings* have at most A distinct types, OPT>0, with at most k comparator partial merges and k greedy full merges; quantify over all tie choices. Treat premature termination by stopping/padding with zero-gain steps. Both replacement-count and raw-overlap greedy are considered. The same analysis allows arbitrary finite nonempty spellings; the construction here can be represented over a **single underlying letter** even though it has many distinct initial token spellings. Hence underlying alphabet size one does not mean initial vocabulary size A=1.

For sufficiently large k and A≥2 the proposed statement is

`R(k,A) = Θ(min(1, max(1/√k, k/A²)))`.

The lower side follows by combining the already verified `OPT ≤ 57 ceil(√k) G` with the bounded-initial inequality at M=2, `OPT ≤ P ≤ (3+2 A²/k)G`. These bounds refer to token count saved, not remaining encoded length. In the fixed-A regime this Θ-expression gives only Θ(1); it does not capture the sharper convergence to 1 or the already-known Θ(1/log k) worst deficit for fixed A≥2 in the atomic subclass.

## Grouped diamonds: comparator and core counts

Fix m≥2, L=floor(k/(2m))≥m. Let q be the least integer with q(q−1)≥L−1. A directed complete graph on q vertices without loops is Eulerian; take the first L−1 edges of an Euler circuit as consecutive group IDs g_0,...,g_(L−1). Thus g_j≠g_(j−1), and **ordered** transitions are all distinct. One has q=O(√L), including short edge cases.

Choose B=2mq+1, U_(j,i)=m g_j+i+1, V_(j,i)=B−U_(j,i), H_j=(j+1)B. These are positive unary spelling lengths. All U's are below all V's; all raw U,V lengths are <B; H_j and H_j+U_(j,i) lie in separate consecutive B-bands, the latter strictly between H_j and H_(j+1). Reuse of a U or V group at nonconsecutive levels is allowed. For seed s∈{0,...,m−1} and x,y∈{0,...,m−1}, start with [H_s] and, at each level j=s,...,L−1, put U_(j,i_j) on the left and V_(j,i_j) on the right, i_j=x for even j and y for odd j. Take all m³ rows, including duplicate spellings as distinct occurrences.

Initially every core ordered pair occurs at most m times, even under raw overlapping counts:

* Every seed-adjacent pair contains H_s, so identifies s and one of x,y; the other has m possible values.
* Every non-seed pair is U_j U_(j−1) or V_(j−1) V_j. Its two groups determine the directed itinerary transition and hence j. Because consecutive levels have opposite parity, its two subindices determine x and y; at most m seeds remain. Different orientations or the U/V ranges cannot collide. Consecutive group IDs differ, so these pairs are not self-loops.

At each level j process rules `(U_(j,i),H_j)` for all i, followed by `(H_j+U_(j,i),V_(j,i))` for all i. By induction the center of each row seeded at s≤j is H_j before this level. The fresh B-band separation shows no other hub or core leaf can accidentally match these operands. Both operations fire once for each active row, for exactly `2m² ∑_(s=0)^(m−1)(L−s) = m³(2L−m+1)` savings using 2mL≤k rules. Repetitions of group IDs do not disturb the level-specific hub. This proof uses full rules, so it is a valid lower bound for either full- or partial-rule comparator optimum.

## Private grid and guard palette

Let n=ceil(√k). Introduce disjoint private token types p_1,...,p_n, q_1,...,q_n and choose any k different ordered grid pairs (p_i,q_j). Add m+1 copies of each two-token block. A private pair has exactly m+1 nonoverlapping occurrences, and its replacement type p_iq_j identifies (i,j). Types p_i, q_j and their pair products can be made disjoint from all core and guard types by assigning their unary spelling lengths distinct powers of 2 larger than every core hub and intermediate. The two exponent ranges for p's and q's are disjoint, so all p_i+q_j are distinct and are not singleton powers of 2. Guard tokens get additional distinct powers of 2. The enormous underlying character lengths do not affect initial **type count**; they would matter under an extra bounded-spelling-length constraint, which is not part of this model.

Serialize all nonempty core and private blocks in any order, placing one guard token at each inter-block boundary. Each block endpoint has one possible state if core and at most two if private (unmerged endpoint or merged p_iq_j). Keep separate resource orientations: `(endpoint,guard)` and `(guard,endpoint)`. Every core endpoint type has at most m² occurrences: each is indexed by its outermost variant, with m seeds and m choices for the other variant. Every private endpoint has at most (m+1)n occurrences; a collapsed private endpoint has only m+1. Hence let `D=max(m²,(m+1)n)`.

Choose guard colors greedily while processing boundaries. A color is forbidden if it has already been used m times with any of the at most four possible oriented endpoint resources of that boundary. Each resource rules out at most floor(D/m) colors, so a palette of `1+4 floor(D/m)` colors suffices. Because L≥m implies m≤√(k/2), the palette has O(√k) types. For every possible subset of selected decoy pairs, each guard-contact ordered pair has raw count ≤m. There are no guard-guard contacts, and core internals never change during the decoy phase. Therefore all and only unselected private pairs attain raw count m+1; each also yields m+1 disjoint replacements. Every greedy tie sequence selects all k private pairs and saves exactly k(m+1). The argument holds for arbitrary selection orders, not just the simulated orders. Comparator rules cannot touch guard/private tokens because the operand spelling ranges are disjoint.

Core initial types number at most 2mq+m; private types at most 2n; guard types at most `1+4D/m`. Altogether this is `O(m√L+√k+m) = O(√(km))`. The ratio against the explicit comparator is

`k(m+1) / [m³(2L−m+1)] = O(1/m)`,

uniformly for L≥m and k<2m(L+1). For A at least a suitable absolute multiple of √k, choose `m=Θ(min(√k,A²/k))`, rounding down with a sufficiently small absolute constant so the entire vocabulary fits A and L≥m. This gives the proposed interpolating upper bound. If A is smaller than that threshold, the target expression is bounded below by a positive absolute constant, and the trivial upper bound R≤1 is enough.

## Ambiguity and edge cases

For m≥2 the large-family input is genuinely non-uniquely decodable in the source's factor sense: the initial row with seed 0 contains the contiguous central triple `U_(0,x), H_0, V_(0,x)`, spelling H_1; H_1 itself occurs in a different seed-1 row. The spellings coincide while the atom sequences differ. In the small-A regime the trivial upper witness can also be genuinely ambiguous with just two token types, e.g. `[a,a,aa]`: `[a,a]` and `[aa]` are both factors, and OPT>0. For an exactly-k-positive-step convention, lengthen the run of initial a's to $2^{k+1}$ as in the supplement. The exact definition of “ambiguous” matters because an unbounded-alphabet upper example is not itself a fixed-A construction.

A source-level theorem still needs to quantify explicitly over the resource colors, early greedy stopping, arbitrary tie histories, integer rounding, and comparator budget. Simulations alone do not establish those obligations. In particular, if a theorem restricts the initial underlying character alphabet, the number/length of markers, or the permitted input representation, the applicability of the unary powers-of-two recoding must be rechecked.

## Independent checks

`check_joint_vocabulary.py` constructs the Euler itinerary, unary numeric token spellings, private grid, reusable guard coloring, and the serialized input from scratch. It actually executes the comparator's 2mL full scans and checks the exact claimed gain; it verifies raw counts at every private greedy step under three shuffled orders for each of 60 (m,L,remainder) settings, totaling **180 cases**. It separately enumerates all **256 subsets** of private choices for m=2,k=8, checking every resulting history state and available pair counts. This is a bounded test, not a proof that the asymptotic construction or source quantifiers have been formalized.
