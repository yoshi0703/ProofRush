# Independent mathematical review of Canonne Q2

**Verdict.** The submitted proof of the two-sided comparison is correct. Its main theorem supplies both inequalities of the author's MathOverflow equation (4) directly, including the displaced radii, and provides sufficient mathematical grounds to treat it as an answer to the research question named in COLT 2024, §5. Any novelty claim still depends on the separate priority search and the author has yet to evaluate it. Q2's published reward is an extra-large wombat plush toy. [MathOverflow statement and comments](https://mathoverflow.net/questions/332062/relation-between-two-different-functionals-lvert-p-max-varepsilon-rve) · [COLT 2024, §5](https://proceedings.mlr.press/v247/canonne24a/canonne24a.pdf).

## Quantitative source match

The MO cutoff keeps the entire smallest prefix with mass at least \(1-e\) then removes the first coordinate. Its index \(k\) is one greater than the proof's \(N_e\) for \(0<e<1\). It does not split a boundary atom. The MO inverse targets \(1-e\). COLT simplifies the displayed BCG quantity by using target \(1-2e\). A relabeling \(e\mapsto2e\) is required before interpreting the same bounds there. The inverse uses signed \(\ell_1+\ell_2\) decompositions as in the source. On its explicitly claimed range, the theorem implies
\[
1\vee F(9e)\le 1\vee D(e)
\quad\text{and}\quad
1\vee D(e)\le \frac{39}{31}\left(1\vee\frac{F(e/32)}e\right)
\qquad (0<e<1/9).
\]
For the right inequality, \(D(e)\le1+(8/31)F(e/32)/e\) and the displayed constant then follows. If one also wants the rough MO question's version without the baseline under a small-\(\ell_2\) assumption, \(\|p\|_2\le 1/2\) suffices in the eq. (4) range. Indeed \(D(e)\ge(1-e)/\|p\|_2>1\) and \(F(e/32)\ge 1-e/32-p_1>e\). At the unused endpoint \(e=1\), \(F(1)=D(1)=0\) under \(K(0)=0\). The target \(e=0\) is outside the source range.

## Proof checks

- **Attainment.** For any witness \(0\le z_i\le1\), the bound against every signed decomposition gives the inverse upper bound. For the waterfilled \(z_i=\min(1,hp_i)\), continuity under the summable dominating sequence \(p\) provides finite \(h\) hitting the exact target. The decomposition \(b_i=z_i/h,\ a_i=p_i-b_i\) has \(0\le a\le p\), \(b\in\ell_2\), and \(a_i z_i=a_i\) on every coordinate, including a tie at saturation. At shorter lengths its cost strictly misses the target. This argument establishes countable support without any finite-limit interchange in the optimization.
- **Lower bound.** The minimality of \(N_e\) gives \(\sum_{i<N_e} p_i<1-e\), including when \(e\) equals one of the original tails at \(N_e\). If \(N_e>1\), then \(p_{N_e}>0\). Multiplying by \(p_{N_e}^{-1/3}\) prices the lost head mass and gained tail mass in opposite directions. Hölder with exponents \(3/2,3\) then gives the written bound on \(\sum p_i^{2/3}z_i\), even when \(\sum p_i^{2/3}=\infty\). The uniform laws give \(F(e)/D(e)\to\sqrt{1-e}\) in growing dimension, and then \(e\downarrow0\) proves the coefficient.
- **Upper bound.** The chosen witness \(z_i=\min(1,p_i^{1/3}/\lambda)\) succeeds because every retained nonmaximum loss is \(p_i^{2/3}x(1-x/\lambda)_+\le p_i^{2/3}\lambda/4\). Equality in this scalar bound occurs at \(x=\lambda/2\). A separate direct witness \(z_i=(1-(e-s)/(S p_i^{1/3}))_+\), with the same protected largest entry and \(S=\sum_{i=2}^{N_s}p_i^{2/3}\), gives the same constant by \((1-u)_+\le1/(4u)\). This provides an independent algebraic check. The \(S=0\) case requires only the largest coordinate.
- **Upper sharpness.** At fixed \(s,e\) with \(2e-s<1\), the proposed three-block family has \(H>0\), eventually ordered atoms and an exact cutoff at the end of its second block. The third block's captured mass is bounded by \(s\|z\|_2/\sqrt M\). With \(M=m^2\) it cannot change the asymptotic coefficient. Splitting the first block into fixed \(L\) gives a constant contribution to \(F(s)^{2/3}\) and makes its \(\ell_2\)-norm as small as prescribed. Taking \(m\to\infty\) proves sharpness also within any fixed positive \(\ell_2\) ceiling. One can choose \(e=1/20,\ s=1/40\) to keep both radii in the original comparison range.
- **Same-radius obstruction.** The \(m^{-1/3}\) captured tail mass requires \(\Omega_e(m^{1/6})\) norm. Its minimal retained prefix contributes \(O_e(1)\) to \(F(e)^{2/3}\) because each tail contribution scales as \(m^{-2/3}\), while the needed number retained is \(O_e(m^{2/3})\). Keeping \(L\) fixed during \(m\to\infty\) both bounds the head contribution and allows any prescribed norm ceiling after choosing \(L\) large enough.

## Independent arithmetic checks

[check.py](check.py) uses exact rational arithmetic. It represents atom probabilities as normalized integer cubes, so both the squared truncated quasinorm and squared minimum norm are rational. The latter is computed by locating the saturated prefix and solving its remaining linear mass equation. It checked 1,000 seeded finite laws and 20 explicit equal-tail cutoffs, including ties and zero entries. The script separately checks the countably infinite law with \(4^j\) atoms of weight \(2^{-3j}\) for \(j\ge1\). The untruncated sum of \(2/3\)-powers diverges for this law, while its inverse and truncated sums at the chosen positive radii have exact rational squares. These checks support the analytic proof and do not certify priority.

The final manuscript includes the canonical MathOverflow link, the inverse endpoint and the explicit COLT normalization.
