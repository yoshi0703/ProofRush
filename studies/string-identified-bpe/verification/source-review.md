# Independent review of the spelling-identified BPE counterexample

## Question and model

Baliga, Xie and Byju ask in Sections 8 and 11 whether the replacement-count guarantee of Theorem 13 survives when initial token spellings are not uniquely decodable. The guarantee concerns every greedy tie history. A rule names two current spellings and replaces their leftmost disjoint occurrences by their concatenation. The benchmark allows a comparator to choose any disjoint occurrences for each of at most $k$ rule applications. [arXiv:2611.08671v3, 23 November 2026](https://arxiv.org/html/2611.08671v3)

Appendix D introduces atoms as characters that may carry markers. Its mathematical non-unique-decoding examples have wider scope. It uses `ab` and `bc` as initial tokens inside rows, with distinct last letters, so these two tokens cannot both be bare characters with the same nonempty appended marker. The v3 supplement makes the domain explicit in `supplement/check/stringid/check_nonfree.py` (lines 3–9 and 68–85). It constructs rows of atom strings, uses ordinary concatenation as token identity, and tests arbitrary placements of `a`, `b` and `ab`. That is exactly the semantics of the example below. The example permits four arbitrary initial spellings. A specialization with one common suffix restricted to row ends remains outside this result. [Author supplement](https://doi.org/10.5281/zenodo.24451469)

## Results

Use the 14 initial tokens of lengths `8 4 2 1 1 8 2 2 4 4 4 8 8 8`, where length $j$ means the literal spelling $a^j$. The third token has the same spelling as the concatenation of the fourth and fifth tokens. The single stream has unit weight, and the budget is four.

| History | Pairs of spelling lengths | Per-rule savings | Total |
|---|---|---|---:|
| Admissible greedy | `(8,4), (12,2), (14,1), (15,1)` | `1, 1, 1, 1` | 4 |
| Full comparator | `(1,1), (2,2), (4,4), (8,8)` | `1, 2, 3, 4` | 10 |

The first history achieves maximum replacement count 1 at each step. The second history is also a valid greedy run with different first tie-breaking. Its first three merge outputs are identified with equal spellings already present in the row. The resulting gain ratio is $2/5< c_4=15/32$. A legal full comparator suffices to conclude the violation. The reported exact optimum, 10, is independently checked for both full and partial comparisons.

This also places the ratio below the uniquely decodable asymptotic constant, since $e^2>1+2+2=5$. The original theorem's pointwise shadow inequality already had non-unique-decoding counterexamples in Section 8. Appendix G reports the approximation ratio holding on its 15,086 non-unique-decoding checks covering budgets at most three. The supplement's `check_nonfree.py` uses the same budget limit. This witness uses budget four. The fresh-symbol approximation question of Kozma and Voderholzer is separate. [Baliga–Xie–Byju v3](https://arxiv.org/html/2611.08671v3) · [Kozma–Voderholzer](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ESA.2026.80)

### Uniquely forced greedy run

The 14-token witness already refutes an all-ties assertion. A longer single stream gives a unique maximizer at all four greedy steps. Take 40 copies of the witness followed by four auxiliary blocks. The auxiliary blocks are its prefixes of initial token lengths 2, 3, 4 and 5. Insert a different fresh separator character between each pair of blocks. No chosen pair contains a separator, and every pair containing a separator occurs at most once.

At step $i$ each main block contributes one occurrence of the chosen pair and at most one of any competitor. Each auxiliary block of length at least $i+1$ contains the chosen pair once under the same sequence of prior applications. The block of length exactly $i+1$ now has just the chosen pair, and shorter blocks have already become single tokens. Other pairs have at most one occurrence per remaining auxiliary block because each block is a prefix of the current main block. The chosen pair therefore wins strictly, giving savings $44,43,42,41$. The same full comparator saves $41,81,121,161$, giving greedy over optimum at most $170/404=85/202$. It also suffices to count only the 400 comparator savings in the main blocks, since $170/400=17/40 < (1-e^{-2})/2$ by $e^2>20/3$.

## Replay

Run from the study directory, one level above this verification record. The independent checker uses all ordered pairs of current spellings, including absent pairs. Its exact search considers all positive full applications and all pairwise-disjoint nonempty subsets for partial applications.

```sh
python3 verify_witness.py
python3 verify_unique_greedy.py
```

The pinned cross-check evaluates the authors' original `pairs_present`, `rep_count` and `full_scan_row` functions on both histories. It also calls their original `opt_table` and `c_ok` directly. The script checks the SHA-256 digest before importing the source from the ZIP. The saved transcript includes the authors' exact partial optima `[0, 1, 3, 6, 10]` for budgets zero through four.

```sh
curl -fsSL 'https://zenodo.org/records/24451469/files/tight-constant-supplement.zip?download=1' -o tight-constant-supplement.zip
python3 replay_author.py tight-constant-supplement.zip
```

ZIP SHA-256 `2bc232a3bab2b04035eec9be4bc4d788ea7d62d2b1d2d1ed3e90d97790680cdf`. The output files `verification/independent-replay.txt`, `verification/unique-greedy-replay.txt` and `verification/author-replay.txt` record the runs. Prior-art queries using the version ID, author names, the rational witness and non-unique-decoding terms yielded the cited source and benchmarks, with no earlier exact counterexample located in the searched results.
