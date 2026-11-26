# Which BPE guarantee does this result address?

The solved question is whether the replacement-count lower bound of Baliga, Xie and Byju survives when the initial sequence has ambiguous token spellings and any two tokens with the same string share their identity. The four-merge counterexample answers that question. The following comparison changes one assumption at a time. [Source, Sections 8, 9 and 11](https://arxiv.org/html/2611.08671v3) · [Independent proof of the finite refutation](lean/FourMerges.lean)

| Initialization and rule | Result after four merges on the same underlying 64 ASCII letters |
|---|---|
| Fourteen prescribed tokens spelling 1, 2, 4 or 8 copies of `a`. Rank by the maximum number of disjoint replacements. | One legal greedy history saves 4 tokens. An exact optimum saves 10. The proposed fraction of optimum, 15/32, fails. |
| Same fourteen tokens. Rank by all adjacent occurrences, allowing overlapping observations. | Every legal greedy tie history saves 5, giving 5/10. The first proposed adverse pair (8, 4) scores 1, while (4, 4) and (8, 8) both score 2. |
| Sixty-four separate copies of the character `a`. Rank by disjoint replacements or by all adjacent occurrences. | Both rules perform the same four doublings, saving 32, 16, 8 and 4. The four final tokens each spell sixteen letters. This reaches the optimum of 60 savings. |
| Hugging Face `tokenizers`, versions 0.21.0 and 0.23.3, trained on that single 64-character word, with no pre-tokenizer or boundary marker. | With zero through four learned merges the encoded lengths are 64, 32, 16, 8 and 4. |
| `subword-nmt` 0.3.8, trained on the same word with its ordinary end-of-word handling. | With zero through four learned merges the encoded lengths are 64, 33, 18, 11 and 8. |

The witness has one underlying letter and four distinct *initial token spellings*. With character initialization every initial token has length one. After j partial or full merge rules the longest possible token has length at most 2^j, since each new token concatenates two current tokens. Consequently every four-rule comparator needs at least four tokens to spell this 64-character word.

The two library rows use a single corpus word and a minimum frequency of two. ASCII characters coincide with their bytes on this input. Each library applies its native BPE trainer. The Hugging Face call uses a vocabulary budget of one initial symbol plus the stated number of merges. The subword-nmt call trains four rules and applies the first zero through four, preserving its default end-of-word symbol. These measurements concern this input only.

## What is known about the separate guarantees?

The replacement-count theorem applies to ordinary character or byte atoms under the authors' assumptions. For overlapping-frequency greedy, Proposition 20 gives a universal lower bound greater than 0.38954 and a construction approaching approximately 0.40407 from the upper-bound side. The latter construction uses a growing alphabet. Extending the 2/5 lower bound beyond the source's short-optimum-token condition is open in that source. Fixed byte alphabets and trained tokenizers with preprocessing or special-token policies have additional restrictions. [Original bounds and their scope](https://arxiv.org/html/2611.08671v3#S9)

The six-phase construction in v3.0.0 gave an upper bound of 1/6 on the large-budget worst-case ratio under the best tie order. That release contained a complete formal finite counterexample and component proofs for the six-phase family. The original one-sixth family now has an end-to-end formal proof on single inputs. A subsequent two-sided construction identifies the large-budget limit as **zero** for both mathematical ranking rules with arbitrary compound initial spellings. For every positive tolerance and all sufficiently large budgets, one admissible input forces every greedy run below the tolerance times its partial optimum. The formal limit takes the infimum across inputs after maximizing over ties. The exact ratio at an individual finite budget and the matching rate of decay are open in this study. [Original v3.0.0 verification scope](https://github.com/yoshi0703/ProofRush/blob/v3.0.0/studies/string-identified-bpe/VERIFY.md) · [New limit theorems](lean/DiamondResult.lean) · [Proof and finite instance](paper.pdf)

The new construction can have only one underlying letter. At budget 338 its unary replay uses 7,617 initial token types to prescribe the segmentation of 159,298,694 copies of that letter. Ordinary character training on those letters starts with one type and a completely different sequence of initial tokens. The formal construction uses distinct guard characters, and the one-letter recoding has a mathematical proof and an independent exact replay. [Unary replay](check_unary_diamond.py) · [Recorded output](verification/diamond-unary-13.json)

## A native trainer on one byte-initialized input

On a separate 892,941-byte ASCII input containing 65 byte values, Hugging Face Tokenizers 0.21.0 trained from all 256 byte types. With the ByteLevel prefix and regex splitting disabled, encoding the single input after 60 learned merges saved **122,332 tokens**. A legal 60-rule comparator on the identical bytes saved **283,050**, so the observed ratio to optimum is at most **3598/8325**, about 0.43219. This is slightly below the replacement-count guarantee's large-budget constant of about 0.43233. The native trainer ranks by overlapping occurrences. Its result therefore answers a different question from the theorem on disjoint ranking, and the exhibited comparator gives an upper bound above 2/5. The zero-limit example uses an entirely different initialization.

The byte input uses the four-phase block patterns of Baliga, Xie and Byju with newly selected integer multiplicities. This is an implementation experiment on a finite specialization of their construction. The archive contains the exact input compressed with gzip, the rules learned by the library, the full comparator rules and a standard-library checker. It verifies raw maximality along the recorded run and recomputes both savings. An optional native rerun checks the pinned library. [Source construction](https://arxiv.org/html/2611.08671v3#A5.SS3) · [Exact data and replay](byte-replay/) · [Recorded library result](byte-replay/trainer-output.json)

## Reproduction

The mathematical comparison uses only Python's standard library. The optional library commands below use two fresh Python 3.12 virtual environments. [Exact mathematical replay](check_scope.py) · [Library replay](replay_trainers.py) · [Recorded output](verification/scope-replay.txt)

```bash
python3 studies/string-identified-bpe/check_scope.py
replay_dir="$(mktemp -d)"
python3.12 -m venv "$replay_dir/original"
"$replay_dir/original/bin/python" -m pip install tokenizers==0.21.0 subword-nmt==0.3.8
"$replay_dir/original/bin/python" studies/string-identified-bpe/replay_trainers.py huggingface
"$replay_dir/original/bin/python" studies/string-identified-bpe/replay_trainers.py subword-nmt
python3.12 -m venv "$replay_dir/recent"
"$replay_dir/recent/bin/python" -m pip install tokenizers==0.23.3
"$replay_dir/recent/bin/python" studies/string-identified-bpe/replay_trainers.py huggingface
```


To replay the byte-initialized experiment, run the following from the repository root. The last command uses the original-version environment created above.

```sh
python3 studies/string-identified-bpe/byte-replay/replay.py
"$replay_dir/original/bin/python" studies/string-identified-bpe/byte-replay/replay.py --huggingface
```
