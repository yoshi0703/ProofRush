"""Replay one 60-merge training run on ordinary bytes and a legal comparator."""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import gzip

HERE = Path(__file__).resolve().parent
SHA256 = "6f6e24e1438d6bb5a0926c9f5ef79b665c68c33c294f1f5ed103642b6e5f37a6"


def program(name):
    rules = []
    for line in (HERE / name).read_text().splitlines():
        phase, left, right = map(int, line.split())
        rules.append((phase, chr(left), chr(right)))
    assert len(rules) == 60
    return rules


def score(text, rules, require_maximum):
    word = text
    for step, (_, left, right) in enumerate(rules):
        if require_maximum:
            raw = Counter(zip(word, word[1:]))
            assert raw[left, right] == max(raw.values())
        # A fresh non-ASCII character tracks the token of this step. All
        # rule operands in these two explicit scripts are original ASCII.
        updated = word.replace(left + right, chr(256 + step))
        assert len(updated) < len(word)
        word = updated
    return len(text) - len(word)


def native(text, rules):
    import tokenizers
    from tokenizers import Tokenizer, models, pre_tokenizers, trainers
    assert tokenizers.__version__ == '0.21.0'
    alphabet = pre_tokenizers.ByteLevel.alphabet()
    tokenizer = Tokenizer(models.BPE())
    tokenizer.pre_tokenizer = pre_tokenizers.ByteLevel(add_prefix_space=False, use_regex=False)
    trainer = trainers.BpeTrainer(vocab_size=316, initial_alphabet=alphabet,
                                  min_frequency=1, show_progress=False)
    tokenizer.train_from_iterator([text], trainer=trainer, length=1)
    import json
    learned = json.loads(tokenizer.to_str())['model']['merges']
    pairs = [tuple(x.split(' ') if isinstance(x, str) else x) for x in learned]
    phase = {(a, b): n for n, a, b in rules}
    assert len(pairs) == 60 and set(pairs) == set(phase)
    steps = [phase[pair] for pair in pairs]
    assert steps == sorted(steps)
    measured = len(text) - len(tokenizer.encode(text, add_special_tokens=False).ids)
    assert tokenizer.get_vocab_size() == 316 and measured == 122332
    print(f"Hugging Face {tokenizers.__version__}, one pretoken, 256 initial byte types, "
          f"{len(learned)} merges, {measured} tokens saved.")


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--huggingface', action='store_true')
    args = parser.parse_args()
    original = gzip.decompress((HERE / 'training-bytes.gz').read_bytes())
    assert sha256(original).hexdigest() == SHA256
    assert len(original) == 892941 and len(set(original)) == 65
    text = original.decode('ascii')
    rules = program('trainer-rules.tsv')
    greedy = score(text, rules, True)
    comparator = score(text, program('comparator-rules.tsv'), False)
    assert (greedy, comparator) == (122332, 283050)
    print(f"{len(original)} bytes, {greedy} greedy savings, {comparator} comparator savings, "
          f"ratio at most {Fraction(greedy, comparator)}.")
    if args.huggingface:
        native(text, rules)
