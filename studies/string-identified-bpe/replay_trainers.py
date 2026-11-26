"""Optional versioned replay on one ASCII word, using each library's own trainer."""
import argparse
from importlib.metadata import version
from io import StringIO

WORD = 'a' * 64


def hugging_face():
    from tokenizers import Tokenizer
    from tokenizers.models import BPE
    from tokenizers.trainers import BpeTrainer

    sizes = []
    for merges in range(5):
        tokenizer = Tokenizer(BPE())
        tokenizer.train_from_iterator(
            [WORD], BpeTrainer(vocab_size=1 + merges, min_frequency=2, show_progress=False)
        )
        tokens = tokenizer.encode(WORD).tokens
        assert ''.join(tokens) == WORD
        sizes.append(len(tokens))
    assert sizes == [64, 32, 16, 8, 4]
    print(f'Hugging Face tokenizers {version("tokenizers")}, no pre-tokenizer or boundary marker: {sizes}')


def subword_nmt():
    from subword_nmt.apply_bpe import BPE
    from subword_nmt.learn_bpe import learn_bpe

    codes = StringIO()
    learn_bpe(StringIO(WORD + '\n'), codes, num_symbols=4, min_frequency=2)
    sizes = []
    for merges in range(5):
        codes.seek(0)
        tokenizer = BPE(codes, merges=merges, separator='')
        tokens = tokenizer.segment_tokens([WORD])
        assert ''.join(tokens) == WORD
        sizes.append(len(tokens))
    assert sizes == [64, 33, 18, 11, 8]
    print(f'subword-nmt {version("subword-nmt")}, library end-of-word handling: {sizes}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('implementation', choices=['huggingface', 'subword-nmt'])
    args = parser.parse_args()
    (hugging_face if args.implementation == 'huggingface' else subword_nmt)()
