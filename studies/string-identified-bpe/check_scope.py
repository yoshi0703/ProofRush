"""Compare initialization and pair ranking on the same 64 ASCII characters."""
from collections import Counter
from functools import cache

from verify_witness import leftmost, occurrences, optimum, replace


INITIAL_LENGTHS = (8, 4, 2, 1, 1, 8, 2, 2, 4, 4, 4, 8, 8, 8)
WORD = 'a' * sum(INITIAL_LENGTHS)


def scores(tokens, overlapping):
    pairs = Counter(zip(tokens, tokens[1:]))
    if overlapping:
        return pairs
    return {pair: len(leftmost(occurrences(tokens, pair))) for pair in pairs}


@cache
def final_lengths(tokens, budget, overlapping):
    if not budget or len(tokens) < 2:
        return frozenset([len(tokens)])
    counted = scores(tokens, overlapping)
    maximum = max(counted.values())
    sizes = set()
    for pair, score in counted.items():
        if score == maximum:
            updated = replace(tokens, leftmost(occurrences(tokens, pair)))
            assert ''.join(updated) == ''.join(tokens)
            sizes.update(final_lengths(updated, budget - 1, overlapping))
    return frozenset(sizes)


def main():
    initial = tuple('a' * k for k in INITIAL_LENGTHS)
    assert ''.join(initial) == WORD
    raw = scores(initial, True)
    adverse = ('a' * 8, 'a' * 4)
    winners = sorted((len(a), len(b)) for (a, b), n in raw.items() if n == max(raw.values()))
    assert raw[adverse] == 1 and max(raw.values()) == 2 and winners == [(4, 4), (8, 8)]
    print(f'Compound tokens, overlap ranking: first maximum 2 at {winners}; (8, 4) scores 1.')
    raw_savings = {len(initial) - n for n in final_lengths(initial, 4, True)}
    assert raw_savings == {5} and optimum(initial, 4, True) == 10
    print('On the 14-token input every four-step overlap-greedy history saves 5; the exact partial optimum is 10.')

    chars = tuple(WORD)
    for overlapping in (False, True):
        tape = chars
        gains = []
        for _ in range(4):
            frequencies = scores(tape, overlapping)
            assert len(frequencies) == 1
            pair = next(iter(frequencies))
            starts = leftmost(occurrences(tape, pair))
            gains.append(len(starts))
            tape = replace(tape, starts)
        assert gains == [32, 16, 8, 4] and tape == ('a' * 16,) * 4
        print(f'64 initial characters, {"overlap" if overlapping else "replacement"} ranking: gains {gains}, final length 4.')
    # A rule can at most double the maximum token length. After four rules any
    # partial comparator still needs at least ceil(64 / 16) final tokens.
    assert len(WORD) == 64 and 2**4 == 16
    print('Four-merge optimum from 64 single characters: 60 tokens saved.')


if __name__ == '__main__':
    main()
