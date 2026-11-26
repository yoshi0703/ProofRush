#!/usr/bin/env python3
"""Replay the same presegmented diamond on the spelling alphabet {a}."""

from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import groupby, product
import json


def model(m, k):
    B = 2*m*m+1
    H = [(j+1)*B for j in range(m+1)]
    largest_core = H[-1]
    private_start = largest_core+k+1
    private = list(range(private_start+1, private_start+k+1))
    first_separator = 2*(private_start+k)+1
    rows = []
    for seed, x, y in product(range(m), repeat=3):
        left = [j*m+(x if j%2==0 else y)+1 for j in range(seed, m)]
        rows.append([*reversed(left), H[seed], *(B-a for a in left)])
    for a in private:
        rows.extend([[a, a]]*(m+1))
    tokens = []
    for index, row in enumerate(rows):
        if index:
            tokens.append(first_separator+index-1)
        tokens.extend(row)
    comparison = []
    for j, h in enumerate(H[:-1]):
        left = range(j*m+1, (j+1)*m+1)
        expected_gain = (j+1)*m
        comparison.extend(((a, h), expected_gain) for a in left)
        comparison.extend(((h+a, B-a), expected_gain) for a in left)
    return tokens, private, comparison, largest_core, first_separator, len(rows)


def pairs(tokens):
    raw = Counter(zip(tokens, tokens[1:]))
    saved = raw.copy()
    for token, run in groupby(tokens):
        size = sum(1 for _ in run)
        if size > 1:
            saved[token, token] += size//2-(size-1)
    return raw, saved


def merge(tokens, rule):
    left, right = rule
    new = left + right
    result = []
    i = 0
    while i < len(tokens):
        token = tokens[i]
        if token == left and i+1 < len(tokens) and tokens[i+1] == right:
            result.append(new)
            i += 2
        else:
            result.append(token)
            i += 1
    return result


def literal_checks(original, current, raw, saved):
    literal_tokens = ['a'*length for length in current]
    assert ''.join(literal_tokens) == original
    observed_pairs = Counter(zip(literal_tokens, literal_tokens[1:]))
    assert {(len(a), len(b)): value for (a, b), value in observed_pairs.items()} == raw
    for left, right in observed_pairs:
        i = 0
        replacements = 0
        while i < len(literal_tokens):
            if (i+1 < len(literal_tokens) and literal_tokens[i] == left
                    and literal_tokens[i+1] == right):
                replacements += 1
                i += 2
            else:
                i += 1
        assert replacements == saved[len(left), len(right)]


def replay(m, k, *, subsets=False, literal=False):
    if m < 1 or k < 2*m*m:
        raise ValueError('require m >= 1 and k >= 2*m*m')
    tokens, private, comparison, core_end, separator_start, row_count = model(m,k)
    assert core_end < private[0] < 2*private[0]
    assert private[-1] < 2*private[0] and 2*private[-1] < separator_start
    initial_raw, initial_saved = pairs(tokens)
    initial_choices = {(a, a) for a in private}
    core_max = max(r for pair, r in initial_raw.items() if max(pair) <= core_end)
    assert core_max == m
    assert max(r for pair, r in initial_raw.items() if max(pair) >= separator_start) == 1
    assert initial_raw == initial_saved
    counted = 0
    raw_literal = 'a'*sum(tokens) if literal else None

    def check_state(state, remaining):
        nonlocal counted
        raw, saved = pairs(state)
        for scores in (raw, saved):
            assert {p for p,n in scores.items() if n == m+1} == remaining
            assert max(scores.values()) == (m+1 if remaining else m)
        if literal:
            literal_checks(raw_literal, state, raw, saved)
        counted += 1

    if subsets:
        # Reconstruct every distinct private-phase state from the root, in the
        # opposite order from the main replay below. Private steps commute.
        for mask in range(1 << k):
            state = tokens
            remain = initial_choices.copy()
            for i, a in enumerate(private):
                if mask >> i & 1:
                    state = merge(state, (a, a))
                    remain.remove((a, a))
            check_state(state, remain)
    state = tokens
    remaining = initial_choices.copy()
    for a in reversed(private):
        check_state(state, remaining)
        after = merge(state, (a, a))
        assert len(state)-len(after) == m+1
        remaining.remove((a, a))
        state = after
    check_state(state, remaining)
    greedy = len(tokens)-len(state)
    state = tokens
    for rule, gain in comparison:
        after = merge(state, rule)
        assert len(state)-len(after) == gain
        if literal:
            assert ''.join('a'*length for length in after) == raw_literal
        state = after
    comparator_saving = len(tokens)-len(state)
    literal_length = sum(tokens)
    assert literal_length == sum(state)
    assert greedy == k*(m+1) and comparator_saving == m**3*(m+1)
    assert len(comparison) == 2*m*m
    digest = sha256()
    chunk = b'a' * min(literal_length, 1024*1024)
    whole_chunks, tail = divmod(literal_length, len(chunk))
    for _ in range(whole_chunks):
        digest.update(chunk)
    digest.update(chunk[:tail])
    if literal:
        assert digest.hexdigest() == sha256(raw_literal.encode('ascii')).hexdigest()
    print(json.dumps(dict(m=m,k=k,alphabet=1,initialTypes=len(set(tokens)),rows=row_count,
                          initialTokens=len(tokens),coreMaximum=core_max,separatorMaximum=1,
                          greedyRawMaximum=m+1,greedyReplacementMaximum=m+1,
                          greedySaving=greedy,comparatorSaving=comparator_saving,ratioUpper=str(Fraction(greedy,comparator_saving)),
                          coreEnd=core_end,privateStart=private[0],privateEnd=private[-1],
                          consumedStart=2*private[0],consumedEnd=2*private[-1],
                          separatorStart=separator_start,separatorEnd=separator_start+row_count-2,
                          literalLength=literal_length,literalSHA256=digest.hexdigest(),
                          exactSubsetReplay=subsets,literalStringTokenReplay=literal,statesChecked=counted,
                          encodingSHA256=sha256(json.dumps(tokens,separators=(',',':')).encode()).hexdigest()),
                     separators=(',',':')))


if __name__=='__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--m', type=int, required=True)
    parser.add_argument('--k', type=int)
    parser.add_argument('--all-subsets', action='store_true')
    parser.add_argument('--literal', action='store_true')
    args = parser.parse_args()
    replay(args.m, args.k if args.k is not None else 2*args.m*args.m,
           subsets=args.all_subsets, literal=args.literal)
