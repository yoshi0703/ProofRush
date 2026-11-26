"""Check the finite cases in the overlap-freeness proof."""
from itertools import product

MORPHISM = dict(zip("1234", ("12", "23", "14", "32")))
IDENTITY = frozenset((letter, letter) for letter in MORPHISM)


def expand(word):
    return "".join(MORPHISM[letter] for letter in word)


def adjacent_pairs(word):
    return {word[index:index + 2] for index in range(len(word) - 1)}


def pair_representatives():
    prefix = "1"
    pairs = set()
    while True:
        expanded = expand(prefix)
        next_pairs = adjacent_pairs(expanded)
        if prefix != "1" and next_pairs == pairs:
            return {pair: prefix.index(pair) for pair in sorted(pairs)}
        prefix, pairs = expanded, next_pairs


def pull_back(relation, digit):
    return frozenset(
        (a, b) for a, b in product(MORPHISM, repeat=2)
        if (MORPHISM[a][digit], MORPHISM[b][digit]) in relation
    )


def endpoint_relations():
    start = (IDENTITY, IDENTITY)
    remaining = [start]
    seen = {start}
    while remaining:
        left, right = remaining.pop()
        even = (pull_back(left, 0) & pull_back(IDENTITY, 1), pull_back(right, 0))
        odd = (pull_back(left, 1), pull_back(IDENTITY, 0) & pull_back(right, 1))
        for state in (even, odd):
            if state not in seen:
                remaining.append(state)
                seen.add(state)
    return seen


def main():
    pairs = pair_representatives()
    crossing_images = {
        pair for pair in pairs
        if MORPHISM[pair[0]][1] + MORPHISM[pair[1]][0] in MORPHISM.values()
    }
    assert crossing_images == {"14", "22"}
    assert "22" not in MORPHISM.values()

    prefix = "1"
    while len(prefix) < (max(pairs.values()) + 2) * 8:
        prefix = expand(prefix)
    states = endpoint_relations()
    for left, right in states:
        for period in (1, 3):
            factors = {
                prefix[i:i + 2 * period + 1]
                for i in range(len(prefix) - 2 * period)
            }
            for word in factors:
                if all(word[t] == word[period + t] for t in range(1, period)):
                    assert (
                        (word[0], word[period]) not in left
                        or (word[period], word[2 * period]) not in right
                    ), (left, right, period, word)
    print(f"adjacent_pairs={pairs}")
    print(f"endpoint_states={len(states)} no_overlaps=True")


if __name__ == "__main__":
    main()
