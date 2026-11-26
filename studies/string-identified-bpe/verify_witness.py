"""Independent exact replay of the spelling-identified BPE counterexample."""
from fractions import Fraction
from functools import cache
from itertools import product


def occurrences(tokens, pair):
    return tuple(
        i for i in range(len(tokens) - 1)
        if (tokens[i], tokens[i + 1]) == pair
    )


def leftmost(starts):
    taken = []
    next_free = 0
    for i in starts:
        if i >= next_free:
            taken.append(i)
            next_free = i + 2
    return tuple(taken)


def replace(tokens, starts):
    chosen = set(starts)
    output = []
    i = 0
    while i < len(tokens):
        if i in chosen:
            output.append(tokens[i] + tokens[i + 1])
            i += 2
        else:
            output.append(tokens[i])
            i += 1
    return tuple(output)


def all_nonoverlapping(starts):
    if not starts:
        yield ()
        return
    first, *tail = starts
    yield from all_nonoverlapping(tail)
    for rest in all_nonoverlapping([x for x in tail if x >= first + 2]):
        yield (first,) + rest


def all_pairs(tokens):
    labels = sorted(set(tokens))
    return product(labels, repeat=2)


@cache
def optimum(tokens, remaining, partial):
    best = 0
    if remaining == 0:
        return best
    for pair in all_pairs(tokens):
        positions = occurrences(tokens, pair)
        selections = all_nonoverlapping(positions) if partial else (leftmost(positions),)
        for starts in selections:
            if starts:
                new = replace(tokens, starts)
                best = max(best, len(starts) + optimum(new, remaining - 1, partial))
    return best


def run(initial, rules, greedy):
    tokens = initial
    gains = []
    total = 0
    for step, pair in enumerate(rules, 1):
        ranks = {
            candidate: len(leftmost(occurrences(tokens, candidate)))
            for candidate in all_pairs(tokens)
        }
        largest = max(ranks.values())
        winners = sorted(tuple(map(len, candidate)) for candidate, gain in ranks.items() if gain == largest)
        starts = leftmost(occurrences(tokens, pair))
        if greedy:
            assert len(starts) == largest
        current = replace(tokens, starts)
        assert ''.join(current) == ''.join(initial)
        assert len(tokens) - len(current) == len(starts) > 0
        print(f"step={step} chosen={tuple(map(len, pair))} gain={len(starts)} "
              f"max={largest} maximizers={winners} positions={starts} "
              f"output={tuple(map(len, current))}")
        gains.append(len(starts))
        total += len(starts)
        tokens = current
    return total, gains


def spell(length):
    return "a" * length


def main():
    initial = tuple(map(spell, (8, 4, 2, 1, 1, 8, 2, 2, 4, 4, 4, 8, 8, 8)))
    assert initial[2] == ''.join(initial[3:5])
    greedy = tuple(tuple(map(spell, pair)) for pair in ((8, 4), (12, 2), (14, 1), (15, 1)))
    comparator = tuple(tuple(map(spell, pair)) for pair in ((1, 1), (2, 2), (4, 4), (8, 8)))

    print("Greedy")
    observed, greedy_steps = run(initial, greedy, greedy=True)
    print("Full comparator")
    admitted, compare_steps = run(initial, comparator, greedy=False)
    assert (observed, greedy_steps) == (4, [1, 1, 1, 1])
    assert (admitted, compare_steps) == (10, [1, 2, 3, 4])
    assert optimum(initial, 4, False) == admitted
    assert optimum(initial, 4, True) == admitted
    print(f"exact full optimum={admitted} exact partial optimum={admitted}")
    ratio = Fraction(observed, admitted)
    threshold = (1 - (1 - Fraction(2, 4)) ** 4) / 2
    assert ratio == Fraction(2, 5)
    assert threshold == Fraction(15, 32)
    assert ratio < threshold
    print(f"ratio={ratio} < stated threshold={threshold}")


if __name__ == "__main__":
    main()
