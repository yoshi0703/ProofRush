"""Exact finite checks of the two counting arguments for literal-spelling BPE."""
from collections import Counter, defaultdict
from dataclasses import dataclass
from random import Random


@dataclass(frozen=True)
class Token:
    text: str
    start: int
    stop: int
    stage: int = 0
    children: tuple = ()

    @property
    def size(self):
        return self.stop - self.start


def pair(left, right):
    return left.text, right.text


def apply_row(row, target, stage, allowed=None):
    selected = []
    last = -2
    for position, (left, right) in enumerate(zip(row, row[1:])):
        if position > last + 1 and pair(left, right) == target:
            if allowed is None or position in allowed:
                selected.append(position)
                last = position
    result = list(row)
    for position in reversed(selected):
        left, right = row[position:position + 2]
        result[position:position + 2] = [
            Token(left.text + right.text, left.start, right.stop, stage, (left, right))
        ]
    return result, len(selected)


def replay(atoms, rules):
    row = list(atoms)
    for chosen in rules:
        result = []
        position = 0
        while position < len(row):
            left = row[position]
            if position + 1 < len(row) and (left, row[position + 1]) == chosen:
                result.append(left + row[position + 1])
                position += 2
            else:
                result.append(left)
                position += 1
        row = result
    return tuple(row)


def initialize(rows):
    return [(weight, [Token(text, i, i + 1) for i, text in enumerate(atoms)])
            for weight, atoms in rows]


def raw_counts(table):
    total = Counter()
    for weight, row in table:
        for left, right in zip(row, row[1:]):
            total[pair(left, right)] += weight
    return total


def transition(table, chosen, stage, rng=None):
    result = []
    gain = 0
    for weight, row in table:
        allowed = None if rng is None else {
            i for i in range(len(row) - 1) if rng.randrange(3) != 0
        }
        after, local = apply_row(row, chosen, stage, allowed)
        result.append((weight, after))
        gain += weight * local
    return result, gain


def inspect_boundaries(initial, table, rules, saved, alphabet_size, potential):
    replays = {}
    groups = defaultdict(Counter)
    lengths = Counter()
    for (_, original), (weight, row) in zip(initial, table):
        assert tuple(atom for token in row for atom in original[token.start:token.stop]) == original
        assert all(token.text == "".join(original[token.start:token.stop]) for token in row)
        for left, right in zip(row, row[1:]):
            assert left.stop == right.start
            atoms = original[left.start:right.stop]
            assert pair(left, right) == replays.setdefault(atoms, replay(atoms, rules))
            groups[len(atoms)][pair(left, right)] += weight
            lengths[len(atoms)] += weight
    assert sum(lengths.values()) == potential - saved
    assert sum((size - 2) * count for size, count in lengths.items()) <= 2 * saved
    largest_raw = max(raw_counts(table).values(), default=0)
    for m in range(2, 8):
        bound = sum(alphabet_size**size for size in range(2, m + 1))
        near = sum(count for size, count in lengths.items() if size <= m)
        actual_types = set().union(*(groups[size].keys() for size in range(2, m + 1)))
        assert len(actual_types) <= bound
        assert near <= bound * largest_raw
        assert (m - 1) * (potential - saved - near) <= 2 * saved


def forest_data(final, initial, budget, gap):
    classes = Counter()
    cherries = []
    short_matching = []
    long_mass = first_mass = short_mass = 0
    for index, (weight, row) in enumerate(final):
        original = initial[index][1]

        def visit(node):
            nonlocal long_mass, first_mass, short_mass
            if not node.children:
                return
            left, right = node.children
            if not left.children and not right.children:
                classes["cherry"] += weight
                assert right.start == left.start + 1
                cherries.append((index, left.start, right.start, pair(left, right), weight))
                return
            if left.children and right.children:
                classes["branch"] += weight
                visit(left)
                visit(right)
                return
            sides = ([], [])
            while node.children:
                left, right = node.children
                if bool(left.children) == bool(right.children):
                    break
                classes["unary"] += weight
                side = int(bool(left.children))
                leaf = (left, right)[side]
                sides[side].append((leaf, node.stage))
                node = (right, left)[side]
            for side, recent_first in enumerate(sides):
                if not recent_first:
                    continue
                first_mass += weight
                next_available = 0
                for position, ((before, start), (after, end)) in enumerate(
                    zip(recent_first[:0:-1], recent_first[-2::-1])
                ):
                    assert 0 < end - start < budget
                    lo, hi = sorted((before.start, after.start))
                    assert hi == lo + 1
                    assert after.start == before.start + (1 if side else -1)
                    if end - start > gap:
                        long_mass += weight
                    else:
                        short_mass += weight
                        if position >= next_available:
                            short_matching.append((index, lo, hi, original[lo:hi+1], weight))
                            next_available = position + 2
            visit(node)
        for token in row:
            visit(token)

    cherry_mass = classes["cherry"]
    assert len({edge[3] for edge in cherries}) <= budget
    assert len({edge[3] for edge in short_matching}) <= 2 * budget * gap
    assert classes["branch"] <= cherry_mass
    assert classes["unary"] == first_mass + long_mass + short_mass
    assert first_mass <= 4 * cherry_mass
    assert long_mass * gap <= 4 * cherry_mass * budget
    assert short_mass <= 2 * sum(edge[4] for edge in short_matching)
    for matching in (cherries, short_matching):
        endpoints = [(row, i) for row, left, right, _, _ in matching for i in (left, right)]
        assert len(set(endpoints)) == len(endpoints)
    return classes.total(), cherries, short_matching


def audit_history(initial, budget, rank_raw, rng):
    potential = sum(weight * max(len(row) - 1, 0) for weight, row in initial)
    alphabet_size = len({atom for _, row in initial for atom in row})
    table = initialize(initial)
    saved, rules = 0, []
    history = []
    for stage in range(1, budget + 1):
        raw = raw_counts(table)
        inspect_boundaries(initial, table, rules, saved, alphabet_size, potential)
        if not raw:
            assert saved == potential
            break
        options = [(candidate, *transition(table, candidate, stage)) for candidate in raw]
        score = max(raw.values() if rank_raw else (gain for _, _, gain in options))
        chosen, after, gain = rng.choice([
            item for item in options if (raw[item[0]] if rank_raw else item[2]) == score
        ])
        assert 2 * gain >= max(raw.values())
        history.append((table, saved, gain))
        rules.append(chosen)
        table = after
        saved += gain
    for m in range(2, 8):
        n = sum(alphabet_size**size for size in range(2, m + 1))
        assert budget * (m - 1) * potential <= (
            budget * (m + 1) + 2 * n * (m - 1)
        ) * saved

    comp = initialize(initial)
    comp_total = 0
    for stage in range(1, budget + 1):
        raw = raw_counts(comp)
        if not raw:
            break
        comp, step_gain = transition(comp, rng.choice(list(raw)), stage, rng)
        comp_total += step_gain
    assert comp_total <= potential

    for gap in {1, 2, 3, budget}:
        utility, cherries, short = forest_data(comp, initial, budget, gap)
        assert utility == comp_total
        for matching in (cherries, short):
            q = len({edge[3] for edge in matching})
            mass = sum(edge[4] for edge in matching)
            for state, already, next_gain in history:
                singleton = [{token.start for token in row if token.size == 1} for _, row in state]
                surviving = sum(weight for j, a, b, _, weight in matching
                                if a in singleton[j] and b in singleton[j])
                assert mass - 2 * already <= surviving <= 2 * q * next_gain
            assert budget * mass <= (2 * budget + 2 * q) * saved
        assert gap * utility <= (28 * gap + 16 * budget + 8 * gap**2) * saved
    return len(history)


def main():
    # Literal reuse can increase the maximum raw pair frequency.
    collision = initialize([(1, ("a", "b", "x")), (1, ("ab", "x"))])
    assert max(raw_counts(collision).values()) == 1
    after, gain = transition(collision, ("a", "b"), 1)
    assert gain == 1
    assert raw_counts(after) == {("ab", "x"): 2}

    rng = Random(20261127)
    traces = states = 0
    alphabets = [('a',), ('a', 'aa'), ('a', 'aa', 'aaa'),
                 ('a', 'ab', 'b'), ('a', 'ba', 'aba', 'b')]
    for alphabet in alphabets:
        for _ in range(190):
            rows = [(rng.randint(1, 5), tuple(rng.choices(alphabet, k=rng.randint(0, 48))))
                    for _ in range(rng.randint(1, 5))]
            budget = rng.randint(1, 22)
            for rank_raw in (False, True):
                states += audit_history(rows, budget, rank_raw, rng)
                traces += 1
    print(f"Exact checks passed for {traces} greedy and partial-comparator traces, {states} greedy states.")


if __name__ == "__main__":
    main()
