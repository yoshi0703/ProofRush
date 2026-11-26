"""Check the chronological-edge argument on reproducible, spelling-colliding inputs."""
from dataclasses import dataclass
from random import Random


@dataclass
class Leaf:
    position: int
    spelling: str


@dataclass
class Merge:
    stage: int
    left: "Leaf | Merge"
    right: "Leaf | Merge"

    @property
    def spelling(self):
        return self.left.spelling + self.right.spelling


def counts(tree):
    if isinstance(tree, Leaf):
        return 0, 0, 0
    children = (tree.left, tree.right)
    merged_children = sum(isinstance(child, Merge) for child in children)
    left, right = (counts(child) for child in children)
    return tuple(left[n] + right[n] + (n == merged_children) for n in range(3))


def side_paths(tree):
    """A path lists leaves from the most recent attachment to the oldest."""
    if isinstance(tree, Leaf):
        return
    left, right = [], []
    while isinstance(tree.left, Leaf) != isinstance(tree.right, Leaf):
        if isinstance(tree.left, Leaf):
            left.append((tree.stage, tree.left))
            tree = tree.right
        else:
            right.append((tree.stage, tree.right))
            tree = tree.left
    if left or right:
        yield False, left
        yield True, right
    yield from side_paths(tree.left)
    yield from side_paths(tree.right)


def partial_pass(forest, pair, stage, rng):
    result = []
    i = 0
    while i < len(forest):
        if (i + 1 < len(forest)
                and (forest[i].spelling, forest[i + 1].spelling) == pair
                and rng.randrange(2)):
            result.append(Merge(stage, forest[i], forest[i + 1]))
            i += 2
        else:
            result.append(forest[i])
            i += 1
    return result


def check_one(rng):
    length = rng.randrange(2, 30)
    budget = rng.randrange(1, 20)
    word = [rng.choice(["a", "aa", "aaa", "b", "ab"]) for _ in range(length)]
    forest = [Leaf(i, token) for i, token in enumerate(word)]
    for stage in range(budget):
        if len(forest) < 2:
            break
        pair = rng.choice([(a.spelling, b.spelling) for a, b in zip(forest, forest[1:])])
        forest = partial_pass(forest, pair, stage, rng)
    paths = [path for tree in forest for path in side_paths(tree)]
    cherries, unary, binary = map(sum, zip(*(counts(tree) for tree in forest)))
    assert len(paths) // 2 <= 2 * cherries and binary <= cherries
    assert sum(len(path) for _, path in paths) == unary
    seen_boundaries, label_types, gaps = set(), {}, []
    for right, path in paths:
        for (newer, a), (older, b) in zip(path, path[1:]):
            assert older < newer
            first, second = (b, a) if right else (a, b)
            assert second.position == first.position + 1
            assert first.position not in seen_boundaries
            seen_boundaries.add(first.position)
            gap = newer - older
            gaps.append(gap)
            key = (right, newer, gap)
            pair = (first.spelling, second.spelling)
            assert label_types.setdefault(key, pair) == pair
    for s in range(1, budget + 1):
        short = sum(gap <= s for gap in gaps)
        assert s * unary <= s * short + 4 * (s + budget) * cherries


if __name__ == "__main__":
    rng = Random(20261127)
    for _ in range(10_000):
        check_one(rng)
    print("10,000 comparator forests passed adjacency, uniqueness, label and long-gap checks.")
