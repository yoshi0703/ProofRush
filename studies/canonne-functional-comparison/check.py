"""Check Canonne Q2 comparisons with rational arithmetic on cubed masses."""
from fractions import Fraction as Q
from random import Random


def inverse_square(p, error):
    """Scan the number of saturated entries in the minimum-norm witness."""
    target = 1 - error
    head = Q(0)
    tail_square = sum(v * v for v in p)
    for count, largest_tail in enumerate(p):
        if head == target:
            return Q(count)
        if tail_square == 0:
            break
        level = (target - head) / tail_square
        if level * largest_tail <= 1:
            assert not count or level * p[count - 1] >= 1
            return count + level**2 * tail_square
        head += largest_tail
        tail_square -= largest_tail**2
    raise AssertionError("positive inverse target has no waterfill solution")


def truncated_square(roots, error):
    total = sum(x**3 for x in roots)
    remaining = Q(1)
    power_sum = 0
    for index, root in enumerate(roots):
        if remaining <= error:
            break
        remaining -= Q(root**3, total)
        if index:
            power_sum += root**2
    assert remaining <= error
    return Q(power_sum**3, total**2)


def compare(roots, error, cutoff):
    scale = sum(x**3 for x in roots)
    p = [Q(x**3, scale) for x in roots]
    inverse = inverse_square(p, error)
    assert truncated_square(roots, error) <= inverse
    assert inverse <= 1 + truncated_square(roots, cutoff) / (4 * (error - cutoff))**2


def main():
    rng = Random(2750)
    for _ in range(1000):
        roots = sorted([rng.randint(0,25) for _ in range(rng.randint(1,50))], reverse=True)
        if not roots[0]:
            roots[0] = 1
        error = Q(rng.randint(1,999),1000)
        cutoff = Q(rng.randint(1,999),1000) * error
        compare(roots, error, cutoff)
    edges = 0
    for roots in ([1], [9,1,0], [3,3,3,3], [9,4,4,2,1,1,1,0]):
        total = sum(x**3 for x in roots)
        for j in range(1,len(roots)):
            tail = Q(sum(x**3 for x in roots[j:]), total)
            if 0 < tail < 1:
                compare(roots, tail, tail/2)
                compare(roots, (tail+1)/2, tail)
                edges += 2
    # Infinite law: block j has 4**j atoms of mass 2**(-3*j).
    # Raw sum of 2/3 powers diverges, since each block contributes one.
    m = 4
    e = Q(14,15*2**m)
    cutoff = e/32
    waterfill_square = Q(4**(m+1)-4,3) + Q(4**m,15)
    def infinite_truncated_square(error):
        mass = Q(0)
        power = Q(0)
        j = 1
        while 1-mass > error:
            probability = Q(1,2**(3*j))
            required = (1-error-mass)/probability
            count = min(4**j,-(-required.numerator//required.denominator))
            mass += count*probability
            power += Q(count,4**j)
            j += 1
        return (power-Q(1,4))**3
    assert infinite_truncated_square(e) <= waterfill_square
    assert waterfill_square <= 1+infinite_truncated_square(cutoff)/(4*(e-cutoff))**2
    print(f"exact checks: 1000 synthetic finite laws, {edges} cutoff-equality cases, 1 divergent-quasinorm countable law")


if __name__ == "__main__":
    main()
