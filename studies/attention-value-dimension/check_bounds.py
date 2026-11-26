"""Finite arithmetic checks accompanying the all-parameter dimension theorem."""
from math import comb, e, log


def parameter_count(heads, degree, width):
    """The parameter count with denominator constant fixed at one."""
    return heads + width * (heads + 1) + comb(degree + width, width)


def binomial_index(heads, degree):
    width = 1
    while comb(degree + width, width) < heads * degree + 1:
        width += 1
    return width


for degree in range(3, 11):
    heads = 4**degree
    width = degree - 2
    count = parameter_count(heads, degree, width)
    threshold = degree * heads
    assert count < threshold
    print(f"D={degree} H={heads} d={width} m={count} T={threshold} gap={threshold-count}")

heads, degree, width, n = 64, 3, 1, 10**8
count = parameter_count(heads, degree, width)
threshold = heads * degree
log_lower = threshold * log(n / threshold)
log_upper = count * log(8 * e * (degree + 1) * n / count)
print(f"example H={heads}, D={degree}, d={width}, n=10^8: log lower {log_lower:.2f}, "
      f"log Warren upper {log_upper:.2f}")

# floor(n/T)^T <= binom(n,T). Replacing e by 3 and n+1 by 2n
# gives an integer comparison with Warren's strict sign-pattern bound.
assert (n // threshold)**threshold * count**count > (24 * (degree + 1) * n)**count
print("exact integer check: binomial lower bound > Warren upper bound")

for heads in range(4, 201):
    for degree in range(2, 101):
        index = binomial_index(heads, degree)
        for width in range((degree - 2) // 2 + 1):
            if parameter_count(heads, degree, width) >= heads * degree:
                assert index <= width + 1
print("comparison audit: H=4..200, D=2..100 passed")
