"""Exact strip inclusion probabilities for the two common duplicate redraw rules."""
from collections import Counter, defaultdict
from fractions import Fraction as F
from math import comb


def whole_redraw(weights=(3,5)):
    a,b = weights
    by_edge = [comb(2,j)*comb(18,4-j)*a**j*b**(4-j) for j in range(3)]
    return [F(x,sum(by_edge)) for x in by_edge]


def successive(weights=(3,5)):
    a,b = weights
    dist = {0: F(1)}
    for t in range(4):
        nxt = defaultdict(F)
        for j, mass in dist.items():
            edge = a*(2-j)
            inner = b*(18-(t-j))
            if edge:
                nxt[j+1] += mass*F(edge,edge+inner)
            nxt[j] += mass*F(inner,edge+inner)
        dist = nxt
    return [dist[j] for j in range(3)]


def moments(dist):
    EJ = sum(j*p for j,p in enumerate(dist))
    return EJ/2, (4-EJ)/18


def inclusion_for(j, method):
    """Probability of this labelled four-set given its j endpoint strips."""
    return method[j]/(comb(2,j)*comb(18,4-j))


if __name__ == "__main__":
    bins = Counter(5*((i+2)//5) for i in range(96))
    assert bins[0] == bins[95] == 3 and all(bins[i]==5 for i in range(5,95,5))
    assert whole_redraw((1,1)) == successive((1,1))
    for label, dist in [('uniform',whole_redraw((1,1))),('full_redraw',whole_redraw()),
                        ('duplicate_only',successive())]:
        edge,inner = moments(dist)
        print(label,'P(J=0,1,2)',','.join(map(str,dist)),'endpoint',edge,
              f'({float(edge):.8f})','interior',inner,f'({float(inner):.8f})',
              f'endpoint-only count ratio {float(5*edge):.6f}')
