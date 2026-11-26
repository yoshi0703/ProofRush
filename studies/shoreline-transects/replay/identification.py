"""Rational certificates for estimability when the transect-selection rule is missing."""
from fractions import Fraction as F
from itertools import product
from math import comb
from rounding import whole_redraw, successive, inclusion_for

U,W,S = whole_redraw((1,1)),whole_redraw(),successive()
ROWS = (U,W,S)
a,b=[v[1] for v in ROWS],[v[2] for v in ROWS]
d=[a[(i+1)%3]*b[(i+2)%3]-a[(i+2)%3]*b[(i+1)%3] for i in range(3)]
assert sum(x*y for x,y in zip(d,a))==sum(x*y for x,y in zip(d,b))==0
assert sum(d)!=0

def solve2(x,y):
    det=a[0]*b[1]-a[1]*b[0]
    return (x*b[1]-y*b[0])/det, (a[0]*y-a[1]*x)/det

# For every vector v=Mh−1, d·v=−sum(d), hence ||v||∞ ≥ gap.
gap=abs(sum(d))/sum(map(abs,d))
sign=lambda x: 1 if x>0 else -1
target=[1-sign(sum(d))*sign(x)*gap for x in d]
h=solve2(*target[:2])
assert all(ai*h[0]+bi*h[1]==v for ai,bi,v in zip(a,b,target))

# Among nonnegative component weights, the largest multiplicative separation
# between the two extreme designs has the sharp lower envelope a_U/a_S.
assert a[0]>a[1]>a[2]>0 and b[0]>b[1]>b[2]>0
assert b[0]/b[2]>a[0]/a[2]
positive_h=(2/(a[0]+a[2]),F(0))
positive_gap=(a[0]-a[2])/(a[0]+a[2])
assert max(abs(ai*positive_h[0]-1) for ai in a)==positive_gap

def labelled_repeat(left,right):
    return sum(left[j]*inclusion_for(j,right) for j in range(3))

if __name__=="__main__":
    print('left-null certificate',*(str(x) for x in d),'sum',sum(d))
    print('signed minimax endpoint-relative bias',gap,float(gap),'weights',h, tuple(map(float,h)))
    print('nonnegative minimax endpoint-relative bias',positive_gap,float(positive_gap),'weights',positive_h)
    print('largest unconditional repeat probability',max(labelled_repeat(l,r) for l,r in product(ROWS,repeat=2)))
    print('largest conditional repeat probability',max(inclusion_for(j,v) for j in range(3) for v in ROWS))
