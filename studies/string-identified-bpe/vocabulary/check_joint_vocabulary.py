"""Independent finite tests of the grouped diamonds plus reusable guards.
Tokens are unary spelling lengths (positive Python ints); merging adds lengths.
The program checks actual raw and nonoverlap counts on the serialized word.
"""
import math, random
from collections import Counter

def itinerary(need):
    q=2
    while q*(q-1)<need:q+=1
    outgoing=[list(range(i))+list(range(i+1,q)) for i in range(q)]
    stack=[0]; circuit=[]
    while stack:
        x=stack[-1]
        if outgoing[x]: stack.append(outgoing[x].pop())
        else: circuit.append(stack.pop())
    p=list(reversed(circuit))[:need+1]
    assert len(p)==need+1 and len(set(zip(p,p[1:])))==need
    return q,p

def raw(word): return Counter(zip(word,word[1:]))
def gain(word,p):
    i=n=0
    while i+1<len(word):
        if (word[i],word[i+1])==p: n+=1;i+=2
        else:i+=1
    return n

def merge(word,p):
    out=[];i=0
    while i<len(word):
        if i+1<len(word) and (word[i],word[i+1])==p:
            out.append(word[i]+word[i+1]);i+=2
        else:out.append(word[i]);i+=1
    return out

def build(m,k):
    L=k//(2*m); assert L>=m
    q,groups=itinerary(L-1)
    B=2*m*q+1
    U=lambda j,i: m*groups[j]+i+1
    V=lambda j,i: B-U(j,i)
    H=lambda j:(j+1)*B
    def row(s,x,y):
        z=[H(s)]
        for j in range(s,L):
            i=x if j%2==0 else y
            z=[U(j,i)]+z+[V(j,i)]
        return z
    core=[row(s,x,y) for s in range(m) for x in range(m) for y in range(m)]
    n=math.isqrt(k-1)+1
    exponent=((L+2)*B).bit_length()+2
    P=[1<<(exponent+i) for i in range(n)]
    Q=[1<<(exponent+n+i) for i in range(n)]
    pairs=[(P[i],Q[j]) for i in range(n) for j in range(n)][:k]
    blocks=[(r,None) for r in core]+[([a,b],(a,b)) for a,b in pairs for _ in range(m+1)]
    # Color each inter-block boundary. Account for either state of every
    # neighboring decoy block; bound each oriented resource/color count by m.
    uses=Counter(); colors=[]
    for (left,lp),(right,rp) in zip(blocks,blocks[1:]):
        lresources={left[-1]} if lp is None else {left[-1],sum(lp)}
        rresources={right[0]} if rp is None else {right[0],sum(rp)}
        color=0
        while any(uses[('L',r,color)]>=m for r in lresources) or any(uses[('R',r,color)]>=m for r in rresources): color+=1
        colors.append(color)
        for r in lresources:uses[('L',r,color)]+=1
        for r in rresources:uses[('R',r,color)]+=1
    guards=[1<<(exponent+2*n+c) for c in range(max(colors,default=-1)+1)]
    word=[]
    for j,(block,_) in enumerate(blocks):
        word.extend(block)
        if j<len(colors):word.append(guards[colors[j]])
    return L,q,U,V,H,pairs,word,len(guards),len(set(word)),len(core)

def check(m,k,seed):
    L,q,U,V,H,pairs,word,ng,types,numrows=build(m,k)
    # Execute comparator literally, including guards and decoy blocks.
    cmp=word
    for j in range(L):
        for i in range(m):cmp=merge(cmp,(U(j,i),H(j)))
        for i in range(m):cmp=merge(cmp,(U(j,i)+H(j),V(j,i)))
    expected=2*m*m*sum(L-s for s in range(m))
    assert len(word)-len(cmp)==expected,(m,k,len(word)-len(cmp),expected)
    # Every tie choice among yet-unselected private rules is forced; raw
    # checking suffices for both because private counts are disjoint.
    rng=random.Random(seed); order=pairs[:];rng.shuffle(order)
    greedy=word
    for ix,p in enumerate(order):
        c=raw(greedy)
        assert c[p]==m+1 and gain(greedy,p)==m+1
        assert all(v<=m or pp in order[ix:] for pp,v in c.items()),(m,k,ix,c.most_common(5))
        assert max(c.values())==m+1
        greedy=merge(greedy,p)
    assert len(word)-len(greedy)==k*(m+1)
    return L,q,ng,types,numrows,expected

if __name__=='__main__':
    count=0
    for m in range(2,6):
        for L in range(m,min(m+5,11)):
            for rem in (0,1,2*m-1):
                k=2*m*L+rem
                for seed in range(3): last=check(m,k,seed);count+=1
    # Exhaust every subset (all possible decoy-history states) for k=8.
    L,q,U,V,H,pairs,initial,ng,types,numrows=build(2,8)
    for mask in range(1<<len(pairs)):
        word=initial
        for i,pair in enumerate(pairs):
            if mask>>i & 1: word=merge(word,pair)
        counts=raw(word)
        remaining={pair for i,pair in enumerate(pairs) if not(mask>>i & 1)}
        assert all(v<=2 or p in remaining for p,v in counts.items())
        assert all(counts[p]==3 for p in remaining)
    print('passed',count,'cases and all 256 k=8 history states; last L,q,guard_types,all_types,core_rows,comparator:',last)
