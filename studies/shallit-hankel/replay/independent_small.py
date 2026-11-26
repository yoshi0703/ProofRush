from itertools import chain
S={1:(1,2),2:(2,3),3:(1,4),4:(3,2)}
P=((1,2),(1,4),(2,1),(2,2),(2,3),(3,1),(3,2),(4,1),(4,2))
def grow(a,k):
 for _ in range(k): a=tuple(chain.from_iterable(S[x] for x in a))
 return a
p=2**61-1
# All requested order-specific offsets are embedded as factors in these nine independently formed 512-letter blocks.
blocks=[grow(pair,8) for pair in P]
# Independently generated sigma^5(1) contains each pair by start offset <25.
seed=grow((1,),5)
assert all(any(seed[i:i+2]==pair for i in range(24)) for pair in P)
w=grow((1,),5+8)[:25*256]
# Deterministic independent primality check for the 61st Mersenne prime.
x=4
for _ in range(59): x=(x*x-2)%p
assert x==0

def det_gaussian(a):
 n=len(a); a=[list(row) for row in a]; det=1
 for j in range(n):
  pivot=next((i for i in range(j,n) if a[i][j]%p),None)
  if pivot is None:return 0
  if pivot!=j:a[j],a[pivot]=a[pivot],a[j];det=-det
  x=a[j][j]%p;det=det*x%p;inv=pow(x,p-2,p)
  for i in range(j+1,n):
   factor=a[i][j]*inv%p
   for k in range(j+1,n):a[i][k]=(a[i][k]-factor*a[j][k])%p
 return det%p
prev2=[1]*(len(w)+1)
prev=list(w)
for n in range(1,82):
 if n>=2:
  den=prev2[2:2+len(prev)-2]
  if not all(den): raise AssertionError(('zero denominator',n))
  prefix=[1]
  for x in den:prefix.append(prefix[-1]*x%p)
  v=pow(prefix[-1],p-2,p)
  inv=[0]*len(den)
  for i in range(len(den)-1,-1,-1):inv[i]=v*prefix[i]%p;v=v*den[i]%p
  new=[(prev[i]*prev[i+2]-prev[i+1]*prev[i+1])*inv[i]%p for i in range(len(den))]
  prev2,prev=prev,new
 assert all(prev), ('zero determinant',n,prev.index(0) if 0 in prev else '')
 if n in (1,2,7,17,43,81):
  for start in (0,37,2049):
   direct=det_gaussian([[w[start+i+j] for j in range(n)] for i in range(n)])
   assert direct==prev[start], ('Gaussian mismatch',n,start)

 # Explicitly map each pair/offset factor to an occurrence inside generated prefix.
 for pair,block in zip(P,blocks):
  first=next(i for i in range(24) if seed[i:i+2]==pair)*256
  for offset in range(256):
   factor=block[offset:offset+2*n-1]
   assert len(factor)==2*n-1 and w[first+offset:first+offset+len(factor)]==factor
 print('n',n,'nonzero_count',len(prev),'pair_offset',len(blocks)*256,flush=True)
print('PASS prime=',p,'coverage=',81*9*256)
