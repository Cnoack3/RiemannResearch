# Exact-rational small-period energy certificate — 30 October 2026

Classification: exact-rational arithmetic enclosure, **not Lean-verified**. Python Fraction operations and comparisons use rational arithmetic; this is independent of the formal Lean modules.

For each residue r=1,...,L and J>0, the omitted decreasing tail obeys

\[
\frac1{L(r+JL)}\le\sum_{j=J}^{\infty}\frac1{(r+jL)^2}
\le\frac1{L(r+JL)}+\frac1{(r+JL)^2}.
\]

Directed fixed-point bounds enclose the finite part. Each weight enclosure yields a positive semidefinite Gram enclosure because it multiplies a residue-row outer product. The code checks positive rational Schur pivots, and solves constrained minima exactly for the lower and upper Gram matrices. Monotonicity of the minimum over the same feasible affine set encloses the actual minimum. The same series method bounds zeta(2) before normalizing.

The assertions certify 0.06698818 < E_2-E_1 < 0.06698820 and fullGain < (3/4) oldHeadCost at p=5. Thus an every-stage 3/4 capture proposal fails. No asymptotic conclusion follows. The long printed decimal endpoints use ordinary decimal rounding; the stated coarse thresholds are checked as exact rational inequalities. The script was rerun independently and all assertions passed.

## Reproducible source

Save as certified_small_energy_diagnostics.py and run with standard-library Python.

```python
#!/usr/bin/env python3
"""Exact rational small-period energy enclosures (paper arithmetic certificate).

For each residue r=1,...,L, sum j=0,...,J-1 with directed fixed-point
rounding. Bound the omitted decreasing tail by the two integral-test bounds:
1/(L*(r+J*L)) <= sum_{j=J}∞ 1/(r+jL)^2
 <= 1/(L*(r+J*L)) + 1/(r+J*L)^2.

Thus Gram_lo <= Gram_true <= Gram_hi in Loewner order. Exact rational
constrained minima then enclose the actual complete-period minimum energy.
The positivity of rational LDL pivots is checked exactly. This script is a
reproducible exact-rational arithmetic certificate; it is NOT Lean-verified.
"""
import json
from functools import lru_cache
from fractions import Fraction
from decimal import Decimal, localcontext

F=Fraction

BITS=100
J=2000

def weight_bounds(r,L,J=J):
    scale=1<<BITS
    acc=sum(scale//((r+j*L)**2) for j in range(J))
    x=r+J*L
    lo=F(acc,scale)+F(1,L*x)
    hi=F(acc+J,scale)+F(1,L*x)+F(1,x*x)
    return lo,hi

def solve(A,b):
    n=len(A)
    M=[list(row)+[rhs] for row,rhs in zip(A,b)]
    for k in range(n):
        pivot=next(j for j in range(k,n) if M[j][k])
        M[k],M[pivot]=M[pivot],M[k]
        p=M[k][k]
        M[k]=[x/p for x in M[k]]
        for j in range(k+1,n):
            a=M[j][k]
            if a:
                M[j]=[x-a*y for x,y in zip(M[j],M[k])]
    x=[F(0)]*n
    for k in reversed(range(n)):
        x[k]=M[k][-1]-sum(M[k][j]*x[j] for j in range(k+1,n))
    return x

def assert_pos_def(G):
    A=[row[:] for row in G]
    for k in range(len(A)):
        p=A[k][k]
        assert p>0
        for i in range(k+1,len(A)):
            for j in range(k+1,len(A)):
                A[i][j]-=A[i][k]*A[k][j]/p

@lru_cache(None)
def grams(L):
    ds=[d for d in range(2,L+1) if L%d==0]
    X=[[F(n%d,d) for d in ds] for n in range(1,L+1)]
    ww=[weight_bounds(n,L) for n in range(1,L+1)]
    Gs=[]
    for side in [0,1]:
        G=[[sum(ww[n][side]*X[n][j]*X[n][k] for n in range(L))
            for k in range(len(ds))] for j in range(len(ds))]
        assert_pos_def(G)
        Gs.append(G)
    return X,Gs

def minimum(G,A):
    n=len(G); h=len(A)
    K=[G[j]+[A[k][j] for k in range(h)] for j in range(n)]
    K += [row+[F(0)]*h for row in A]
    c=solve(K,[F(0)]*n+[F(1)]*h)[:n]
    assert all(sum(a*x for a,x in zip(row,c))==1 for row in A)
    return sum(c[j]*G[j][k]*c[k] for j in range(n) for k in range(n))

@lru_cache(None)
def energy(L,H):
    X,Gs=grams(L)
    A=X[:H]
    return tuple(minimum(G,A) for G in Gs)

def decimal_bounds(pair):
    with localcontext() as ctx:
        ctx.prec=30
        return [str(Decimal(x.numerator)/Decimal(x.denominator)) for x in pair]

old=energy(6,2); old_next=energy(6,3); new=energy(30,3)
zlo,zhi=weight_bounds(1,1,J=100000)
delta=(new[0]-old[1],new[1]-old[0])
cost=(old_next[0]-old[1],old_next[1]-old[0])
gain=(old_next[0]-new[1],old_next[1]-new[0])
assert delta[0]>0 and cost[0]>0 and gain[0]>0
normalized_delta=(delta[0]/zhi,delta[1]/zlo)
normalized_cost=(cost[0]/zhi,cost[1]/zlo)
normalized_gain=(gain[0]/zhi,gain[1]/zlo)
assert normalized_delta[0]>F(669,10000)
assert normalized_delta[1]<F(671,10000)
assert normalized_delta[0]>F(6698818,100000000)
assert normalized_delta[1]<F(6698820,100000000)
assert gain[1] < F(3,4)*cost[0]
result={'classification':'Exact rational enclosures; not Lean-verified',
 'p':5,'old_period':6,'new_period':30,'old_head':2,'new_head':3,
 'trigamma_period_terms':J,'fixed_point_bits':BITS,
 'normalized_increment_bounds':decimal_bounds(normalized_delta),
 'normalized_old_head_cost_bounds':decimal_bounds(normalized_cost),
 'normalized_full_gain_bounds':decimal_bounds(normalized_gain),
 'full_gain_over_old_head_cost_bounds':decimal_bounds((gain[0]/cost[1],gain[1]/cost[0])),
 'exact_rational_checks':{'0.0669 < actual_increment < 0.0671':True,
                         '0.06698818 < actual_increment < 0.06698820':True,
                         'actual_full_gain < (3/4)*old_head_cost':True}}
print(json.dumps(result,indent=2))
```

## Output

```json
{
  "classification": "Exact rational enclosures; not Lean-verified",
  "p": 5,
  "old_period": 6,
  "new_period": 30,
  "old_head": 2,
  "new_head": 3,
  "trigamma_period_terms": 2000,
  "fixed_point_bits": 100,
  "normalized_increment_bounds": [
    "0.0669881867337068618046770590928",
    "0.0669881999780641090112138834253"
  ],
  "normalized_old_head_cost_bounds": [
    "0.252249656066311654383252007244",
    "0.252249701272230412308591954810"
  ],
  "normalized_full_gain_bounds": [
    "0.185261467530273252007255082624",
    "0.185261503096497843978264364580"
  ],
  "full_gain_over_old_head_cost_bounds": [
    "0.734436816405183909889112123602",
    "0.734437088931188797944291767375"
  ],
  "exact_rational_checks": {
    "0.0669 < actual_increment < 0.0671": true,
    "0.06698818 < actual_increment < 0.06698820": true,
    "actual_full_gain < (3/4)*old_head_cost": true
  }
}
```
