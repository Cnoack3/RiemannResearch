# Reproducibility packet: delayed CRT conductors

28 October 2026. These are exact computational certificate sources and data,
separate from the Lean numerical theorems. The accompanying research memo is
[DelayedCRTConductorSchedule20261028.md](DelayedCRTConductorSchedule20261028.md).

The packet preserves all 18 files as text. From the repository root, extract
them into a local experiment directory, then run the immutable checker:

```python
from pathlib import Path
import re
p = Path("RiemannResearch/RH/DelayedCRTComputations20261028.md")
out = p.parent / "experiments" / "DelayedCRT20261028"
out.mkdir(parents=True, exist_ok=True)
pattern = r"<!-- BEGIN_FILE ([A-Za-z0-9_.-]+) -->\n````[^\n]*\n(.*?)\n````\n<!-- END_FILE -->"
for name, body in re.findall(pattern, p.read_text(), re.S):
    (out / name).write_text(body + "\n")
```

```bash
cd RiemannResearch/RH/experiments/DelayedCRT20261028
python verify_all.py
```

All six immutable certificate outputs passed the standard-library checker.
Numerical discovery additionally needs NumPy and SciPy; it is not needed to
verify the rational witnesses. Integral-test tail arguments are documented
in README below and implemented separately from floating-point discovery.

## README.md

<!-- BEGIN_FILE README.md -->
````markdown
# Growing-period CRT energy experiments — 28 October 2026

All energies use `Q(n)=1/(zeta(2)*n^2)`, `n>=1`, and atoms
`g_d(n)=(n mod d)/d`. The computations are finite computational certificates,
not Lean kernel checks. The supplied Lean module is a separate verification layer.

## Results

| Period | Head | Full dictionary numerical minimum | Rigorous feasible-vector upper bound |
|---:|---:|---:|---:|
| 30030 | 15 | 1.01925432764544 | Not asserted; the existing Lean conductor-gap theorem proves every feasible energy >1 |
| 510510 | 15 | 0.9751351445376681 | 80205043617271/82245000000000 = 0.9751965908841996… |
| 510510 | 17 | 0.9891328614338042 | 162709990384841/164490000000000 = 0.9891786150212232… |
| 9699690 | 17 | 0.9758656518545655 | 2717400901/2741500000 = 0.9912095207003465… |
| 9699690 | 19 | 0.9783718881637521 | 543483191/548300000 = 0.991215011854824… |
| 223092870 | 23 | Not computed in the full dictionary | 17378821007/17545600000 = 0.9904945403405983… |

For period 223092870 the floating-point estimate of the constrained minimum
over its 68 divisor conductors at most 300 is 0.9859942421485601. The full
dictionary minimum was not numerically computed; the separate exact
certificate supplies its rigorous upper bound.
The witnesses for 9699690 use 17 conductors; the 223092870 witness uses 68.
The 510510 witnesses use all 127 conductors.

A particularly simple 14-atom witness for 510510, head 15, has

```
c2=c3=c5=c7=c11=c13=c30=1
c6=c10=c14=c15=-1
c17=29518/15015, c34=-2, c51=-3/2.
```

Its complete numerical energy is 0.9856526321394752. A smaller certificate,
using just 768 prefix coordinates and a proved uniform bound 4, gives the
rigorous upper bound `4676846561/4687500000 < 1`.

## Signed constrained system and complete tails

Let D be the divisor dictionary, `A_nd=g_d(n)`, and `c` its signed real
coefficient vector. The exact complete Gram matrix is

```
G_de = (1/zeta(2)) sum_{r=1}^ell
         g_d(r)*g_e(r)*sum_{k=0}^infinity 1/(r+k*ell)^2,
ell = lcm(d,e).
```

The inner sum is `polygamma(1,r/ell)/ell^2`. Using the common period L
instead of `ell` yields the same matrix. The system is `min c^T G c`
subject to `Ac=1`. No cross terms are discarded. The matrix is positive
definite: first differences and divisor induction show the residue atoms
at distinct conductor indices are linearly independent.

For squarefree L containing all primes <=H and 1<=H<L, the head constraints
are equivalent to `c_d=-mu(d)` at every `d<=H` in D, and
`sum c_d/d=1`. Write I for these fixed indices, J for the free indices,
`b=G_JI c_I`, `a=(1/d)_{d in J}`, and
`t=1-sum_{d in I}c_d/d`. Then

```
c_J = -G_JJ^{-1} b + lambda G_JJ^{-1} a,
lambda=(t+a^T G_JJ^{-1}b)/(a^T G_JJ^{-1}a).
```

This is the system used for numerical discovery. The full 510510 and
9699690 Grams sum every period residue with its infinite trigamma weight.
The 223092870 restricted Gram uses each pair's exact period `lcm(d,e)`.
The special-function evaluation is numerical and not part of certification.

## Exact rational certification

The JSON files store rational coefficients as integer numerators over one
common denominator. Head identities and membership are checked exactly.
The atom denominators and all signed cross terms are retained by forming
one exact integer numerator `P(n)` for the whole sum before squaring.

Two independent tail methods are implemented:

1. `certify.py` enumerates a whole period. For `1<=r<=L`, the decreasing
   integral test gives
   `sum_{k>=0}(r+kL)^(-2) <= 1/r^2 + 1/(L*r)`.
   Each nonnegative rational summand is rounded upward to a common integer
   grid of spacing `1/10^14`; its integer ceiling is computed exactly.
   The bound therefore includes every infinite tail.
2. `certify_prefix.py` uses a finite prefix K and the exact signed atom bound
   `|F|<=max(sum_{c>0} c(1-1/d),sum_{c<0}(-c)(1-1/d))<=B`.
   Then `sum_{n>K} F(n)^2/n^2 <= B^2/K`. Each prefix square is rounded
   upward to spacing `1/10^10` and summed in exact integer arithmetic.

Both scripts verify the rational lower bound
`zeta(2)>sum_{n=1}^{200}1/n^2+1/201>16449/10000`, using the lower integral
bound on the omitted inverse-square tail. The JSON bounds are then divided
by `16449/10000`. The finite lower-sum comparison is exact rational arithmetic;
the integral-test facts are mathematical arguments supplied here, not executed
proof-assistant checks.

`certify_simple.py` verifies the 14-atom witness by decomposing it into
periods 30,14,11,13,102. The exact block ranges are

```
[-2/3,14/15], [-1/2,3/7], [0,10/11], [0,12/13], [-2,6584/15015].
```

Their sum is contained in `[-4,4]`. With `P(n)=510510 F(n)` and S=10^8,

```
sum_{n=1}^{768} ceil(S*P(n)^2/(510510^2*n^2)) = 162016546.
(76/125)*(162016546/10^8+16/768) = 4676846561/4687500000 < 1.
```

Here `1/zeta(2)<76/125` follows from the same rational zeta lower bound.

## Reproduction

Certificate checking needs only Python's standard library. The aggregate checker
recomputes each result, compares it with the immutable manifest and JSON record,
and leaves all input files unchanged:

```
python verify_all.py
```

Individual checks:

```
python certify.py witness_510510_15.json
python certify.py witness_510510_17.json
python certify_prefix.py next_17_sparse_17.json 8192
python certify_prefix.py next_sparse_17.json 8192
python certify_prefix.py witness_223092870_23.json 65536
python certify_simple.py
```

Numerical discovery additionally needs NumPy and SciPy:

```
OPENBLAS_NUM_THREADS=4 python experiment.py 7
OPENBLAS_NUM_THREADS=4 python experiment.py 8
OPENBLAS_NUM_THREADS=4 python subset_experiment.py 9 300
```

`make_witness.py` rounds free coefficients and repairs one coefficient to
make the normalization exact. `sparse.py` and `sparse_next.py` supply greedy
small-dictionary discovery. The exact JSON witnesses, not discovery scripts,
are the authoritative certificate inputs.

These finitely many certificates establish no common bound for infinitely
many increasing heads. They prove neither a bounded cofinal schedule nor RH.
````
<!-- END_FILE -->

## experiment.py

<!-- BEGIN_FILE experiment.py -->
````python
import os
os.environ['OPENBLAS_NUM_THREADS']='4'
import numpy as np
from scipy.special import polygamma
from scipy.linalg import solve
import itertools, json, time
from pathlib import Path
OUT=Path(__file__).parent

def dictionary(primes):
    ds=[1]
    mus={1:1}
    for p in primes:
        for d in list(ds): mus[d*p]=-mus[d]
        ds += [d*p for d in ds]
    return np.array(sorted(ds)[1:],dtype=np.int64),mus

def gram(primes):
    ds,mu=dictionary(primes); L=int(np.prod(primes))
    fn=OUT/f'gram_{L}.npz'
    if fn.exists(): return ds,mu,np.load(fn)['G']
    G=np.zeros((len(ds),len(ds))); t=time.time()
    for st in range(1,L+1,16384):
        ns=np.arange(st,min(st+16384,L+1),dtype=np.int64)
        A=(ns[:,None]%ds)/ds
        w=polygamma(1,ns/L)/(L*L*(np.pi*np.pi/6))
        B=A*np.sqrt(w[:,None]); G+=B.T@B
    np.savez(fn,G=G)
    print('GRAM',L,len(ds),'seconds',time.time()-t,flush=True)
    return ds,mu,G

def minimize(ds,mu,G,H):
    fixed=ds<=H; free=~fixed
    c=np.zeros(len(ds)); c[fixed]=[-mu[int(d)] for d in ds[fixed]]
    b=G[np.ix_(free,fixed)]@c[fixed]
    a=1/ds[free]; target=1-np.dot(1/ds[fixed],c[fixed])
    x=solve(G[np.ix_(free,free)],np.column_stack([b,a]),assume_a='pos')
    lam=(target+np.dot(a,x[:,0]))/np.dot(a,x[:,1])
    c[free]=-x[:,0]+lam*x[:,1]
    E=c@G@c
    return c,E,lam

if __name__=='__main__':
    import sys
    ps=[2,3,5,7,11,13,17,19,23][:int(sys.argv[1]) if len(sys.argv)>1 else 7]
    ds,mu,G=gram(ps); L=int(np.prod(ps))
    res=[]
    for H in range(max(2,ps[-1]-5),ps[-1]+2):
        c,E,lam=minimize(ds,mu,G,H)
        row={'period':L,'head':H,'energy_numerical':float(E),'normalization_error':float(np.dot(1/ds,c)-1),'coefficients':[[int(d),float(v)] for d,v in zip(ds,c)]}
        res.append(row)
        print('MIN',L,H,E,'maxc',max(abs(c)),flush=True)
    (OUT/f'candidates_{L}.json').write_text(json.dumps(res,indent=2))
````
<!-- END_FILE -->

## subset_experiment.py

<!-- BEGIN_FILE subset_experiment.py -->
````python
from experiment import *
import math

def gram_subset(primes,cutoff):
 ds,mu=dictionary(primes);ds=ds[ds<=cutoff]; L=math.prod(primes);path=OUT/f'gram_subset_{L}_{cutoff}.npz'
 if path.exists():return ds,mu,np.load(path)['G']
 G=np.zeros((len(ds),len(ds)));t=time.time()
 for i,d in enumerate(ds):
  for j,e in enumerate(ds[:i+1]):
   ell=math.lcm(int(d),int(e));ns=np.arange(1,ell+1,dtype=np.int64)
   w=polygamma(1,ns/ell)/(ell*ell*(np.pi*np.pi/6))
   G[i,j]=G[j,i]=np.sum((ns%d)/d*(ns%e)/e*w)
 np.savez(path,G=G);print('SUBGRAM',L,cutoff,len(ds),time.time()-t,flush=True)
 return ds,mu,G

if __name__=='__main__':
 import sys
 ps=[2,3,5,7,11,13,17,19,23,29,31][:int(sys.argv[1]) if len(sys.argv)>1 else 9];cutoff=int(sys.argv[2]) if len(sys.argv)>2 else 300
 ds,mu,G=gram_subset(ps,cutoff);L=math.prod(ps);rows=[]
 for H in sorted(set([15,ps[-2],ps[-1],ps[-1]+1])):
  c,e,_=minimize(ds,mu,G,H);print('SUBMIN',L,H,e,flush=True)
  rows.append({'period':L,'head':H,'energy_numerical':float(e),'coefficients':[[int(d),float(v)]for d,v in zip(ds,c)]})
 (OUT/f'candidates_subset_{L}_{cutoff}.json').write_text(json.dumps(rows,indent=2))
````
<!-- END_FILE -->

## make_witness.py

<!-- BEGIN_FILE make_witness.py -->
````python
import json,sys
from pathlib import Path
OUT=Path(__file__).parent
L=int(sys.argv[1]);H=int(sys.argv[2]);D=1000000
row=next(x for x in json.loads((OUT/f'candidates_{L}.json').read_text()) if x['head']==H)
cs=[[d,round(c*D)] for d,c in row['coefficients']]
cs[-1][1]=L*D-sum((L//d)*c for d,c in cs[:-1])
w={'period':L,'head':H,'denominator':D,'rounding_scale':10**14,'coefficients':cs}
p=OUT/f'witness_{L}_{H}.json';p.write_text(json.dumps(w,indent=2)+'\n');print(p)
````
<!-- END_FILE -->

## sparse.py

<!-- BEGIN_FILE sparse.py -->
````python
import math
from experiment import *
from fractions import Fraction
ps=[2,3,5,7,11,13,17];ds,mu,G=gram(ps);H=15
fixed=list(np.nonzero(ds<=H)[0]);free=list(np.nonzero(ds>H)[0])
def fit(ids):
 d=ds[ids];g=G[np.ix_(ids,ids)];c,e,l=minimize(d,mu,g,H);return c,e
ids=fixed+[int(np.where(ds==17)[0][0])]
for j in range(30):
 c,e=fit(ids)
 B=max(np.maximum(c,0).sum(),np.maximum(-c,0).sum())
 print('SPARSE',len(ids),'E',e,'B',B,'D',ds[ids].tolist(),flush=True)
 if e<.997:
  D=10**6;cc={int(d):Fraction(round(float(x)*D),D) for d,x in zip(ds[ids],c)}
  pivot=17;cc[pivot]=pivot*(1-sum(v/d for d,v in cc.items() if d!=pivot))
  den=math.lcm(*(x.denominator for x in cc.values()))
  w={'period':510510,'head':H,'denominator':den,'rounding_scale':10**14,'coefficients':[[d,int(x*den)] for d,x in sorted(cc.items())]}
  (OUT/f'sparse_{len(ids)}.json').write_text(json.dumps(w,indent=2))
 if len(ids)>=40:break
 candidates=[]
 for k in free:
  if k not in ids:
   _,ek=fit(ids+[k]);candidates.append((ek,k))
 ids.append(min(candidates)[1])
````
<!-- END_FILE -->

## sparse_next.py

<!-- BEGIN_FILE sparse_next.py -->
````python
from experiment import *
from fractions import Fraction as F
import math
ps=[2,3,5,7,11,13,17,19];ds,mu,G=gram(ps);L=int(np.prod(ps));H=int(__import__("sys").argv[1]) if len(__import__("sys").argv)>1 else 19
fixed=list(np.nonzero(ds<=H)[0]);free=list(np.nonzero(ds>H)[0])
def fit(ids):
 d=ds[ids];g=G[np.ix_(ids,ids)];c,e,l=minimize(d,mu,g,H);return c,e
init=min((fit(fixed+[k])[1],k) for k in free)[1];ids=fixed+[init]
for j in range(20):
 c,e=fit(ids);B=max(np.maximum(c,0).sum(),np.maximum(-c,0).sum())
 print('SPARSE',len(ids),'E',e,'B',B,'D',ds[ids].tolist(),flush=True)
 if e<.995:
  D=1000;cc={int(d):F(round(float(x)*D),D) for d,x in zip(ds[ids],c)}
  pivot=int(ds[init]);cc[pivot]=pivot*(1-sum(v/d for d,v in cc.items() if d!=pivot))
  den=math.lcm(*(x.denominator for x in cc.values()))
  w={'period':L,'head':H,'denominator':den,'rounding_scale':10**10,'coefficients':[[d,int(x*den)] for d,x in sorted(cc.items())]}
  (OUT/f'next_{H}_sparse_{len(ids)}.json').write_text(json.dumps(w,indent=2))
  if e<.987:break
 candidates=[]
 for k in free:
  if k not in ids:
   _,ek=fit(ids+[k]);candidates.append((ek,k))
 ids.append(min(candidates)[1])
````
<!-- END_FILE -->

## certify.py

<!-- BEGIN_FILE certify.py -->
````python
"""Standard-library exact integer checker for complete-energy witnesses.
No floating point enters the certificate verification. Candidate discovery uses
numpy/scipy separately. Residuewise infinite weights are upper bounded by
1/r^2 + 1/(L*r), the latter by the integral test on k>=1.
"""
import json,math,time
from pathlib import Path
OUT=Path(__file__).parent

def certify(w):
    L=w['period']; H=w['head']; D=w['denominator']; S=w['rounding_scale']; cs=w['coefficients']
    assert L>0 and D>0 and S>0 and 0<H<L
    assert len({d for d,c in cs})==len(cs)
    assert all(L%d==0 and d>1 for d,c in cs)
    assert all(all(d%(p*p) for p in range(2,math.isqrt(d)+1)) for d,c in cs)
    assert sum((L//d)*c for d,c in cs)==L*D
    Q=L*D; Q2=Q*Q; total=0; first_total=0; tail_total=0
    # Group exact integer coefficient weights. Each residue value is P/Q.
    terms=[(d,c*(L//d)) for d,c in cs if c]
    for r in range(1,L+1):
        P=sum(c*(r%d) for d,c in terms)
        if r<=H: assert P==Q
        p2=P*P*S
        a=Q2*r*r; b=Q2*L*r
        first_total+=(p2+a-1)//a
        tail_total+=(p2+b-1)//b
    total=first_total+tail_total
    # zeta(2)> sum_{n=1}^200 1/n² +1/201 > 16449/10000.
    # Verify lower rational by integer fractions; tail integral from201.
    from fractions import Fraction
    zl=sum((Fraction(1,n*n) for n in range(1,201)),Fraction(1,201))
    assert zl>Fraction(16449,10000)
    E=Fraction(total*10000,S*16449)
    assert E<1
    return {'raw_upper_numerator':total,'raw_upper_denominator':S,'q_energy_upper_numerator':E.numerator,'q_energy_upper_denominator':E.denominator,'first_period_upper_numerator':first_total,'tail_upper_numerator':tail_total}

if __name__=='__main__':
    import sys
    p=Path(sys.argv[1]); w=json.loads(p.read_text()); t=time.time(); cert=certify(w)
    print(json.dumps(cert)); print('SECONDS',time.time()-t)
    from fractions import Fraction
    print('UPPER',float(Fraction(cert['q_energy_upper_numerator'],cert['q_energy_upper_denominator'])))
    if 'certificate' in w: assert w['certificate']==cert
````
<!-- END_FILE -->

## certify_prefix.py

<!-- BEGIN_FILE certify_prefix.py -->
````python
"""Exact integer prefix-plus-infinite-tail energy certificate.
For F=P/T and |F|<=B, complete raw energy is at most
sum_{n=1}^K ceil(S P(n)^2/(T^2 n^2))/S + B^2/K.
The integral test bounds every omitted positive inverse-square term.
This checker uses no floating-point arithmetic or special functions.
"""
import json,math,sys,time
from pathlib import Path
from fractions import Fraction as F

def certify(w,K=65536,S=10**10):
 L=w['period'];H=w['head'];den=w['denominator'];cs={d:F(c,den) for d,c in w['coefficients']}
 assert L>0 and den>0 and S>0 and K>=H>0 and H<L
 assert len(cs)==len(w['coefficients'])
 assert all(d>1 and L%d==0 for d in cs)
 assert all(all(d%(p*p) for p in range(2,math.isqrt(d)+1)) for d in cs)
 assert sum(c/d for d,c in cs.items())==1
 scaled={d:c/d for d,c in cs.items()};T=math.lcm(*(x.denominator for x in scaled.values()))
 terms=[(d,int(x*T)) for d,x in scaled.items()]
 bp=sum((c*F(d-1,d) for d,c in cs.items() if c>0),F(0));bn=sum((-c*F(d-1,d) for d,c in cs.items() if c<0),F(0));B=math.ceil(max(bp,bn))
 total=0
 for n in range(1,K+1):
  P=sum(a*(n%d) for d,a in terms)
  if n<=H:assert P==T
  assert abs(P)<=B*T
  numer=S*P*P;div=T*T*n*n;total+=(numer+div-1)//div
 zl=sum((F(1,n*n) for n in range(1,201)),F(1,201));assert zl>F(16449,10000)
 raw=F(total,S)+F(B*B,K);bound=raw*F(10000,16449)
 assert bound<1
 return {'prefix':K,'rounding_scale':S,'scaled_value_denominator':T,'scaled_residue_coefficients':terms,'uniform_bound':B,'ceil_sum':total,'q_energy_upper_numerator':bound.numerator,'q_energy_upper_denominator':bound.denominator,'q_energy_upper_via_76_125':str(raw*F(76,125))}

if __name__=='__main__':
 p=Path(sys.argv[1]);w=json.loads(p.read_text());t=time.time();out=certify(w,int(sys.argv[2]) if len(sys.argv)>2 else 65536);recorded=w.get('prefix_certificate');assert recorded is None or json.loads(json.dumps(out))==recorded;print(json.dumps({k:v for k,v in out.items() if k!='scaled_residue_coefficients'}));print('UPPER',float(F(out['q_energy_upper_numerator'],out['q_energy_upper_denominator'])),'SECONDS',time.time()-t)
````
<!-- END_FILE -->

## certify_simple.py

<!-- BEGIN_FILE certify_simple.py -->
````python
"""Exact small-block certificate for the fourteen-atom L=510510, H=15 witness."""
import json,math
from pathlib import Path
from fractions import Fraction as F
OUT=Path(__file__).parent

def verify():
 w=json.loads((OUT/'simple_14.json').read_text());cs={d:F(c,w['denominator'])for d,c in w['coefficients']}
 assert sum(c/d for d,c in cs.items())==1
 assert sum((F(1,n*n)for n in range(1,201)),F(1,201))>F(125,76)
 assert all(510510%d==0 for d in cs)
 blocks=[{d:cs[d] for d in [2,3,5,6,10,15,30]}, {d:cs[d]for d in[7,14]}, {11:cs[11]}, {13:cs[13]}, {d:cs[d]for d in[17,34,51]}]
 bounds=[]
 for block in blocks:
  period=math.lcm(*block)
  vs=[sum((c*F(r%d,d)for d,c in block.items()),F(0))for r in range(period)]
  bounds.append((min(vs),max(vs)))
 assert bounds==[(F(-2,3),F(14,15)),(F(-1,2),F(3,7)),(F(0),F(10,11)),(F(0),F(12,13)),(F(-2),F(6584,15015))]
 assert sum(x[0]for x in bounds)>-4
 assert sum(x[1]for x in bounds)<4
 terms=[(d,int(c/d*510510))for d,c in cs.items()]
 assert all(F(a,510510)==cs[d]/d for d,a in terms)
 S=10**8;K=768;total=0
 for n in range(1,K+1):
  P=sum(a*(n%d)for d,a in terms)
  if n<=15:assert P==510510
  denom=510510**2*n*n;total+=(S*P*P+denom-1)//denom
 assert total==162016546
 bound=F(76,125)*(F(total,S)+F(16,K))
 assert bound==F(4676846561,4687500000)<1
 return {'prefix':K,'rounding_scale':S,'ceil_sum':total,'uniform_bound':4,'energy_upper':str(bound),'block_bounds':[[str(a),str(b)]for a,b in bounds]}

if __name__=='__main__':
 print(json.dumps(verify(),indent=2))
````
<!-- END_FILE -->

## verify_all.py

<!-- BEGIN_FILE verify_all.py -->
````python
"""Read-only exact checks of every published witness and its recorded output."""
import json
from pathlib import Path
from fractions import Fraction
from certify import certify as periodic
from certify_prefix import certify as prefix
from certify_simple import verify as simple
ROOT=Path(__file__).parent
manifest=json.loads((ROOT/'manifest.json').read_text())
for case in manifest['certificates']:
    w=json.loads((ROOT/case['file']).read_text())
    if case['method']=='periodic':
        got=periodic(w)
        assert got==w['certificate']
    elif case['method']=='prefix':
        recorded=w['prefix_certificate']
        got=prefix(w,recorded['prefix'],recorded['rounding_scale'])
        assert json.loads(json.dumps(got))==recorded
    else:
        got=simple()
    if case['method']=='simple':
        energy=Fraction(got['energy_upper'])
    else:
        energy=Fraction(got['q_energy_upper_numerator'],got['q_energy_upper_denominator'])
    assert str(energy)==case['energy_upper']
    assert energy<1
    print(case['file']+': PASS; complete energy <= '+str(energy))
print('All recorded exact certificates reproduced; no source files modified.')
````
<!-- END_FILE -->

## manifest.json

<!-- BEGIN_FILE manifest.json -->
````json
{
  "status": "exact finite computational certificates; not Lean kernel checks",
  "certificates": [
    {
      "file": "witness_510510_15.json",
      "method": "periodic",
      "period": 510510,
      "head": 15,
      "energy_upper": "80205043617271/82245000000000"
    },
    {
      "file": "witness_510510_17.json",
      "method": "periodic",
      "period": 510510,
      "head": 17,
      "energy_upper": "162709990384841/164490000000000"
    },
    {
      "file": "next_17_sparse_17.json",
      "method": "prefix",
      "period": 9699690,
      "head": 17,
      "energy_upper": "2717400901/2741500000"
    },
    {
      "file": "next_sparse_17.json",
      "method": "prefix",
      "period": 9699690,
      "head": 19,
      "energy_upper": "543483191/548300000"
    },
    {
      "file": "witness_223092870_23.json",
      "method": "prefix",
      "period": 223092870,
      "head": 23,
      "energy_upper": "17378821007/17545600000"
    },
    {
      "file": "simple_14.json",
      "method": "simple",
      "period": 510510,
      "head": 15,
      "energy_upper": "4676846561/4687500000"
    }
  ]
}
````
<!-- END_FILE -->

## numerical_summary.json

<!-- BEGIN_FILE numerical_summary.json -->
````json
{
  "status": "floating-point discovery only; special-function complete tails",
  "results": [
    {
      "period": 510510,
      "head": 12,
      "energy_numerical": 0.9619824299478816,
      "dictionary": "all divisors > 1"
    },
    {
      "period": 510510,
      "head": 13,
      "energy_numerical": 0.9643708449304352,
      "dictionary": "all divisors > 1"
    },
    {
      "period": 510510,
      "head": 14,
      "energy_numerical": 0.9678902581261455,
      "dictionary": "all divisors > 1"
    },
    {
      "period": 510510,
      "head": 15,
      "energy_numerical": 0.9751351445376681,
      "dictionary": "all divisors > 1"
    },
    {
      "period": 510510,
      "head": 16,
      "energy_numerical": 0.9751351445376681,
      "dictionary": "all divisors > 1"
    },
    {
      "period": 510510,
      "head": 17,
      "energy_numerical": 0.9891328614338042,
      "dictionary": "all divisors > 1"
    },
    {
      "period": 510510,
      "head": 18,
      "energy_numerical": 0.9891328614338042,
      "dictionary": "all divisors > 1"
    },
    {
      "period": 9699690,
      "head": 14,
      "energy_numerical": 0.9655250770992145,
      "dictionary": "all divisors > 1"
    },
    {
      "period": 9699690,
      "head": 15,
      "energy_numerical": 0.9721282388540168,
      "dictionary": "all divisors > 1"
    },
    {
      "period": 9699690,
      "head": 16,
      "energy_numerical": 0.9721282388540168,
      "dictionary": "all divisors > 1"
    },
    {
      "period": 9699690,
      "head": 17,
      "energy_numerical": 0.9758656518545655,
      "dictionary": "all divisors > 1"
    },
    {
      "period": 9699690,
      "head": 18,
      "energy_numerical": 0.9758656518545655,
      "dictionary": "all divisors > 1"
    },
    {
      "period": 9699690,
      "head": 19,
      "energy_numerical": 0.9783718881637521,
      "dictionary": "all divisors > 1"
    },
    {
      "period": 9699690,
      "head": 20,
      "energy_numerical": 0.9783718881637521,
      "dictionary": "all divisors > 1"
    },
    {
      "period": 30030,
      "head": 15,
      "energy_numerical": 1.01925432764544,
      "dictionary": "all divisors > 1"
    },
    {
      "period": 223092870,
      "head": 15,
      "energy_numerical": 0.9736096983766074,
      "dictionary": "divisors 1 < d <= 300; 68 atoms"
    },
    {
      "period": 223092870,
      "head": 19,
      "energy_numerical": 0.9787835910215111,
      "dictionary": "divisors 1 < d <= 300; 68 atoms"
    },
    {
      "period": 223092870,
      "head": 23,
      "energy_numerical": 0.9859942421485601,
      "dictionary": "divisors 1 < d <= 300; 68 atoms"
    },
    {
      "period": 223092870,
      "head": 24,
      "energy_numerical": 0.9859942421485601,
      "dictionary": "divisors 1 < d <= 300; 68 atoms"
    }
  ]
}
````
<!-- END_FILE -->

## witness_510510_15.json

<!-- BEGIN_FILE witness_510510_15.json -->
````json
{
  "period": 510510,
  "head": 15,
  "denominator": 1000000,
  "rounding_scale": 100000000000000,
  "coefficients": [
    [
      2,
      1000000
    ],
    [
      3,
      1000000
    ],
    [
      5,
      1000000
    ],
    [
      6,
      -1000000
    ],
    [
      7,
      1000000
    ],
    [
      10,
      -1000000
    ],
    [
      11,
      1000000
    ],
    [
      13,
      1000000
    ],
    [
      14,
      -1000000
    ],
    [
      15,
      -1000000
    ],
    [
      17,
      2317360
    ],
    [
      21,
      -354964
    ],
    [
      22,
      -192282
    ],
    [
      26,
      -426584
    ],
    [
      30,
      1948716
    ],
    [
      33,
      -527652
    ],
    [
      34,
      -1812376
    ],
    [
      35,
      -583536
    ],
    [
      39,
      -156789
    ],
    [
      42,
      1279485
    ],
    [
      51,
      -1430695
    ],
    [
      55,
      -310064
    ],
    [
      65,
      -865809
    ],
    [
      66,
      407716
    ],
    [
      70,
      1411301
    ],
    [
      77,
      -245677
    ],
    [
      78,
      414301
    ],
    [
      85,
      -2025818
    ],
    [
      91,
      -904763
    ],
    [
      102,
      1803924
    ],
    [
      105,
      694229
    ],
    [
      110,
      844614
    ],
    [
      119,
      -2602398
    ],
    [
      130,
      669245
    ],
    [
      143,
      -692252
    ],
    [
      154,
      -513881
    ],
    [
      165,
      505362
    ],
    [
      170,
      1625596
    ],
    [
      182,
      634792
    ],
    [
      187,
      -1325261
    ],
    [
      195,
      975271
    ],
    [
      210,
      -2379187
    ],
    [
      221,
      -1775546
    ],
    [
      231,
      487031
    ],
    [
      238,
      1892352
    ],
    [
      255,
      1432043
    ],
    [
      273,
      233276
    ],
    [
      286,
      -859699
    ],
    [
      330,
      -2204315
    ],
    [
      357,
      1812903
    ],
    [
      374,
      797027
    ],
    [
      385,
      91982
    ],
    [
      390,
      -1876363
    ],
    [
      429,
      1090772
    ],
    [
      442,
      1231258
    ],
    [
      455,
      984669
    ],
    [
      462,
      -747313
    ],
    [
      510,
      -3150682
    ],
    [
      546,
      -1291063
    ],
    [
      561,
      877984
    ],
    [
      595,
      2355069
    ],
    [
      663,
      1947276
    ],
    [
      714,
      -2268348
    ],
    [
      715,
      -446629
    ],
    [
      770,
      -306847
    ],
    [
      858,
      382420
    ],
    [
      910,
      -1493925
    ],
    [
      935,
      956019
    ],
    [
      1001,
      1204773
    ],
    [
      1105,
      2481678
    ],
    [
      1122,
      -988661
    ],
    [
      1155,
      -96846
    ],
    [
      1190,
      -2672634
    ],
    [
      1309,
      1681465
    ],
    [
      1326,
      -2143034
    ],
    [
      1365,
      -1408816
    ],
    [
      1430,
      1170646
    ],
    [
      1547,
      3647348
    ],
    [
      1785,
      -3268146
    ],
    [
      1870,
      -205688
    ],
    [
      2002,
      1271490
    ],
    [
      2145,
      -162939
    ],
    [
      2210,
      -1991671
    ],
    [
      2310,
      1943404
    ],
    [
      2431,
      808827
    ],
    [
      2618,
      -856955
    ],
    [
      2730,
      3252067
    ],
    [
      2805,
      -1095160
    ],
    [
      3003,
      -1267885
    ],
    [
      3094,
      -2281342
    ],
    [
      3315,
      -1891560
    ],
    [
      3570,
      5421039
    ],
    [
      3927,
      -1457778
    ],
    [
      4290,
      1271233
    ],
    [
      4641,
      -3762194
    ],
    [
      4862,
      581998
    ],
    [
      5005,
      719213
    ],
    [
      5610,
      686361
    ],
    [
      6006,
      -80194
    ],
    [
      6545,
      -354890
    ],
    [
      6630,
      2716949
    ],
    [
      7293,
      -2127787
    ],
    [
      7735,
      -3611445
    ],
    [
      7854,
      1870064
    ],
    [
      9282,
      3834848
    ],
    [
      10010,
      -2333238
    ],
    [
      12155,
      350494
    ],
    [
      13090,
      -1100706
    ],
    [
      14586,
      -170940
    ],
    [
      15015,
      496167
    ],
    [
      15470,
      3216958
    ],
    [
      17017,
      -3203740
    ],
    [
      19635,
      -201714
    ],
    [
      23205,
      3703114
    ],
    [
      24310,
      -2383673
    ],
    [
      30030,
      -902515
    ],
    [
      34034,
      612580
    ],
    [
      36465,
      683955
    ],
    [
      39270,
      275245
    ],
    [
      46410,
      -4814131
    ],
    [
      51051,
      3992533
    ],
    [
      72930,
      -582866
    ],
    [
      85085,
      1301268
    ],
    [
      102102,
      -1252249
    ],
    [
      170170,
      217705
    ],
    [
      255255,
      -796956
    ],
    [
      510510,
      769556
    ]
  ],
  "certificate": {
    "raw_upper_numerator": 160410087234542,
    "raw_upper_denominator": 100000000000000,
    "q_energy_upper_numerator": 80205043617271,
    "q_energy_upper_denominator": 82245000000000,
    "first_period_upper_numerator": 160401427608130,
    "tail_upper_numerator": 8659626412
  }
}
````
<!-- END_FILE -->

## witness_510510_17.json

<!-- BEGIN_FILE witness_510510_17.json -->
````json
{
  "period": 510510,
  "head": 17,
  "denominator": 1000000,
  "rounding_scale": 100000000000000,
  "coefficients": [
    [
      2,
      1000000
    ],
    [
      3,
      1000000
    ],
    [
      5,
      1000000
    ],
    [
      6,
      -1000000
    ],
    [
      7,
      1000000
    ],
    [
      10,
      -1000000
    ],
    [
      11,
      1000000
    ],
    [
      13,
      1000000
    ],
    [
      14,
      -1000000
    ],
    [
      15,
      -1000000
    ],
    [
      17,
      1000000
    ],
    [
      21,
      676504
    ],
    [
      22,
      26632
    ],
    [
      26,
      -314622
    ],
    [
      30,
      1879129
    ],
    [
      33,
      -429383
    ],
    [
      34,
      -662867
    ],
    [
      35,
      -571032
    ],
    [
      39,
      -171377
    ],
    [
      42,
      295475
    ],
    [
      51,
      -495656
    ],
    [
      55,
      -438939
    ],
    [
      65,
      -1358979
    ],
    [
      66,
      56063
    ],
    [
      70,
      1407471
    ],
    [
      77,
      -261305
    ],
    [
      78,
      352766
    ],
    [
      85,
      -1039309
    ],
    [
      91,
      -1003591
    ],
    [
      102,
      908024
    ],
    [
      105,
      67123
    ],
    [
      110,
      674280
    ],
    [
      119,
      -1583197
    ],
    [
      130,
      1131611
    ],
    [
      143,
      -1177857
    ],
    [
      154,
      -550309
    ],
    [
      165,
      464223
    ],
    [
      170,
      773056
    ],
    [
      182,
      639692
    ],
    [
      187,
      -959015
    ],
    [
      195,
      1235986
    ],
    [
      210,
      -1726530
    ],
    [
      221,
      -862671
    ],
    [
      231,
      -102159
    ],
    [
      238,
      882962
    ],
    [
      255,
      770836
    ],
    [
      273,
      14184
    ],
    [
      286,
      55661
    ],
    [
      330,
      -1075723
    ],
    [
      357,
      487441
    ],
    [
      374,
      510439
    ],
    [
      385,
      346129
    ],
    [
      390,
      -1940069
    ],
    [
      429,
      1158206
    ],
    [
      442,
      180097
    ],
    [
      455,
      1326069
    ],
    [
      462,
      11190
    ],
    [
      510,
      -2185131
    ],
    [
      546,
      -723952
    ],
    [
      561,
      135340
    ],
    [
      595,
      1309509
    ],
    [
      663,
      572091
    ],
    [
      714,
      -760847
    ],
    [
      715,
      725913
    ],
    [
      770,
      -582584
    ],
    [
      858,
      106097
    ],
    [
      910,
      -1824251
    ],
    [
      935,
      564873
    ],
    [
      1001,
      1139313
    ],
    [
      1105,
      1807709
    ],
    [
      1122,
      -444928
    ],
    [
      1155,
      1081
    ],
    [
      1190,
      -1404515
    ],
    [
      1309,
      971076
    ],
    [
      1326,
      -1059044
    ],
    [
      1365,
      -1330111
    ],
    [
      1430,
      -412826
    ],
    [
      1547,
      2932002
    ],
    [
      1785,
      -1394196
    ],
    [
      1870,
      83037
    ],
    [
      2002,
      736051
    ],
    [
      2145,
      -1022643
    ],
    [
      2210,
      -1389617
    ],
    [
      2310,
      944738
    ],
    [
      2431,
      756728
    ],
    [
      2618,
      -251093
    ],
    [
      2730,
      2739516
    ],
    [
      2805,
      -444011
    ],
    [
      3003,
      -1166057
    ],
    [
      3094,
      -1494256
    ],
    [
      3315,
      -1459495
    ],
    [
      3570,
      2631531
    ],
    [
      3927,
      -338984
    ],
    [
      4290,
      1662051
    ],
    [
      4641,
      -2026614
    ],
    [
      4862,
      288696
    ],
    [
      5005,
      -724173
    ],
    [
      5610,
      74819
    ],
    [
      6006,
      185283
    ],
    [
      6545,
      40722
    ],
    [
      6630,
      2370359
    ],
    [
      7293,
      -802657
    ],
    [
      7735,
      -3105078
    ],
    [
      7854,
      463814
    ],
    [
      9282,
      2057922
    ],
    [
      10010,
      -120435
    ],
    [
      12155,
      -327200
    ],
    [
      13090,
      -1496459
    ],
    [
      14586,
      -447085
    ],
    [
      15015,
      1340081
    ],
    [
      15470,
      2778463
    ],
    [
      17017,
      -2223038
    ],
    [
      19635,
      -1159673
    ],
    [
      23205,
      2765585
    ],
    [
      24310,
      -771063
    ],
    [
      30030,
      -1578705
    ],
    [
      34034,
      356578
    ],
    [
      36465,
      627944
    ],
    [
      39270,
      1221015
    ],
    [
      46410,
      -3839413
    ],
    [
      51051,
      2546553
    ],
    [
      72930,
      -879978
    ],
    [
      85085,
      1281127
    ],
    [
      102102,
      -628524
    ],
    [
      170170,
      -27991
    ],
    [
      255255,
      -529262
    ],
    [
      510510,
      643203
    ]
  ],
  "certificate": {
    "raw_upper_numerator": 162709990384841,
    "raw_upper_denominator": 100000000000000,
    "q_energy_upper_numerator": 162709990384841,
    "q_energy_upper_denominator": 164490000000000,
    "first_period_upper_numerator": 162704860853803,
    "tail_upper_numerator": 5129531038
  }
}
````
<!-- END_FILE -->

## simple_14.json

<!-- BEGIN_FILE simple_14.json -->
````json
{
  "period": 510510,
  "head": 15,
  "denominator": 30030,
  "rounding_scale": 100000000000000,
  "coefficients": [
    [
      2,
      30030
    ],
    [
      3,
      30030
    ],
    [
      5,
      30030
    ],
    [
      6,
      -30030
    ],
    [
      7,
      30030
    ],
    [
      10,
      -30030
    ],
    [
      11,
      30030
    ],
    [
      13,
      30030
    ],
    [
      14,
      -30030
    ],
    [
      15,
      -30030
    ],
    [
      17,
      59036
    ],
    [
      30,
      30030
    ],
    [
      34,
      -60060
    ],
    [
      51,
      -45045
    ]
  ]
}
````
<!-- END_FILE -->

## next_17_sparse_17.json

<!-- BEGIN_FILE next_17_sparse_17.json -->
````json
{
  "period": 9699690,
  "head": 17,
  "denominator": 170170000,
  "rounding_scale": 10000000000,
  "coefficients": [
    [
      2,
      170170000
    ],
    [
      3,
      170170000
    ],
    [
      5,
      170170000
    ],
    [
      6,
      -170170000
    ],
    [
      7,
      170170000
    ],
    [
      10,
      -170170000
    ],
    [
      11,
      170170000
    ],
    [
      13,
      170170000
    ],
    [
      14,
      -170170000
    ],
    [
      15,
      -170170000
    ],
    [
      17,
      170170000
    ],
    [
      19,
      166942819
    ],
    [
      30,
      169148980
    ],
    [
      34,
      -172892720
    ],
    [
      38,
      -142432290
    ],
    [
      51,
      -145835690
    ],
    [
      65,
      -156386230
    ]
  ],
  "prefix_certificate": {
    "prefix": 8192,
    "rounding_scale": 10000000000,
    "scaled_value_denominator": 9699690000,
    "scaled_residue_coefficients": [
      [
        2,
        4849845000
      ],
      [
        3,
        3233230000
      ],
      [
        5,
        1939938000
      ],
      [
        6,
        -1616615000
      ],
      [
        7,
        1385670000
      ],
      [
        10,
        -969969000
      ],
      [
        11,
        881790000
      ],
      [
        13,
        746130000
      ],
      [
        14,
        -692835000
      ],
      [
        15,
        -646646000
      ],
      [
        17,
        570570000
      ],
      [
        19,
        500828457
      ],
      [
        30,
        321383062
      ],
      [
        34,
        -289849560
      ],
      [
        38,
        -213648435
      ],
      [
        51,
        -162992830
      ],
      [
        65,
        -137138694
      ]
    ],
    "uniform_bound": 8,
    "ceil_sum": 16226280406,
    "q_energy_upper_numerator": 2717400901,
    "q_energy_upper_denominator": 2741500000,
    "q_energy_upper_via_76_125": "154891851357/156250000000"
  }
}
````
<!-- END_FILE -->

## next_sparse_17.json

<!-- BEGIN_FILE next_sparse_17.json -->
````json
{
  "period": 9699690,
  "head": 19,
  "denominator": 255255000,
  "rounding_scale": 10000000000,
  "coefficients": [
    [
      2,
      255255000
    ],
    [
      3,
      255255000
    ],
    [
      5,
      255255000
    ],
    [
      6,
      -255255000
    ],
    [
      7,
      255255000
    ],
    [
      10,
      -255255000
    ],
    [
      11,
      255255000
    ],
    [
      13,
      255255000
    ],
    [
      14,
      -255255000
    ],
    [
      15,
      -255255000
    ],
    [
      17,
      255255000
    ],
    [
      19,
      255255000
    ],
    [
      30,
      249384135
    ],
    [
      34,
      -260870610
    ],
    [
      38,
      -217614037
    ],
    [
      51,
      -218753535
    ],
    [
      65,
      -232026795
    ]
  ],
  "prefix_certificate": {
    "prefix": 8192,
    "rounding_scale": 10000000000,
    "scaled_value_denominator": 9699690000,
    "scaled_residue_coefficients": [
      [
        2,
        4849845000
      ],
      [
        3,
        3233230000
      ],
      [
        5,
        1939938000
      ],
      [
        6,
        -1616615000
      ],
      [
        7,
        1385670000
      ],
      [
        10,
        -969969000
      ],
      [
        11,
        881790000
      ],
      [
        13,
        746130000
      ],
      [
        14,
        -692835000
      ],
      [
        15,
        -646646000
      ],
      [
        17,
        570570000
      ],
      [
        19,
        510510000
      ],
      [
        30,
        315886571
      ],
      [
        34,
        -291561270
      ],
      [
        38,
        -217614037
      ],
      [
        51,
        -162992830
      ],
      [
        65,
        -135646434
      ]
    ],
    "uniform_bound": 8,
    "ceil_sum": 16226370730,
    "q_energy_upper_numerator": 543483191,
    "q_energy_upper_denominator": 548300000,
    "q_energy_upper_via_76_125": "30978541887/31250000000"
  }
}
````
<!-- END_FILE -->

## witness_223092870_23.json

<!-- BEGIN_FILE witness_223092870_23.json -->
````json
{
  "period": 223092870,
  "head": 23,
  "denominator": 8580495000000,
  "coefficients": [
    [
      2,
      8580495000000
    ],
    [
      3,
      8580495000000
    ],
    [
      5,
      8580495000000
    ],
    [
      6,
      -8580495000000
    ],
    [
      7,
      8580495000000
    ],
    [
      10,
      -8580495000000
    ],
    [
      11,
      8580495000000
    ],
    [
      13,
      8580495000000
    ],
    [
      14,
      -8580495000000
    ],
    [
      15,
      -8580495000000
    ],
    [
      17,
      8580495000000
    ],
    [
      19,
      8580495000000
    ],
    [
      21,
      -8580495000000
    ],
    [
      22,
      -8580495000000
    ],
    [
      23,
      8580495000000
    ],
    [
      26,
      2191580022944
    ],
    [
      30,
      16576632549015
    ],
    [
      33,
      -3262664579790
    ],
    [
      34,
      -6194568238320
    ],
    [
      35,
      -4584652863945
    ],
    [
      38,
      -3102243645270
    ],
    [
      39,
      -3786941404785
    ],
    [
      42,
      15305569502685
    ],
    [
      46,
      -1194996958155
    ],
    [
      51,
      -7373794246665
    ],
    [
      55,
      -3952948241550
    ],
    [
      57,
      -4281023467875
    ],
    [
      65,
      -4427947283760
    ],
    [
      66,
      6464064425280
    ],
    [
      69,
      -5267728909905
    ],
    [
      70,
      10454852649780
    ],
    [
      77,
      -4293937112850
    ],
    [
      78,
      -374959051005
    ],
    [
      85,
      -4983774588870
    ],
    [
      91,
      -9694449182880
    ],
    [
      95,
      -3924177841815
    ],
    [
      102,
      7961395124760
    ],
    [
      105,
      6507181412655
    ],
    [
      110,
      6238903655985
    ],
    [
      114,
      3936293500755
    ],
    [
      115,
      -5866853392785
    ],
    [
      119,
      -9425347698690
    ],
    [
      130,
      -1758958572525
    ],
    [
      133,
      -3800584391835
    ],
    [
      138,
      2553563892495
    ],
    [
      143,
      -4252613448930
    ],
    [
      154,
      4898398663620
    ],
    [
      161,
      -2724264260025
    ],
    [
      165,
      373835006160
    ],
    [
      170,
      2449036302405
    ],
    [
      182,
      2878696009035
    ],
    [
      187,
      -3053815331490
    ],
    [
      190,
      3834494508075
    ],
    [
      195,
      5026702805355
    ],
    [
      209,
      -4668604427025
    ],
    [
      210,
      -16045062303270
    ],
    [
      221,
      -1435482491520
    ],
    [
      230,
      4663876574280
    ],
    [
      231,
      815679015690
    ],
    [
      238,
      7917179834025
    ],
    [
      247,
      -3537163195335
    ],
    [
      253,
      -4654661122650
    ],
    [
      255,
      4446009225735
    ],
    [
      266,
      1224393734025
    ],
    [
      273,
      4368141233610
    ],
    [
      285,
      1779328667655
    ],
    [
      286,
      517052048205
    ],
    [
      299,
      -8448398279475
    ]
  ],
  "prefix_certificate": {
    "prefix": 65536,
    "rounding_scale": 10000000000,
    "scaled_value_denominator": 223092870000000,
    "scaled_residue_coefficients": [
      [
        2,
        111546435000000
      ],
      [
        3,
        74364290000000
      ],
      [
        5,
        44618574000000
      ],
      [
        6,
        -37182145000000
      ],
      [
        7,
        31870410000000
      ],
      [
        10,
        -22309287000000
      ],
      [
        11,
        20281170000000
      ],
      [
        13,
        17160990000000
      ],
      [
        14,
        -15935205000000
      ],
      [
        15,
        -14872858000000
      ],
      [
        17,
        13123110000000
      ],
      [
        19,
        11741730000000
      ],
      [
        21,
        -10623470000000
      ],
      [
        22,
        -10140585000000
      ],
      [
        23,
        9699690000000
      ],
      [
        26,
        2191580022944
      ],
      [
        30,
        14366414875813
      ],
      [
        33,
        -2570584214380
      ],
      [
        34,
        -4737022770480
      ],
      [
        35,
        -3405742127502
      ],
      [
        38,
        -2122587757290
      ],
      [
        39,
        -2524627603190
      ],
      [
        42,
        9474876358805
      ],
      [
        46,
        -675433063305
      ],
      [
        51,
        -3759189223790
      ],
      [
        55,
        -1868666441460
      ],
      [
        57,
        -1952747546750
      ],
      [
        65,
        -1771178913504
      ],
      [
        66,
        2546449622080
      ],
      [
        69,
        -1984941328370
      ],
      [
        70,
        3883230984204
      ],
      [
        77,
        -1449900843300
      ],
      [
        78,
        -124986350335
      ],
      [
        85,
        -1524448697772
      ],
      [
        91,
        -2769842623680
      ],
      [
        95,
        -1073985514602
      ],
      [
        102,
        2029375227880
      ],
      [
        105,
        1611302064086
      ],
      [
        110,
        1474649955051
      ],
      [
        114,
        897751149295
      ],
      [
        115,
        -1326419027934
      ],
      [
        119,
        -2059319665260
      ],
      [
        130,
        -351791714505
      ],
      [
        133,
        -742971384870
      ],
      [
        138,
        481106240615
      ],
      [
        143,
        -773202445260
      ],
      [
        154,
        827002371780
      ],
      [
        161,
        -439943296650
      ],
      [
        165,
        58907334304
      ],
      [
        170,
        374558493309
      ],
      [
        182,
        411242287005
      ],
      [
        187,
        -424594645020
      ],
      [
        190,
        524720301105
      ],
      [
        195,
        670227040714
      ],
      [
        209,
        -580783325850
      ],
      [
        210,
        -1986531523262
      ],
      [
        221,
        -168880293120
      ],
      [
        230,
        527220830136
      ],
      [
        231,
        91808027740
      ],
      [
        238,
        864901998675
      ],
      [
        247,
        -372332967930
      ],
      [
        253,
        -478344621300
      ],
      [
        255,
        453318587722
      ],
      [
        266,
        119677583025
      ],
      [
        273,
        416013450820
      ],
      [
        285,
        162324720558
      ],
      [
        286,
        47004731655
      ],
      [
        299,
        -734643328650
      ]
    ],
    "uniform_bound": 22,
    "ceil_sum": 16218792155,
    "q_energy_upper_numerator": 17378821007,
    "q_energy_upper_denominator": 17545600000,
    "q_energy_upper_via_76_125": "990592797399/1000000000000"
  }
}
````
<!-- END_FILE -->
