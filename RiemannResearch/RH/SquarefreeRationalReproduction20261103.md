# Complete-Q rational certificate reproduction — 3 November 2026

The executable scripts remain in the user's approved review archive. This
repository document records their complete reproducible source and data;
it makes no changes to the protected tools directory.

Save each fenced block below under its displayed relative filename in one
local working directory. Create the reference subdirectory. Then run:

```sh
python verify_certificate.py
```

The strongest saved certificate is checked using the Python standard
library only. The full generation and diagnostics additionally use NumPy
and SciPy; see the companion research memorandum for the exact tail proof
and verification distinctions. Floating optimization never supplies an
assumption to the exact arithmetic certificate.

The reference Python module is copied from the pre-existing
PrimeTensorCRTReproduction20261102.md at commit f7cf4a1a. Its full source is
retained below for standalone reproduction.

## verify_certificate.py

```python
"""Standard-library-only verifier for the strongest saved certificate.

Run: python verify_certificate.py
Requires certificates.json in the current directory. No floats, SciPy,
NumPy, optimizer, zeta evaluation, or unverified truncated tail is used.
"""
import json, math
from array import array
from fractions import Fraction as Q

rec=next(x for x in json.load(open('certificates.json')) if x['label']=='squarefree_200')
ds=rec['dictionary'];a=rec['coefficient_numerators'];q=rec['coefficient_denominator'];N=rec['N'];S=rec['rounding_scale']
assert ds==[d for d in range(2,201) if all(d%(k*k) for k in range(2,math.isqrt(d)+1))]
assert len(a)==len(ds)==121 and q==10**6
c=[Q(x,q) for x in a]
mean=lambda d,e: Q((d-1)*(e-1),4*d*e)+Q(math.gcd(d,e)**2-1,12*d*e)
mu=1-2*sum(x*Q(d-1,2*d) for d,x in zip(ds,c))+sum(x*y*mean(d,e) for d,x in zip(ds,c) for e,y in zip(ds,c))
D=(2*sum(abs(x)*d for d,x in zip(ds,c))+sum(abs(x*y)*math.lcm(d,e) for d,x in zip(ds,c) for e,y in zip(ds,c)))/4
assert mu==Q(rec['period_mean_square']) and D==Q(rec['centered_partial_sum_bound'])
L=math.lcm(*ds);den=q*L;step=-sum(x*(L//d) for d,x in zip(ds,a));A=den;total=0
jumps=array('q',[0])*(N+1)
assert sum(map(abs,a))<2**63
for d,x in zip(ds,a):
    for n in range(d,N+1,d):jumps[n]+=x
for n in range(1,N+1):
    A+=step+L*jumps[n]
    total+=S*A*A//(den*den*n*n)
headlo=Q(total,S);headhi=Q(total+N,S)
assert headlo==Q(rec['head_lower']) and headhi==Q(rec['head_upper'])
T=10000;Z=sum(S//(n*n) for n in range(1,T+1))
zl=Q(Z,S)+Q(1,T+1);zu=Q(Z+T,S)+Q(1,T)
assert zl==Q(rec['zeta_lower']) and zu==Q(rec['zeta_upper'])
upper=(headhi+mu/N+D/(N+1)**2)/zl
lower=max(Q(0),(headlo+mu/(N+1)-D/(N+1)**2)/zu)
assert upper==Q(rec['full_error_upper']) and lower==Q(rec['full_error_lower'])
assert upper<Q(5873,10**6)
assert Q(5873,10**6)<Q(59,10000)<Q(59,1000)
print('PASS: exact complete-Q certificate < 5873/1000000')
print('PASS: every conductor is squarefree; the infinite tail is included')
print('This is an arithmetic certificate check, not a Lean kernel check.')
```

## certify.py

```python
"""Exact-integer complete Q certificates. No floating input is trusted.

Input coefficient numerators are integers chosen by a separate diagnostic.
All verification arithmetic below is integer/Fraction arithmetic.
The tail proof and period-mean identity are in the accompanying
SquarefreeRationalUpperBounds20261103.md research memorandum.
"""
import json, math
from fractions import Fraction as Q
from pathlib import Path
import numpy as np

S = 10**20

def sf(d):
    return d >= 2 and all(d % (p*p) for p in range(2,math.isqrt(d)+1))

def zeta_interval(T=10000):
    z=sum(S//(n*n) for n in range(1,T+1))
    return Q(z,S)+Q(1,T+1),Q(z+T,S)+Q(1,T)

def mean_product(d,e):
    return Q((d-1)*(e-1),4*d*e)+Q(math.gcd(d,e)**2-1,12*d*e)

def check_mean_identity(ds):
    # Every product sum below is below signed int64 capacity.
    for i,d in enumerate(ds):
        for e in ds[:i+1]:
            l=math.lcm(d,e)
            assert l*(d-1)*(e-1)<2**63
            n=np.arange(l,dtype=np.int64)
            s=int(((n%d)*(n%e)).sum(dtype=np.int64))
            assert Q(s,l*d*e)==mean_product(d,e)

def certify(item,N):
    ds=item['dictionary']; a=item['coefficient_numerators_1e6']; scale=10**6
    assert len(set(ds))==len(ds) and all(sf(d) for d in ds)
    assert len(ds)==len(a) and all(type(v) is int for v in a)
    cs=[Q(v,scale) for v in a]
    check_mean_identity(ds)
    mu=1-2*sum(c*Q(d-1,2*d) for d,c in zip(ds,cs))
    mu+=sum(c*e*mean_product(d,f) for d,c in zip(ds,cs) for f,e in zip(ds,cs))
    D=(2*sum(abs(c)*d for d,c in zip(ds,cs))+
       sum(abs(c*e)*math.lcm(d,f) for d,c in zip(ds,cs) for f,e in zip(ds,cs)))/4
    assert mu>=0 and D>=0
    L=math.lcm(*ds);den=scale*L
    slope=-sum(v*(L//d) for d,v in zip(ds,a))
    assert sum(abs(v) for v in a)<2**63
    jumps=np.zeros(N+1,dtype=np.int64)
    for d,v in zip(ds,a):jumps[d::d]+=v
    num=den;floors=0;den2=den*den
    # A_n is exactly den*(1-sum c_d*(n mod d)/d).
    for n in range(1,N+1):
        num+=slope+L*int(jumps[n])
        if n<=1000 or n==N:
            assert num==den-sum(v*(L//d)*(n%d) for d,v in zip(ds,a))
        floors+=(S*num*num)//(den2*n*n)
    hlow=Q(floors,S);hhigh=Q(floors+N,S)
    zlow,zhigh=zeta_interval()
    low=max(Q(0),(hlow+mu/Q(N+1)-D/Q((N+1)**2))/zhigh)
    high=(hhigh+mu/Q(N)+D/Q((N+1)**2))/zlow
    # Also retain the simpler unsigned, pointwise tail certificate.
    M=max(abs(1-sum(max(c,0)*Q(d-1,d) for d,c in zip(ds,cs))),abs(1-sum(min(c,0)*Q(d-1,d) for d,c in zip(ds,cs))))
    crude=(hhigh+M*M/N)/zlow
    endpoint=Q((high.numerator*10**6)//high.denominator+1,10**6)
    assert high<endpoint
    return dict(label=item['label'],dictionary=ds,coefficient_denominator=scale,
      coefficient_numerators=a,N=N,rounding_scale=S,
      head_lower=str(hlow),head_upper=str(hhigh),period_mean_square=str(mu),
      centered_partial_sum_bound=str(D),zeta_lower=str(zlow),zeta_upper=str(zhigh),
      full_error_lower=str(low),full_error_upper=str(high),
      full_error_lower_display=float(low),full_error_upper_display=float(high),
      simple_tail_upper_display=float(crude),simple_tail_upper=str(crude),
      strict_rational_bound=str(endpoint),strict_rational_bound_display=float(endpoint),
      exact_arithmetic_checks_passed=True,
      status='Exact integer/rational certificate with an analytic infinite-tail proof; NOT Lean-checked')

if __name__=='__main__':
    records=[]
    for item in json.loads(Path('exploration.json').read_text()):
        N=2000000 if item['label']=='squarefree_200' else (1000000 if item['label'] in ['squarefree_100','divisors_30030'] else 200000)
        rec=certify(item,N)
        records.append(rec)
        Path('certificates.json').write_text(json.dumps(records,indent=2))
        print(rec['label'],rec['full_error_lower_display'],rec['full_error_upper_display'],rec['strict_rational_bound'],flush=True)
```

## gram_optimality.py

```python
"""Rational enclosure and optimality-gap proof for seven complete-Q atoms."""
from fractions import Fraction as Q
import json, math
from pathlib import Path
from certify import S,zeta_interval,mean_product

def moment(d,e=None,N=20000):
    period=math.lcm(d,e) if e else d
    den=d*e if e else d
    mean=mean_product(d,e) if e else Q(d-1,2*d)
    total=sum((S*(n%d)*(n%e))//(den*n*n) if e else (S*(n%d))//(den*n*n) for n in range(1,N+1))
    zl,zu=zeta_interval()
    delta=Q(period,4*(N+1)**2)
    return ((Q(total,S)+mean/(N+1)-delta)/zu,
            (Q(total+N,S)+mean/N+delta)/zl)

item=next(x for x in json.loads(Path('exploration.json').read_text()) if x['label']=='divisors_30')
ds=item['dictionary'];cs=[Q(x,10**6) for x in item['coefficient_numerators_1e6']];n=len(ds)
B=[moment(d) for d in ds];G=[[moment(d,e) for e in ds] for d in ds]
mid=[[sum(v)/2 for v in row] for row in G]
rad=[[(v[1]-v[0])/2 for v in row] for row in G]
gamma=max(sum(row) for row in rad);alpha=Q(1,250)
A=[[mid[i][j]-(gamma+alpha if i==j else 0) for j in range(n)] for i in range(n)]
# Exact LDL^T: positive rational pivots prove G >= (1/250) I.
L=[[Q(0) for j in range(n)] for i in range(n)];piv=[]
for i in range(n):
    L[i][i]=1
    p=A[i][i]-sum(L[i][k]**2*piv[k] for k in range(i))
    assert p>0
    piv.append(p)
    for j in range(i+1,n):
        L[j][i]=(A[j][i]-sum(L[j][k]*L[i][k]*piv[k] for k in range(i)))/p
assert all(A[i][j]==sum(L[i][k]*piv[k]*L[j][k] for k in range(n)) for i in range(n) for j in range(n))
vbound=[]
for i in range(n):
    vmid=sum(mid[i][j]*cs[j] for j in range(n))-sum(B[i])/2
    vrad=sum(rad[i][j]*abs(cs[j]) for j in range(n))+(B[i][1]-B[i][0])/2
    vbound.append(abs(vmid)+vrad)
gap=sum(v*v for v in vbound)/alpha
assert gap<Q(1,10**11)
Path('gram_optimality.json').write_text(json.dumps(dict(
 status='Exact rational complete-moment enclosures and LDL proof; NOT Lean-checked',
 dictionary=ds,gram_interval=[[[str(a),str(b)] for a,b in row] for row in G],
 mean_interval=[[str(a),str(b)] for a,b in B],
 lower_eigenvalue_bound=str(alpha),positive_ldl_pivots=[str(p) for p in piv],
 normal_residual_component_upper=[str(v) for v in vbound],
 certified_suboptimality_upper=str(gap),certified_suboptimality_display=float(gap),
 strict_suboptimality_bound='1/100000000000'),indent=2))
print('Complete-Q eigenvalue lower bound',alpha,'rational certificate suboptimality <',float(gap))
```

## explore.py

```python
import sys, json, math, time
from pathlib import Path
sys.path.insert(0,'reference')
import prime_tensor_crt_diagnostics as b
import numpy as np
from scipy.special import polygamma
out=[]
for label,ds in [('original',[2,3,6])]+[(f'divisors_{l}',b.divisors(l)[1:]) for l in [30,210,2310,30030]]+[(f'squarefree_{h}',[d for d in range(2,h+1) if b.mu(d)]) for h in [30,60,100,200]]:
    info,g,m,c=b.fit(ds)
    info['label']=label
    info['coefficient_numerators_1e6']=np.rint(c*1e6).astype(int).tolist()
    out.append(info)
    np.savez(f'{label}.npz',g=g,b=m,c=c,ds=ds)
    print(label,len(ds),info['squared_error'],info['coefficient_l1'],info['condition'],flush=True)
    Path('exploration.json').write_text(json.dumps(out,indent=2))
```

## compare_methods.py

```python
"""Complete-Q signed block comparison; numerical diagnostics only."""
import sys, json
from pathlib import Path
import numpy as np
sys.path.insert(0,'reference')
import prime_tensor_crt_diagnostics as base

z=np.load('squarefree_30.npz');G=z['g'];b=z['b'];c=z['c'];ds=z['ds'].astype(int).tolist()
rows=base.divisors(60)
A=np.array([base.row(r,ds) for r in rows]);y=np.array([float(r==1) for r in rows]);K=G-A.T@A
assert np.linalg.eigvalsh(K).min()>-1e-12
partitions={
 'singleton_columns':[[i] for i in range(len(ds))],
 'pairs': [list(range(i,min(i+2,len(ds)))) for i in range(0,len(ds),2)],
 'four_consecutive_blocks': [a.tolist() for a in np.array_split(np.arange(len(ds)),4)],
 'one_signed_block': [list(range(len(ds)))]}
records=[]
for name,parts in partitions.items():
    mats=[K[np.ix_(p,p)] for p in parts]
    # Tiny roundoff negatives are clipped solely in this floating diagnostic.
    mats=[(lambda e,u:(u*np.maximum(e,0))@u.T)(*np.linalg.eigh(M)) for M in mats]
    def value_grad(x):
        retained=y-A@x
        lens=[np.sqrt(max(float(x[p]@M@x[p]),0)) for p,M in zip(parts,mats)]
        total=sum(lens);grad=-2*A.T@retained
        for p,M,l in zip(parts,mats,lens):
            if l>1e-18:grad[p]+=2*total*(M@x[p])/l
        return float(retained@retained+total**2),grad
    records.append(dict(method=name,certificate_at_Gram_solution=value_grad(c)[0],
      note='Same complete-Gram coefficient vector for every method; no separate optimization claimed'))
out=dict(status='Floating complete-Q diagnostics only; no certified optimization claim',
 dictionary=ds,retained_rows=rows,complete_Gram_error=float(1-2*b@c+c@G@c),
 projected_anchor_error=float(1-2*b@c+c@G@c),methods=records)
Path('method_comparison.json').write_text(json.dumps(out,indent=2))
print(json.dumps({**out,'methods':[{k:v for k,v in x.items() if k!='coefficients'} for x in records]},indent=2))
```

## reference/prime_tensor_crt_diagnostics.py

```python
"""Complete weighted moments and exact rational benchmark, 2026-11-02.

Floating calculations select candidates only. rational_certificate() uses
fractions and integral-test bounds for every omitted positive-integer term.
Source: the supplied Prime Tensor CRT project, sections 4, 6 and Appendix B.
"""
import json
import math
from fractions import Fraction as Q
from functools import lru_cache
import numpy as np
from scipy.special import polygamma


def factors(n):
    out, p = [], 2
    while p*p <= n:
        if n % p == 0:
            a = 0
            while n % p == 0:
                n //= p
                a += 1
            out.append((p,a))
        p += 1
    if n > 1:
        out.append((n,1))
    return out


def mu(n):
    fs = factors(n)
    return 0 if any(a > 1 for _,a in fs) else (-1)**len(fs)


def divisors(n):
    ds = [1]
    for p,a in factors(n):
        ds = [d*p**k for d in ds for k in range(a+1)]
    return sorted(ds)


@lru_cache(None)
def weights(l):
    w = np.empty(l)
    w[0] = 1/l**2
    w[1:] = polygamma(1,np.arange(1,l)/l)/(l*l*(math.pi**2/6))
    assert abs(sum(w)-1) < 1e-12
    return w


@lru_cache(None)
def gram_entry(d,e):
    l = math.lcm(d,e)
    n = np.arange(l)
    return float(weights(l) @ ((n%d)/d*((n%e)/e)))


@lru_cache(None)
def twisted(d,a):
    n = np.arange(d)
    return float(weights(d) @ ((a*n%d)/d))


def row(r,ds):
    j2 = math.prod(p**(2*a)-p**(2*a-2) for p,a in factors(r))
    return [sum(mu(r//a)*twisted(d,a%d) for a in divisors(r))/math.sqrt(j2) for d in ds]


def fit(ds):
    g = np.array([[gram_entry(d,e) for e in ds] for d in ds])
    b = np.array([twisted(d,1) for d in ds])
    c = np.linalg.solve(g,b)
    err = float(1-2*b@c+c@g@c)
    return dict(dictionary=ds, coefficients=c.tolist(), squared_error=err,
                capacity=(1-err)/err, coefficient_l1=float(np.abs(c).sum()),
                condition=float(np.linalg.cond(g)), normal_residual=float(np.linalg.norm(g@c-b))), g,b,c


def rational_certificate():
    ds = [2,3,6]
    c = [Q(1045918,10**6),Q(1069558,10**6),Q(604750,10**6)]
    kmax=tmax=100
    residues = [1-sum((v*Q(n%d,d) for v,d in zip(c,ds)),Q(0)) for n in range(1,7)]
    lo=hi=Q(0)
    for r,e in enumerate(residues,1):
        s = sum((Q(1,(6*k+r)**2) for k in range(kmax)),Q(0))
        tail = Q(1,6*(6*kmax+r))
        lo += e*e*(s+tail)
        hi += e*e*(s+tail+Q(1,(6*kmax+r)**2))
    z = sum((Q(1,n*n) for n in range(1,tmax+1)),Q(0))
    lower,upper = lo/(z+Q(1,tmax)),hi/(z+Q(1,tmax+1))
    assert Q(5476,100000) < lower < upper < Q(5478,100000)
    return dict(coefficients=[str(x) for x in c], K=kmax,T=tmax,
                rigorous_outer_interval=['0.05476','0.05478'],
                lower=str(lower),upper=str(upper))


def main():
    out={'status':'Floating diagnostics except the explicitly rational benchmark.'}
    out['stages']=[fit([d for d in range(2,b+1) if mu(d)])[0] for b in [2,3,6,10,15,20,30]]
    out['primorial']=[fit(divisors(l)[1:])[0] for l in [6,30,210]]
    all_ds=[d for d in range(2,31) if mu(d)]
    selected=[]
    adaptive=[]
    for _ in range(8):
        best=min((fit(sorted(selected+[d])) for d in all_ds if d not in selected),key=lambda x:x[0]['squared_error'])
        selected=best[0]['dictionary']
        adaptive.append(best[0])
    out['adaptive']=adaptive
    info,g,b,c=fit([2,3,6])
    a=np.array([row(r,[2,3,6]) for r in divisors(12)])
    k=g-a.T@a
    y=np.zeros(len(a));y[0]=1
    info['retained_error']=float(np.linalg.norm(y-a@c)**2)
    info['exact_tail']=float(c@k@c)
    diag=np.diag(k)
    info['raw_tail_diagonal']=diag.tolist()
    assert diag.min()>-1e-12
    # g_2 has exactly zero omitted energy here; roundoff may give -1e-16.
    # Clipping is only a floating diagnostic, never an interval certificate.
    info['column_tail_bound']=float((np.abs(c)@np.sqrt(np.maximum(diag,0)))**2)
    info['tail_eigenvalues']=np.linalg.eigvalsh(k).tolist()
    out['benchmark_float']=info
    out['benchmark_rational']=rational_certificate()
    with open('prime_tensor_crt_diagnostics.json','w') as f:
        json.dump(out,f,indent=2)
    print(json.dumps({'stage_errors':[(x['dictionary'][-1],x['squared_error']) for x in out['stages']],
                      'primorial_errors':[x['squared_error'] for x in out['primorial']],
                      'adaptive_dictionary':selected,'adaptive_error':adaptive[-1]['squared_error'],
                      'rational_outer_interval':out['benchmark_rational']['rigorous_outer_interval']},indent=2))


if __name__=='__main__':
    main()
```

## exploration.json

```json
[
  {
    "dictionary": [
      2,
      3,
      6
    ],
    "coefficients": [
      1.0459181205625996,
      1.0695580135833513,
      0.6047499290144435
    ],
    "squared_error": 0.05476694337026178,
    "capacity": 17.259189548690347,
    "coefficient_l1": 2.7202260631603945,
    "condition": 13.327586346026692,
    "normal_residual": 0.0,
    "label": "original",
    "coefficient_numerators_1e6": [
      1045918,
      1069558,
      604750
    ]
  },
  {
    "dictionary": [
      2,
      3,
      5,
      6,
      10,
      15,
      30
    ],
    "coefficients": [
      0.9855868955790479,
      0.963419223438624,
      0.8237209582958145,
      -0.15823158694020995,
      0.091951844701465,
      0.13861137882444968,
      0.14643875873284265
    ],
    "squared_error": 0.02540022543571796,
    "capacity": 38.36972931719706,
    "coefficient_l1": 3.307960646512454,
    "condition": 123.2566022386384,
    "normal_residual": 9.205483015737869e-17,
    "label": "divisors_30",
    "coefficient_numerators_1e6": [
      985587,
      963419,
      823721,
      -158232,
      91952,
      138611,
      146439
    ]
  },
  {
    "dictionary": [
      2,
      3,
      5,
      6,
      7,
      10,
      14,
      15,
      21,
      30,
      35,
      42,
      70,
      105,
      210
    ],
    "coefficients": [
      0.9778348343202422,
      0.9578673620094047,
      0.7900754609230942,
      -0.4631998011032164,
      0.6715141099660072,
      -0.0851572922048438,
      0.03657133801597476,
      -0.13165232486293502,
      0.014011108900186297,
      0.19990832615007414,
      -0.02173262410915433,
      0.06993662786561362,
      0.009942563505144119,
      0.015590793147770085,
      -0.04562652366982372
    ],
    "squared_error": 0.016870436061022787,
    "capacity": 58.275290596097015,
    "coefficient_l1": 4.490621090753485,
    "condition": 1172.42629263737,
    "normal_residual": 8.886119947416683e-17,
    "label": "divisors_210",
    "coefficient_numerators_1e6": [
      977835,
      957867,
      790075,
      -463200,
      671514,
      -85157,
      36571,
      -131652,
      14011,
      199908,
      -21733,
      69937,
      9943,
      15591,
      -45627
    ]
  },
  {
    "dictionary": [
      2,
      3,
      5,
      6,
      7,
      10,
      11,
      14,
      15,
      21,
      22,
      30,
      33,
      35,
      42,
      55,
      66,
      70,
      77,
      105,
      110,
      154,
      165,
      210,
      231,
      330,
      385,
      462,
      770,
      1155,
      2310
    ],
    "coefficients": [
      0.9836036840112464,
      0.9570160796426512,
      0.8270015747395939,
      -0.5628738701584838,
      0.6980679447898208,
      -0.4486582733831734,
      0.6791671761533972,
      -0.10680828484386949,
      -0.18222439189092632,
      -0.07619070581428249,
      -0.08291395631265988,
      0.44604022084252576,
      -0.19963921942358634,
      -0.10074401862964372,
      0.2003604172685123,
      -0.14901126875771153,
      0.06450188211826266,
      0.1708958400638439,
      -0.13428044768630404,
      0.06647379855326659,
      0.05379236888915962,
      -0.06449482993623146,
      0.10573293719098825,
      -0.2420480648321761,
      0.1328797078447363,
      -0.09576719589153039,
      0.07435895925490651,
      -0.023531771076611786,
      -0.003977997128643423,
      -0.03272228092500199,
      0.03483634459594093
    ],
    "squared_error": 0.013549481065413205,
    "capacity": 72.80356451824777,
    "coefficient_l1": 8.000615512649688,
    "condition": 15172.971297951573,
    "normal_residual": 1.195961001944021e-16,
    "label": "divisors_2310",
    "coefficient_numerators_1e6": [
      983604,
      957016,
      827002,
      -562874,
      698068,
      -448658,
      679167,
      -106808,
      -182224,
      -76191,
      -82914,
      446040,
      -199639,
      -100744,
      200360,
      -149011,
      64502,
      170896,
      -134280,
      66474,
      53792,
      -64495,
      105733,
      -242048,
      132880,
      -95767,
      74359,
      -23532,
      -3978,
      -32722,
      34836
    ]
  },
  {
    "dictionary": [
      2,
      3,
      5,
      6,
      7,
      10,
      11,
      13,
      14,
      15,
      21,
      22,
      26,
      30,
      33,
      35,
      39,
      42,
      55,
      65,
      66,
      70,
      77,
      78,
      91,
      105,
      110,
      130,
      143,
      154,
      165,
      182,
      195,
      210,
      231,
      273,
      286,
      330,
      385,
      390,
      429,
      455,
      462,
      546,
      715,
      770,
      858,
      910,
      1001,
      1155,
      1365,
      1430,
      2002,
      2145,
      2310,
      2730,
      3003,
      4290,
      5005,
      6006,
      10010,
      15015,
      30030
    ],
    "coefficients": [
      0.9875897218616095,
      0.9581418515323669,
      0.8506554109804333,
      -0.6313202710320133,
      0.7405333701798092,
      -0.5044985884523003,
      0.5594463619281782,
      0.6311080983631094,
      -0.4685630568898555,
      -0.2597749251228552,
      -0.09029934969400123,
      -0.017516348849781073,
      -0.19404132795964682,
      0.619938483725712,
      -0.08374196251086075,
      -0.27229601621910643,
      -0.14681701672031053,
      0.3909255533582057,
      -0.0710041716573757,
      -0.40469450649887434,
      0.01931581737580693,
      0.5973332455066488,
      -0.19172438544000422,
      0.16329511275857767,
      -0.4160915994867612,
      0.24221680141779384,
      0.07578511422149256,
      0.16286593661194781,
      -0.37586703616136713,
      0.06603613392241926,
      -0.04258655688874506,
      0.25020300777164034,
      0.3949852475769246,
      -0.7266157362976868,
      0.08274883911973215,
      0.18773481630841882,
      0.03720595039050681,
      -0.10830477715595514,
      0.017547588805493095,
      -0.29883524422802576,
      0.3086124163593266,
      0.3713341485730919,
      -0.21625043357437054,
      -0.2619043252921399,
      0.17981542552265853,
      -0.08534449310136917,
      0.0688975650756514,
      -0.351257643849476,
      0.2749672073465927,
      0.10831158522381315,
      -0.3218364494330857,
      0.13455191916382717,
      0.039644299433709354,
      -0.24024855199679776,
      0.1147392295448864,
      0.3996053752552819,
      -0.2853770580105874,
      0.08862941971142618,
      -0.14834092660110051,
      0.0654953096318984,
      0.00363867426519391,
      0.07670755853647872,
      -0.07632689276613291
    ],
    "squared_error": 0.011752997896377071,
    "capacity": 84.08467446490872,
    "coefficient_l1": 17.562042249251252,
    "condition": 223037.32181151872,
    "normal_residual": 1.745063224339508e-16,
    "label": "divisors_30030",
    "coefficient_numerators_1e6": [
      987590,
      958142,
      850655,
      -631320,
      740533,
      -504499,
      559446,
      631108,
      -468563,
      -259775,
      -90299,
      -17516,
      -194041,
      619938,
      -83742,
      -272296,
      -146817,
      390926,
      -71004,
      -404695,
      19316,
      597333,
      -191724,
      163295,
      -416092,
      242217,
      75785,
      162866,
      -375867,
      66036,
      -42587,
      250203,
      394985,
      -726616,
      82749,
      187735,
      37206,
      -108305,
      17548,
      -298835,
      308612,
      371334,
      -216250,
      -261904,
      179815,
      -85344,
      68898,
      -351258,
      274967,
      108312,
      -321836,
      134552,
      39644,
      -240249,
      114739,
      399605,
      -285377,
      88629,
      -148341,
      65495,
      3639,
      76708,
      -76327
    ]
  },
  {
    "dictionary": [
      2,
      3,
      5,
      6,
      7,
      10,
      11,
      13,
      14,
      15,
      17,
      19,
      21,
      22,
      23,
      26,
      29,
      30
    ],
    "coefficients": [
      0.9886591389631102,
      0.9654595849351775,
      0.8595669494889128,
      -0.666108298177249,
      0.7455980895866459,
      -0.5332486683476282,
      0.5487792223380172,
      0.543435089468184,
      -0.43980756827777606,
      -0.4513011323033924,
      0.3481578586792714,
      0.34384443913244395,
      -0.3064990212420581,
      -0.34809508143253337,
      0.36565353615242213,
      -0.39715255050202003,
      0.22123217742314602,
      0.24523872322096946
    ],
    "squared_error": 0.009866930389172412,
    "capacity": 100.34864244074949,
    "coefficient_l1": 9.317837129670957,
    "condition": 962.5005275250868,
    "normal_residual": 1.4488835837920476e-16,
    "label": "squarefree_30",
    "coefficient_numerators_1e6": [
      988659,
      965460,
      859567,
      -666108,
      745598,
      -533249,
      548779,
      543435,
      -439808,
      -451301,
      348158,
      343844,
      -306499,
      -348095,
      365654,
      -397153,
      221232,
      245239
    ]
  },
  {
    "dictionary": [
      2,
      3,
      5,
      6,
      7,
      10,
      11,
      13,
      14,
      15,
      17,
      19,
      21,
      22,
      23,
      26,
      29,
      30,
      31,
      33,
      34,
      35,
      37,
      38,
      39,
      41,
      42,
      43,
      46,
      47,
      51,
      53,
      55,
      57,
      58,
      59
    ],
    "coefficients": [
      0.9896332907887695,
      0.9735571959822692,
      0.884676558273291,
      -0.7424342562229831,
      0.8045301929318562,
      -0.6252557371995451,
      0.6522773110269325,
      0.614645224189226,
      -0.56205539634799,
      -0.5632351092790416,
      0.5261481984591857,
      0.5284028457117513,
      -0.571979994228955,
      -0.40742043778299497,
      0.5167758986520288,
      -0.42227011226052347,
      0.3324149389892963,
      0.43503158443316126,
      0.29114266183504994,
      -0.31235010525075185,
      -0.30602053490574865,
      -0.30998939285705635,
      0.3948799215980966,
      -0.3654540047979908,
      -0.34695311356323494,
      0.29146640267072177,
      0.43880498347747426,
      0.21167448739735922,
      -0.4071244603719461,
      0.23771404733829854,
      -0.17935194436749755,
      0.38782210761242103,
      -0.25564480953704777,
      -0.24321113255881432,
      -0.22729178095238148,
      0.30788363013203257
    ],
    "squared_error": 0.007613322602681771,
    "capacity": 130.348696513629,
    "coefficient_l1": 16.667523803983723,
    "condition": 4826.584214587303,
    "normal_residual": 1.5170650228460041e-16,
    "label": "squarefree_60",
    "coefficient_numerators_1e6": [
      989633,
      973557,
      884677,
      -742434,
      804530,
      -625256,
      652277,
      614645,
      -562055,
      -563235,
      526148,
      528403,
      -571980,
      -407420,
      516776,
      -422270,
      332415,
      435032,
      291143,
      -312350,
      -306021,
      -309989,
      394880,
      -365454,
      -346953,
      291466,
      438805,
      211674,
      -407124,
      237714,
      -179352,
      387822,
      -255645,
      -243211,
      -227292,
      307884
    ]
  },
  {
    "dictionary": [
      2,
      3,
      5,
      6,
      7,
      10,
      11,
      13,
      14,
      15,
      17,
      19,
      21,
      22,
      23,
      26,
      29,
      30,
      31,
      33,
      34,
      35,
      37,
      38,
      39,
      41,
      42,
      43,
      46,
      47,
      51,
      53,
      55,
      57,
      58,
      59,
      61,
      62,
      65,
      66,
      67,
      69,
      70,
      71,
      73,
      74,
      77,
      78,
      79,
      82,
      83,
      85,
      86,
      87,
      89,
      91,
      93,
      94,
      95,
      97
    ],
    "coefficients": [
      0.9912105989644467,
      0.9759834253067415,
      0.8981005335886236,
      -0.7700548618091351,
      0.8235617855932618,
      -0.6661103632291665,
      0.6866399466242399,
      0.6815528833675469,
      -0.643068169218188,
      -0.5942156284383927,
      0.5856162383277299,
      0.5460099809501507,
      -0.5280522645971123,
      -0.5110730659438587,
      0.5298117212690809,
      -0.4960518677903241,
      0.44033442516985377,
      0.4465273542319226,
      0.46374671850210925,
      -0.5157788745976141,
      -0.30277042272250176,
      -0.446485317870581,
      0.5116073752638624,
      -0.34223947624810275,
      -0.5685205983698998,
      0.335343824002587,
      0.4378156737741738,
      0.38537074797255905,
      -0.3358842109548837,
      0.2225859970584018,
      -0.23554705959074612,
      0.35204766539265603,
      -0.247311491311643,
      -0.20825275546317631,
      -0.30103989017165483,
      0.19672413619936452,
      0.25079369958023623,
      -0.3572343303708289,
      -0.3062346974443808,
      0.46023897824691146,
      0.1655199376646577,
      -0.2666534825438601,
      0.3990127066898089,
      0.12346186695236956,
      0.1544624785215142,
      -0.3310464500006995,
      -0.2226264213914975,
      0.46566134408301973,
      0.1726199602601671,
      -0.24461913212119885,
      0.30133346779475256,
      -0.2980212012264777,
      -0.2457155999007603,
      -0.1537144490752534,
      0.24469028406299764,
      -0.19477177761904083,
      -0.2949145225287248,
      -0.14869135572119882,
      -0.16134568994565365,
      0.6684428834727382
    ],
    "squared_error": 0.0068102038375825735,
    "capacity": 145.83848293665338,
    "coefficient_l1": 24.854874067105044,
    "condition": 12697.58917290115,
    "normal_residual": 1.6435074526764696e-16,
    "label": "squarefree_100",
    "coefficient_numerators_1e6": [
      991211,
      975983,
      898101,
      -770055,
      823562,
      -666110,
      686640,
      681553,
      -643068,
      -594216,
      585616,
      546010,
      -528052,
      -511073,
      529812,
      -496052,
      440334,
      446527,
      463747,
      -515779,
      -302770,
      -446485,
      511607,
      -342239,
      -568521,
      335344,
      437816,
      385371,
      -335884,
      222586,
      -235547,
      352048,
      -247311,
      -208253,
      -301040,
      196724,
      250794,
      -357234,
      -306235,
      460239,
      165520,
      -266653,
      399013,
      123462,
      154462,
      -331046,
      -222626,
      465661,
      172620,
      -244619,
      301333,
      -298021,
      -245716,
      -153714,
      244690,
      -194772,
      -294915,
      -148691,
      -161346,
      668443
    ]
  },
  {
    "dictionary": [
      2,
      3,
      5,
      6,
      7,
      10,
      11,
      13,
      14,
      15,
      17,
      19,
      21,
      22,
      23,
      26,
      29,
      30,
      31,
      33,
      34,
      35,
      37,
      38,
      39,
      41,
      42,
      43,
      46,
      47,
      51,
      53,
      55,
      57,
      58,
      59,
      61,
      62,
      65,
      66,
      67,
      69,
      70,
      71,
      73,
      74,
      77,
      78,
      79,
      82,
      83,
      85,
      86,
      87,
      89,
      91,
      93,
      94,
      95,
      97,
      101,
      102,
      103,
      105,
      106,
      107,
      109,
      110,
      111,
      113,
      114,
      115,
      118,
      119,
      122,
      123,
      127,
      129,
      130,
      131,
      133,
      134,
      137,
      138,
      139,
      141,
      142,
      143,
      145,
      146,
      149,
      151,
      154,
      155,
      157,
      158,
      159,
      161,
      163,
      165,
      166,
      167,
      170,
      173,
      174,
      177,
      178,
      179,
      181,
      182,
      183,
      185,
      186,
      187,
      190,
      191,
      193,
      194,
      195,
      197,
      199
    ],
    "coefficients": [
      0.992128638204226,
      0.9792412061575908,
      0.911721509148766,
      -0.7994951384353132,
      0.8452774270495695,
      -0.7081876637895873,
      0.7296015231889393,
      0.7014645604331419,
      -0.6645063578934818,
      -0.6592419156010623,
      0.6590611440424408,
      0.5970126033490596,
      -0.5960080317425843,
      -0.5640545203260288,
      0.5900720764259796,
      -0.5648805057825544,
      0.5603621855497712,
      0.4811343378678457,
      0.5083571967138067,
      -0.5258535538956404,
      -0.4474967198073731,
      -0.5125238404982966,
      0.5692678560482393,
      -0.5228930825425516,
      -0.4716681380021951,
      0.46958353001837877,
      0.44759135260991223,
      0.3893387333863615,
      -0.4094134635882329,
      0.4089000511040811,
      -0.4454387624235873,
      0.509012510047831,
      -0.4175882277746735,
      -0.36903523534542726,
      -0.4328398231378571,
      0.36665448628928554,
      0.42221134799863763,
      -0.38391451865291837,
      -0.41516471574054536,
      0.5475298763181522,
      0.3464740020110736,
      -0.5920243004941856,
      0.386964803371002,
      0.33755339288622005,
      0.3099435921586605,
      -0.36593110803318346,
      -0.3359705258144218,
      0.3970562215567772,
      0.45169757831308505,
      -0.35427739211060466,
      0.33066781514033156,
      -0.37801299914504516,
      -0.24856353055528602,
      -0.42892944279946044,
      0.445246423407787,
      -0.3481230177306071,
      -0.34310872672280357,
      -0.2604582412328947,
      -0.3060453712670528,
      0.5409812080205574,
      0.2068822068167278,
      0.2513821589083988,
      0.21508576430364335,
      0.2809281589926731,
      -0.3606406209288164,
      0.18271514761701485,
      0.12243037719696095,
      0.22649841796868359,
      -0.3339200172591137,
      0.25763673088537814,
      0.43523184017974065,
      -0.1172376287596841,
      -0.3210994339765479,
      -0.18852613239063998,
      -0.25502401711128153,
      -0.26495609634301076,
      0.26249789393359285,
      -0.19647606521488442,
      0.26043444616303524,
      0.18722482262152526,
      -0.2553593279461158,
      -0.3182971858021359,
      0.2577061113261868,
      0.428683215406855,
      0.2678275105119929,
      -0.14110327722505225,
      -0.20274971148335738,
      -0.21712387665268812,
      -0.3271992094560089,
      -0.23101001157710094,
      0.19067089902788992,
      0.11777673561476984,
      0.3192276059208057,
      -0.14667499150326985,
      0.22085755015315264,
      -0.3532561749941653,
      -0.27009068881814896,
      -0.2838539264236865,
      0.18122382444695323,
      0.20761633577476651,
      -0.1772998216134702,
      0.1487250643010255,
      0.12326860646275045,
      0.23721253608038123,
      0.39961328823188025,
      -0.14330949663605136,
      -0.4272092282107475,
      0.2695908545864889,
      0.20992847377492077,
      0.2810595076757407,
      -0.27974915600463973,
      -0.2986073935040538,
      0.2892918588821253,
      -0.23348716835573202,
      0.2813549715211471,
      0.21950464303014422,
      0.2658108162826065,
      -0.46047768782487053,
      0.13254795344147774,
      -0.026187222627251473,
      -0.4748427027743836
    ],
    "squared_error": 0.005872228653412193,
    "capacity": 169.29309637303157,
    "coefficient_l1": 45.347972659161314,
    "condition": 55743.45021565097,
    "normal_residual": 2.614545389997933e-16,
    "label": "squarefree_200",
    "coefficient_numerators_1e6": [
      992129,
      979241,
      911722,
      -799495,
      845277,
      -708188,
      729602,
      701465,
      -664506,
      -659242,
      659061,
      597013,
      -596008,
      -564055,
      590072,
      -564881,
      560362,
      481134,
      508357,
      -525854,
      -447497,
      -512524,
      569268,
      -522893,
      -471668,
      469584,
      447591,
      389339,
      -409413,
      408900,
      -445439,
      509013,
      -417588,
      -369035,
      -432840,
      366654,
      422211,
      -383915,
      -415165,
      547530,
      346474,
      -592024,
      386965,
      337553,
      309944,
      -365931,
      -335971,
      397056,
      451698,
      -354277,
      330668,
      -378013,
      -248564,
      -428929,
      445246,
      -348123,
      -343109,
      -260458,
      -306045,
      540981,
      206882,
      251382,
      215086,
      280928,
      -360641,
      182715,
      122430,
      226498,
      -333920,
      257637,
      435232,
      -117238,
      -321099,
      -188526,
      -255024,
      -264956,
      262498,
      -196476,
      260434,
      187225,
      -255359,
      -318297,
      257706,
      428683,
      267828,
      -141103,
      -202750,
      -217124,
      -327199,
      -231010,
      190671,
      117777,
      319228,
      -146675,
      220858,
      -353256,
      -270091,
      -283854,
      181224,
      207616,
      -177300,
      148725,
      123269,
      237213,
      399613,
      -143309,
      -427209,
      269591,
      209928,
      281060,
      -279749,
      -298607,
      289292,
      -233487,
      281355,
      219505,
      265811,
      -460478,
      132548,
      -26187,
      -474843
    ]
  }
]
```

## certificates.json

```json
[
  {
    "label": "original",
    "dictionary": [
      2,
      3,
      6
    ],
    "coefficient_denominator": 1000000,
    "coefficient_numerators": [
      1045918,
      1069558,
      604750
    ],
    "N": 200000,
    "rounding_scale": 100000000000000000000,
    "head_lower": "9008664133017053549/100000000000000000000",
    "head_upper": "9008664133017253549/100000000000000000000",
    "period_mean_square": "51358518371/187500000000",
    "centered_partial_sum_bound": "13612039037367/1000000000000",
    "zeta_lower": "20563731940690556584651/12501250000000000000000",
    "zeta_upper": "257020948726259347/156250000000000000",
    "full_error_lower": "360355645703490892308936653549/6579802084919606612777637982080",
    "full_error_upper": "400435204464603751578793483111061/7311622250141886858216572595419120",
    "full_error_lower_display": 0.054766942995048126,
    "full_error_upper_display": 0.05476694374587432,
    "simple_tail_upper_display": 0.05476915058157475,
    "simple_tail_upper": "90100650494305552743549/1645098555255244526772080",
    "strict_rational_bound": "54767/1000000",
    "strict_rational_bound_display": 0.054767,
    "exact_arithmetic_checks_passed": true,
    "status": "Exact integer/rational certificate with an analytic infinite-tail proof; NOT Lean-checked"
  },
  {
    "label": "divisors_30",
    "dictionary": [
      2,
      3,
      5,
      6,
      10,
      15,
      30
    ],
    "coefficient_denominator": 1000000,
    "coefficient_numerators": [
      985587,
      963419,
      823721,
      -158232,
      91952,
      138611,
      146439
    ],
    "N": 200000,
    "rounding_scale": 100000000000000000000,
    "head_lower": "41780703267511033/1000000000000000000",
    "head_upper": "41780703267513033/1000000000000000000",
    "period_mean_square": "14892941105207/75000000000000",
    "centered_partial_sum_bound": "32378347356481/800000000000",
    "zeta_lower": "20563731940690556584651/12501250000000000000000",
    "zeta_upper": "257020948726259347/156250000000000000",
    "full_error_lower": "2785474195431302109137035055/109663368081993443546293966368",
    "full_error_upper": "41786293171578588218418293395117/1645115006281924543098728833969302",
    "full_error_lower_display": 0.025400224743677854,
    "full_error_upper_display": 0.025400226131313788,
    "simple_tail_upper_display": 0.02540362602243456,
    "simple_tail_upper": "2089573423387581378749/82254927762762226338604",
    "strict_rational_bound": "25401/1000000",
    "strict_rational_bound_display": 0.025401,
    "exact_arithmetic_checks_passed": true,
    "status": "Exact integer/rational certificate with an analytic infinite-tail proof; NOT Lean-checked"
  },
  {
    "label": "divisors_210",
    "dictionary": [
      2,
      3,
      5,
      6,
      7,
      10,
      14,
      15,
      21,
      30,
      35,
      42,
      70,
      105,
      210
    ],
    "coefficient_denominator": 1000000,
    "coefficient_numerators": [
      977835,
      957867,
      790075,
      -463200,
      671514,
      -85157,
      36571,
      -131652,
      14011,
      199908,
      -21733,
      69937,
      9943,
      15591,
      -45627
    ],
    "N": 200000,
    "rounding_scale": 100000000000000000000,
    "head_lower": "693746649897437133/25000000000000000000",
    "head_upper": "693746649897487133/25000000000000000000",
    "period_mean_square": "1306840977564539/7350000000000000",
    "centered_partial_sum_bound": "652068205232093/4000000000000",
    "zeta_lower": "20563731940690556584651/12501250000000000000000",
    "zeta_upper": "257020948726259347/156250000000000000",
    "full_error_lower": "1359800393155146151525056469517/80602575540265181006526065280480",
    "full_error_upper": "27198735456882085171356764984436599/1612212706156286052236754257289915960",
    "full_error_lower_display": 0.016870433531939125,
    "full_error_upper_display": 0.016870438592266914,
    "simple_tail_upper_display": 0.016878364794998352,
    "simple_tail_upper": "170070262928351952979381/10076228650938372726478990",
    "strict_rational_bound": "16871/1000000",
    "strict_rational_bound_display": 0.016871,
    "exact_arithmetic_checks_passed": true,
    "status": "Exact integer/rational certificate with an analytic infinite-tail proof; NOT Lean-checked"
  },
  {
    "label": "divisors_2310",
    "dictionary": [
      2,
      3,
      5,
      6,
      7,
      10,
      11,
      14,
      15,
      21,
      22,
      30,
      33,
      35,
      42,
      55,
      66,
      70,
      77,
      105,
      110,
      154,
      165,
      210,
      231,
      330,
      385,
      462,
      770,
      1155,
      2310
    ],
    "coefficient_denominator": 1000000,
    "coefficient_numerators": [
      983604,
      957016,
      827002,
      -562874,
      698068,
      -448658,
      679167,
      -106808,
      -182224,
      -76191,
      -82914,
      446040,
      -199639,
      -100744,
      200360,
      -149011,
      64502,
      170896,
      -134280,
      66474,
      53792,
      -64495,
      105733,
      -242048,
      132880,
      -95767,
      74359,
      -23532,
      -3978,
      -32722,
      34836
    ],
    "N": 200000,
    "rounding_scale": 100000000000000000000,
    "head_lower": "557176445054104167/25000000000000000000",
    "head_upper": "557176445054154167/25000000000000000000",
    "period_mean_square": "21015917701964347/111168750000000000",
    "centered_partial_sum_bound": "4182735624731201/1000000000000",
    "zeta_lower": "20563731940690556584651/12501250000000000000000",
    "zeta_upper": "257020948726259347/156250000000000000",
    "full_error_lower": "132146271398745705348105811806143/9752911640372086901789653898938080",
    "full_error_upper": "1321607261498947542278336966551915123/97538868722455306160323632566039915580",
    "full_error_lower_display": 0.013549417473621667,
    "full_error_upper_display": 0.013549544697504662,
    "simple_tail_upper_display": 0.013582642100332725,
    "simple_tail_upper": "74521254176570424030825133/5486506500435943949567810055",
    "strict_rational_bound": "271/20000",
    "strict_rational_bound_display": 0.01355,
    "exact_arithmetic_checks_passed": true,
    "status": "Exact integer/rational certificate with an analytic infinite-tail proof; NOT Lean-checked"
  },
  {
    "label": "divisors_30030",
    "dictionary": [
      2,
      3,
      5,
      6,
      7,
      10,
      11,
      13,
      14,
      15,
      21,
      22,
      26,
      30,
      33,
      35,
      39,
      42,
      55,
      65,
      66,
      70,
      77,
      78,
      91,
      105,
      110,
      130,
      143,
      154,
      165,
      182,
      195,
      210,
      231,
      273,
      286,
      330,
      385,
      390,
      429,
      455,
      462,
      546,
      715,
      770,
      858,
      910,
      1001,
      1155,
      1365,
      1430,
      2002,
      2145,
      2310,
      2730,
      3003,
      4290,
      5005,
      6006,
      10010,
      15015,
      30030
    ],
    "coefficient_denominator": 1000000,
    "coefficient_numerators": [
      987590,
      958142,
      850655,
      -631320,
      740533,
      -504499,
      559446,
      631108,
      -468563,
      -259775,
      -90299,
      -17516,
      -194041,
      619938,
      -83742,
      -272296,
      -146817,
      390926,
      -71004,
      -404695,
      19316,
      597333,
      -191724,
      163295,
      -416092,
      242217,
      75785,
      162866,
      -375867,
      66036,
      -42587,
      250203,
      394985,
      -726616,
      82749,
      187735,
      37206,
      -108305,
      17548,
      -298835,
      308612,
      371334,
      -216250,
      -261904,
      179815,
      -85344,
      68898,
      -351258,
      274967,
      108312,
      -321836,
      134552,
      39644,
      -240249,
      114739,
      399605,
      -285377,
      88629,
      -148341,
      65495,
      3639,
      76708,
      -76327
    ],
    "N": 1000000,
    "rounding_scale": 100000000000000000000,
    "head_lower": "386652667269781383/20000000000000000000",
    "head_upper": "386652667269981383/20000000000000000000",
    "period_mean_square": "23463888877071738817/85885800000000000000",
    "centered_partial_sum_bound": "1291743713531867491/4000000000000",
    "zeta_lower": "20563731940690556584651/12501250000000000000000",
    "zeta_upper": "257020948726259347/156250000000000000",
    "full_error_lower": "166039773163075800058423946250220307/14127676126102678849216488262543726464",
    "full_error_upper": "16606192481964842199354237407690567811887/1412908880782931648646992042273943695084640",
    "full_error_lower_display": 0.011752801499766562,
    "full_error_upper_display": 0.01175319421360201,
    "simple_tail_upper_display": 0.01179207486143714,
    "simple_tail_upper": "174941486709959425128768943979/14835513577178792439631358388720",
    "strict_rational_bound": "5877/500000",
    "strict_rational_bound_display": 0.011754,
    "exact_arithmetic_checks_passed": true,
    "status": "Exact integer/rational certificate with an analytic infinite-tail proof; NOT Lean-checked"
  },
  {
    "label": "squarefree_30",
    "dictionary": [
      2,
      3,
      5,
      6,
      7,
      10,
      11,
      13,
      14,
      15,
      17,
      19,
      21,
      22,
      23,
      26,
      29,
      30
    ],
    "coefficient_denominator": 1000000,
    "coefficient_numerators": [
      988659,
      965460,
      859567,
      -666108,
      745598,
      -533249,
      548779,
      543435,
      -439808,
      -451301,
      348158,
      343844,
      -306499,
      -348095,
      365654,
      -397153,
      221232,
      245239
    ],
    "N": 200000,
    "rounding_scale": 100000000000000000000,
    "head_lower": "1622940010050459297/100000000000000000000",
    "head_upper": "1622940010050659297/100000000000000000000",
    "period_mean_square": "823772821102417310854166971/3923535486288600000000000000",
    "centered_partial_sum_bound": "9598245582466047/4000000000000",
    "zeta_lower": "20563731940690556584651/12501250000000000000000",
    "zeta_upper": "257020948726259347/156250000000000000",
    "full_error_lower": "424540983326415096687700620500770522791857/43026811621562988140168536863999897354180480",
    "full_error_upper": "2830577174204652200912471346547734370768417333/286874093607689958046007217987033412139302780320",
    "full_error_lower_display": 0.009866893858192722,
    "full_error_upper_display": 0.009866966858553504,
    "simple_tail_upper_display": 0.009912978487353433,
    "simple_tail_upper": "2176337970121027112497958620203073/219544304761430582702183553893105520",
    "strict_rational_bound": "9867/1000000",
    "strict_rational_bound_display": 0.009867,
    "exact_arithmetic_checks_passed": true,
    "status": "Exact integer/rational certificate with an analytic infinite-tail proof; NOT Lean-checked"
  },
  {
    "label": "squarefree_60",
    "dictionary": [
      2,
      3,
      5,
      6,
      7,
      10,
      11,
      13,
      14,
      15,
      17,
      19,
      21,
      22,
      23,
      26,
      29,
      30,
      31,
      33,
      34,
      35,
      37,
      38,
      39,
      41,
      42,
      43,
      46,
      47,
      51,
      53,
      55,
      57,
      58,
      59
    ],
    "coefficient_denominator": 1000000,
    "coefficient_numerators": [
      989633,
      973557,
      884677,
      -742434,
      804530,
      -625256,
      652277,
      614645,
      -562055,
      -563235,
      526148,
      528403,
      -571980,
      -407420,
      516776,
      -422270,
      332415,
      435032,
      291143,
      -312350,
      -306021,
      -309989,
      394880,
      -365454,
      -346953,
      291466,
      438805,
      211674,
      -407124,
      237714,
      -179352,
      387822,
      -255645,
      -243211,
      -227292,
      307884
    ],
    "N": 200000,
    "rounding_scale": 100000000000000000000,
    "head_lower": "1252186552192944741/100000000000000000000",
    "head_upper": "1252186552193144741/100000000000000000000",
    "period_mean_square": "5741307774855938072783409891115639793515078588345181/18546859686246573891818203781181943597650000000000000",
    "centered_partial_sum_bound": "30562718300907913/1000000000000",
    "zeta_lower": "20563731940690556584651/12501250000000000000000",
    "zeta_upper": "257020948726259347/156250000000000000",
    "full_error_lower": "6193550423603112282937026806965967210909568687870439020927878316391/813564440215177385633178300947692753444489094804123734389392809534080",
    "full_error_upper": "20649752159946683218751151198506261073491911028890048749898644675647887/2712152639044400486087044108868472261956967898531440118891113452047941360",
    "full_error_lower_display": 0.007612857835778807,
    "full_error_upper_display": 0.007613786872711712,
    "simple_tail_upper_display": 0.007781136195554291,
    "simple_tail_upper": "44280951517212964015530825377143944709/5690807923721042134223299900463188183920",
    "strict_rational_bound": "3807/500000",
    "strict_rational_bound_display": 0.007614,
    "exact_arithmetic_checks_passed": true,
    "status": "Exact integer/rational certificate with an analytic infinite-tail proof; NOT Lean-checked"
  },
  {
    "label": "squarefree_100",
    "dictionary": [
      2,
      3,
      5,
      6,
      7,
      10,
      11,
      13,
      14,
      15,
      17,
      19,
      21,
      22,
      23,
      26,
      29,
      30,
      31,
      33,
      34,
      35,
      37,
      38,
      39,
      41,
      42,
      43,
      46,
      47,
      51,
      53,
      55,
      57,
      58,
      59,
      61,
      62,
      65,
      66,
      67,
      69,
      70,
      71,
      73,
      74,
      77,
      78,
      79,
      82,
      83,
      85,
      86,
      87,
      89,
      91,
      93,
      94,
      95,
      97
    ],
    "coefficient_denominator": 1000000,
    "coefficient_numerators": [
      991211,
      975983,
      898101,
      -770055,
      823562,
      -666110,
      686640,
      681553,
      -643068,
      -594216,
      585616,
      546010,
      -528052,
      -511073,
      529812,
      -496052,
      440334,
      446527,
      463747,
      -515779,
      -302770,
      -446485,
      511607,
      -342239,
      -568521,
      335344,
      437816,
      385371,
      -335884,
      222586,
      -235547,
      352048,
      -247311,
      -208253,
      -301040,
      196724,
      250794,
      -357234,
      -306235,
      460239,
      165520,
      -266653,
      399013,
      123462,
      154462,
      -331046,
      -222626,
      465661,
      172620,
      -244619,
      301333,
      -298021,
      -245716,
      -153714,
      244690,
      -194772,
      -294915,
      -148691,
      -161346,
      668443
    ],
    "N": 1000000,
    "rounding_scale": 100000000000000000000,
    "head_lower": "560095994926118051/50000000000000000000",
    "head_upper": "560095994926618051/50000000000000000000",
    "period_mean_square": "332010660858140711060130219529964199928414207385906945723399518368576076043186816053/797346545455782502045194312458518971378751390985005407945694000497276735000000000000",
    "centered_partial_sum_bound": "186230189747712567/1000000000000",
    "zeta_lower": "20563731940690556584651/12501250000000000000000",
    "zeta_upper": "257020948726259347/156250000000000000",
    "full_error_lower": "89320135181868070621905039135458555567121453800904398960815700516120705413103179325944149320599168697/13115851228568753936630479028112340229364241665887169535141497740281350303465901423540271260219481090880",
    "full_error_upper": "12237265382977470867937983860372786758057279751861437195169261132642409985845006436167987192533203604099/1796871607391341917757423437912877492712125897180067105308604962930663390238939571963445440756551996755560",
    "full_error_lower_display": 0.006810090601463386,
    "full_error_upper_display": 0.006810317071425743,
    "simple_tail_upper_display": 0.006889826201156398,
    "simple_tail_upper": "874578226361056909602498232818441365674422814353809063/126937632507227320640193081667615572573742483449860513520",
    "strict_rational_bound": "6811/1000000",
    "strict_rational_bound_display": 0.006811,
    "exact_arithmetic_checks_passed": true,
    "status": "Exact integer/rational certificate with an analytic infinite-tail proof; NOT Lean-checked"
  },
  {
    "label": "squarefree_200",
    "dictionary": [
      2,
      3,
      5,
      6,
      7,
      10,
      11,
      13,
      14,
      15,
      17,
      19,
      21,
      22,
      23,
      26,
      29,
      30,
      31,
      33,
      34,
      35,
      37,
      38,
      39,
      41,
      42,
      43,
      46,
      47,
      51,
      53,
      55,
      57,
      58,
      59,
      61,
      62,
      65,
      66,
      67,
      69,
      70,
      71,
      73,
      74,
      77,
      78,
      79,
      82,
      83,
      85,
      86,
      87,
      89,
      91,
      93,
      94,
      95,
      97,
      101,
      102,
      103,
      105,
      106,
      107,
      109,
      110,
      111,
      113,
      114,
      115,
      118,
      119,
      122,
      123,
      127,
      129,
      130,
      131,
      133,
      134,
      137,
      138,
      139,
      141,
      142,
      143,
      145,
      146,
      149,
      151,
      154,
      155,
      157,
      158,
      159,
      161,
      163,
      165,
      166,
      167,
      170,
      173,
      174,
      177,
      178,
      179,
      181,
      182,
      183,
      185,
      186,
      187,
      190,
      191,
      193,
      194,
      195,
      197,
      199
    ],
    "coefficient_denominator": 1000000,
    "coefficient_numerators": [
      992129,
      979241,
      911722,
      -799495,
      845277,
      -708188,
      729602,
      701465,
      -664506,
      -659242,
      659061,
      597013,
      -596008,
      -564055,
      590072,
      -564881,
      560362,
      481134,
      508357,
      -525854,
      -447497,
      -512524,
      569268,
      -522893,
      -471668,
      469584,
      447591,
      389339,
      -409413,
      408900,
      -445439,
      509013,
      -417588,
      -369035,
      -432840,
      366654,
      422211,
      -383915,
      -415165,
      547530,
      346474,
      -592024,
      386965,
      337553,
      309944,
      -365931,
      -335971,
      397056,
      451698,
      -354277,
      330668,
      -378013,
      -248564,
      -428929,
      445246,
      -348123,
      -343109,
      -260458,
      -306045,
      540981,
      206882,
      251382,
      215086,
      280928,
      -360641,
      182715,
      122430,
      226498,
      -333920,
      257637,
      435232,
      -117238,
      -321099,
      -188526,
      -255024,
      -264956,
      262498,
      -196476,
      260434,
      187225,
      -255359,
      -318297,
      257706,
      428683,
      267828,
      -141103,
      -202750,
      -217124,
      -327199,
      -231010,
      190671,
      117777,
      319228,
      -146675,
      220858,
      -353256,
      -270091,
      -283854,
      181224,
      207616,
      -177300,
      148725,
      123269,
      237213,
      399613,
      -143309,
      -427209,
      269591,
      209928,
      281060,
      -279749,
      -298607,
      289292,
      -233487,
      281355,
      219505,
      265811,
      -460478,
      132548,
      -26187,
      -474843
    ],
    "N": 2000000,
    "rounding_scale": 100000000000000000000,
    "head_lower": "482955104505085687/50000000000000000000",
    "head_upper": "482955104506085687/50000000000000000000",
    "period_mean_square": "59661875481814048292947793353662783432542262272565718529535810893023564092519040773881006274905087263083427673125350545481414779543609643382384790449394425517985527939959291399/91258175784509249022294249367332965354867397184097613013666356249019202131439523581354062388118804674622555707114012887082388893405592546149064424461322015221984150000000000000",
    "centered_partial_sum_bound": "10451955150997945739/4000000000000",
    "zeta_lower": "20563731940690556584651/12501250000000000000000",
    "zeta_upper": "257020948726259347/156250000000000000",
    "full_error_lower": "1175257512981876322075458374365440398508934283735505954734972112082322886124680261333834578048799165581976414294734726483392579264637213797265183512947373811607693787845560849343237896502872407/200151777061812027990962207942708765584358271612330157355412429670149762293249941858919815326763039862048358635875010892232138563989578386388946162144905478828400713454768072340226794387249813440",
    "full_error_upper": "783610989376182738138700149457380304781744955465451907581161170250718362375785907010118688639763175827567612092209589332722389067861863875880593368750242185412193653959220951893840535332280649/133434517230104524962173303048825252210435557959176247504196747829931592235154784020902016126679536183711532997524649553792193446449124384808145724543459252673424615492620546428085419551011338960",
    "full_error_lower_display": 0.0058718315182329185,
    "full_error_upper_display": 0.005872625806595942,
    "simple_tail_upper_display": 0.006013708163587516,
    "simple_tail_upper": "354541469990846953022731109846079689013715207111484539376713477930709277035597327513734872432465473935904737807842899441759184603758071776454824843260639819343912158029/58955549612062143078568052465262242626499999784849725211669283059371207163725593857901159497830833287646063876575937974509450670989679768163445526006246252005791715220960",
    "strict_rational_bound": "5873/1000000",
    "strict_rational_bound_display": 0.005873,
    "exact_arithmetic_checks_passed": true,
    "status": "Exact integer/rational certificate with an analytic infinite-tail proof; NOT Lean-checked"
  }
]
```

## gram_optimality.json

```json
{
  "status": "Exact rational complete-moment enclosures and LDL proof; NOT Lean-checked",
  "dictionary": [
    2,
    3,
    5,
    6,
    10,
    15,
    30
  ],
  "gram_interval": [
    [
      [
        "12338239170253929583468721599/65803942774703192256089182080",
        "123394731066828380405271684731599/658105227689406575745147409972080"
      ],
      [
        "220330609670249442958561805/1880112650705805493031119488",
        "5141561869304778502133412095545/43873681845960438383009827331472"
      ],
      [
        "173191768953507172384957453/1880112650705805493031119488",
        "12124637189231192720353916416171/131621045537881315149029481994416"
      ],
      [
        "323707473459617090996036141/3655774598594621792004954560",
        "9712195847095363354654239008423/109684204614901095957524568328680"
      ],
      [
        "4000091887195788270483417077/65803942774703192256089182080",
        "40004924089363909134105654207077/658105227689406575745147409972080"
      ],
      [
        "205547497075999081207246579/4700281626764513732577798720",
        "4796590395630530437025403755351/109684204614901095957524568328680"
      ],
      [
        "566144034875151301401849697/21934647591567730752029727360",
        "5662011534959331712320232159697/219368409229802191915049136657360"
      ]
    ],
    [
      [
        "220330609670249442958561805/1880112650705805493031119488",
        "5141561869304778502133412095545/43873681845960438383009827331472"
      ],
      [
        "19869630033770603433030306319/118447096994465746060960527744",
        "66238724333797761320845964510773/394863136613643945447088445983248"
      ],
      [
        "6892958832993703374464949583/65803942774703192256089182080",
        "22978829640957813821341653599861/219368409229802191915049136657360"
      ],
      [
        "61981445339058276673257236557/592235484972328730304802638720",
        "206625487807397795467751540995519/1974315683068219727235442229916240"
      ],
      [
        "762030009020307625148850703/10967323795783865376014863680",
        "7621064645465860020113822550703/109684204614901095957524568328680"
      ],
      [
        "15905084945963977090584741473/296117742486164365152401319360",
        "53022263021580921818314166520491/987157841534109863617721114958120"
      ],
      [
        "18633836393616505637991444011/592235484972328730304802638720",
        "62119044767651189093187143911337/1974315683068219727235442229916240"
      ]
    ],
    [
      [
        "173191768953507172384957453/1880112650705805493031119488",
        "12124637189231192720353916416171/131621045537881315149029481994416"
      ],
      [
        "6892958832993703374464949583/65803942774703192256089182080",
        "22978829640957813821341653599861/219368409229802191915049136657360"
      ],
      [
        "7993520878719195297958146139/65803942774703192256089182080",
        "79943205048356753390880419556139/658105227689406575745147409972080"
      ],
      [
        "6275128177748322412442103029/65803942774703192256089182080",
        "20919190691284239987611490804343/219368409229802191915049136657360"
      ],
      [
        "4952571455199709325631512669/65803942774703192256089182080",
        "49530672343985374081641758222669/658105227689406575745147409972080"
      ],
      [
        "1850483424960190177683095237/32901971387351596128044591040",
        "6168896196694856391669711825079/109684204614901095957524568328680"
      ],
      [
        "1102070570594765254567822237/32901971387351596128044591040",
        "3673938460205707056311096734079/109684204614901095957524568328680"
      ]
    ],
    [
      [
        "323707473459617090996036141/3655774598594621792004954560",
        "9712195847095363354654239008423/109684204614901095957524568328680"
      ],
      [
        "61981445339058276673257236557/592235484972328730304802638720",
        "206625487807397795467751540995519/1974315683068219727235442229916240"
      ],
      [
        "6275128177748322412442103029/65803942774703192256089182080",
        "20919190691284239987611490804343/219368409229802191915049136657360"
      ],
      [
        "12508680483377036875085994967/118447096994465746060960527744",
        "41699773124398658480512278566989/394863136613643945447088445983248"
      ],
      [
        "4460393681978288923377925811/65803942774703192256089182080",
        "14869470802220121721234545351937/219368409229802191915049136657360"
      ],
      [
        "7858230569378557341782422889/148058871243082182576200659680",
        "26196732710654975316222753785963/493578920767054931808860557479060"
      ],
      [
        "4939044020965432273465205119/148058871243082182576200659680",
        "16465137832235747161392588813373/493578920767054931808860557479060"
      ]
    ],
    [
      [
        "4000091887195788270483417077/65803942774703192256089182080",
        "40004924089363909134105654207077/658105227689406575745147409972080"
      ],
      [
        "762030009020307625148850703/10967323795783865376014863680",
        "7621064645465860020113822550703/109684204614901095957524568328680"
      ],
      [
        "4952571455199709325631512669/65803942774703192256089182080",
        "49530672343985374081641758222669/658105227689406575745147409972080"
      ],
      [
        "4460393681978288923377925811/65803942774703192256089182080",
        "14869470802220121721234545351937/219368409229802191915049136657360"
      ],
      [
        "80661696498987804585032581/1175070406691128433144449680",
        "5646884047497493165709500900567/82263153461175821968143426246510"
      ],
      [
        "195754922731320588489863089/4112746423418949516005573880",
        "217527325976679928845798139371/4570175192287545664896857013695"
      ],
      [
        "69203065075965884626391749/2193464759156773075202972736",
        "23865529725607902994778524681/756442790447593765224307367784"
      ]
    ],
    [
      [
        "205547497075999081207246579/4700281626764513732577798720",
        "4796590395630530437025403755351/109684204614901095957524568328680"
      ],
      [
        "15905084945963977090584741473/296117742486164365152401319360",
        "53022263021580921818314166520491/987157841534109863617721114958120"
      ],
      [
        "1850483424960190177683095237/32901971387351596128044591040",
        "6168896196694856391669711825079/109684204614901095957524568328680"
      ],
      [
        "7858230569378557341782422889/148058871243082182576200659680",
        "26196732710654975316222753785963/493578920767054931808860557479060"
      ],
      [
        "195754922731320588489863089/4112746423418949516005573880",
        "217527325976679928845798139371/4570175192287545664896857013695"
      ],
      [
        "28150601500217060805303724793/592235484972328730304802638720",
        "93844745272498075152617183944931/1974315683068219727235442229916240"
      ],
      [
        "17311225254733592057559345649/592235484972328730304802638720",
        "57709900396595073220553338671883/1974315683068219727235442229916240"
      ]
    ],
    [
      [
        "566144034875151301401849697/21934647591567730752029727360",
        "5662011534959331712320232159697/219368409229802191915049136657360"
      ],
      [
        "18633836393616505637991444011/592235484972328730304802638720",
        "62119044767651189093187143911337/1974315683068219727235442229916240"
      ],
      [
        "1102070570594765254567822237/32901971387351596128044591040",
        "3673938460205707056311096734079/109684204614901095957524568328680"
      ],
      [
        "4939044020965432273465205119/148058871243082182576200659680",
        "16465137832235747161392588813373/493578920767054931808860557479060"
      ],
      [
        "69203065075965884626391749/2193464759156773075202972736",
        "23865529725607902994778524681/756442790447593765224307367784"
      ],
      [
        "17311225254733592057559345649/592235484972328730304802638720",
        "57709900396595073220553338671883/1974315683068219727235442229916240"
      ],
      [
        "2920277215534673990942372149/118447096994465746060960527744",
        "9735240001893768265738821299383/394863136613643945447088445983248"
      ]
    ]
  ],
  "mean_interval": [
    [
      "24676478390507861131533888109/65803942774703192256089182080",
      "246789461633606700442471414998109/658105227689406575745147409972080"
    ],
    [
      "858464035588511845084798411/2350140813382256866288899360",
      "6677610244203144721427970262653/18280700769150182659587428054780"
    ],
    [
      "1949782659519472193482763665/6580394277470319225608918208",
      "19499776667885249608621219415665/65810522768940657574514740997208"
    ],
    [
      "4415679362478689513989149923/16450985693675798064022295520",
      "4906801128711854002322859820547/18280700769150182659587428054780"
    ],
    [
      "6437320354722087210043827991/32901971387351596128044591040",
      "64379643592859385320648823747991/329052613844703287872573704986040"
    ],
    [
      "9740518414756670181804248999/65803942774703192256089182080",
      "373237289783403093885920667659/2521475968158645884081024559280"
    ],
    [
      "5831994654154789334008344229/65803942774703192256089182080",
      "6480643780123107099490938961581/73122803076600730638349712219120"
    ]
  ],
  "lower_eigenvalue_bound": "1/250",
  "positive_ldl_pivots": [
    "12415371793691684773604985226990967770229119452506009/67658731992976880229778532891578180606761643612704000",
    "168039474210781850576586073248788500851756505056338332188113306066766626220806960352718484906775167751601/1890018703760738282160512265512318686952317064836335806641662421622026633370773947194750009792314661256000",
    "67525729330235257364768866919188209168997995671654970328998886068573539921689147390454764233150224622174877229873508576503527074258196277116221523187542723/1421167218733504923139740028309544775719095171195711031877863143988965094357807248786676469392472031697288528897515838985165927169592607382851377814992388000",
    "339012025770710879613550190701442623656424794625305348546984390097259168095398118793797147237023230600566752086579833797604037907926719709085362216855053010618372168353191464448053013984950927431012390136753/18274820893538741961344496744242530917609040039093844209427900423533041835492259773525513731174506654056454412330713253846311592854612802645809841909282989631383538000165734097662163120150207533096262211968000",
    "880809754825202311183824713908190433261875176109751183099232671761404224226601578589513645686979323104320650294363615678970188056512273683545339990881437735926688735859279900980877622606762816664822654382673802226828878820779529012999353174759021219956859247/61165663450711196780598258246885657404056205278691419819294903374459297499325965085234687781856986383950744118073140882217559315491471379964102619926424262627099874569849132865830441136639441808753399425664496239687943381651098200593095687904694537408293632000",
    "204755765611327183529039353673540269428976803807677384855209861517885184247321969718363162159096635699210237095871439336228189319223379718868830460988200679896016215414814080521843963323692649442015743807721658973703261042942553065632868220543159219291080763912112359239725102981246376128451146044181904600617/25540487630793444692250084607669392188080415208971560138076689472823377135610885558899741808790911531628931064990869208946312843767890247563040708064610282902928096988846351759308336968234418119678072980672662799295439122110732389774972759656735967080173460752029706339930897262117363730087187163675846745952000",
    "15869239258412127538236143834600578933610384843311984414664873702767013461041081057621359107548748600892285843928822639817557102106367506855438696806140602741500215752181220553824555288610696778010051129910460527755840704637679297788657028419199899438759012692197988084820671023591704051773966371690550832623340805049135582062040117725105685362909222112491607/32324869428865014888073467237363992810980198520458314510950124611627112068297865543030584575381089785063463068226254458806207739963410206991832191153141081796405045978915650683951337805609936658974441400654163540413891243743601552757674275901604410102372764118236147754055588685634900680733457153087005412404107808105721506631363645940393414926138623677356192000"
  ],
  "normal_residual_component_upper": [
    "6059879866045393424615522566536146252916887076917/112764553321628133716297554819296967677936072687840000000",
    "1985149334334489094436890778777829963159342786587/24163832854634600082063761746992207359557729861680000000",
    "93837937303164976230888086001536986250606633991109/1353174639859537604595570657831563612135232872254080000000",
    "53400113657867313810562572072909530640944988473093/676587319929768802297785328915781806067616436127040000000",
    "7094129334894959527855763649428037490600645023833/112764553321628133716297554819296967677936072687840000000",
    "685926453557441397899708375566527474291174200959/10571676873902637535902895764309090719806506814485000000",
    "9172303934682012523182769948541066873755135394747/135317463985953760459557065783156361213523287225408000000"
  ],
  "certified_suboptimality_upper": "61226988924396748179587243064318803809402077179308739386426360913749369495404321703924639330383419297/7324326423835957189399508102137315184633823904612895351510822700115020034019530491248033281200306585600000000000",
  "certified_suboptimality_display": 8.359401995675999e-12,
  "strict_suboptimality_bound": "1/100000000000"
}
```

## method_comparison.json

```json
{
  "status": "Floating complete-Q diagnostics only; no certified optimization claim",
  "dictionary": [
    2,
    3,
    5,
    6,
    7,
    10,
    11,
    13,
    14,
    15,
    17,
    19,
    21,
    22,
    23,
    26,
    29,
    30
  ],
  "retained_rows": [
    1,
    2,
    3,
    4,
    5,
    6,
    10,
    12,
    15,
    20,
    30,
    60
  ],
  "complete_Gram_error": 0.009866930389172412,
  "projected_anchor_error": 0.009866930389172412,
  "methods": [
    {
      "method": "singleton_columns",
      "certificate_at_Gram_solution": 0.6739755889234607,
      "note": "Same complete-Gram coefficient vector for every method; no separate optimization claimed"
    },
    {
      "method": "pairs",
      "certificate_at_Gram_solution": 0.4244925918431435,
      "note": "Same complete-Gram coefficient vector for every method; no separate optimization claimed"
    },
    {
      "method": "four_consecutive_blocks",
      "certificate_at_Gram_solution": 0.08503581786179795,
      "note": "Same complete-Gram coefficient vector for every method; no separate optimization claimed"
    },
    {
      "method": "one_signed_block",
      "certificate_at_Gram_solution": 0.009866930389172694,
      "note": "Same complete-Gram coefficient vector for every method; no separate optimization claimed"
    }
  ]
}
```
