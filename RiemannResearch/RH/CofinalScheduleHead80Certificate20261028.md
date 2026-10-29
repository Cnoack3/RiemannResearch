# A rigorous H=80 CRT certificate and exploratory H=320 comparison

28 October 2026. This packet supplements the delayed-period research. It does
not modify or replace the previously published fixed-stage minimizers.

## Established finite computational result

For `H=80`, use the primorial through 79,

```
L = 3217644767340672907899084554130
```

and the 126 squarefree conductors `2<=d<=300` all of whose prime factors are
at most 79. The explicit rational witness below is legal in this divisor
stage and has `F(n)=1` for every `1<=n<=80`. Its complete Q-energy satisfies

```
||F||_Q^2 <= 13222897792897/13159200000000
           = 1.004840552077406...
           < 129/128 = 1.0078125.
```

This certifies the proposed finite n=2 target for `H_n=5*4^n`. It is an exact
Python integer/rational certificate, **not a new Lean kernel theorem**.
It neither proves the n>=3 targets nor establishes a uniformly bounded
cofinal family.

## Signed head equations and constrained Gram system

Every conductor is squarefree and divides L. Write
`F(n)=sum_d c_d*(n mod d)/d`. The coefficients satisfy the exact equations

```
c_d = -mu(d) for every dictionary conductor d<=80,
sum_d c_d/d = 1,
F(n) = 1 for n=1,...,80.
```

The last eighty equations are individually checked in exact rational
arithmetic. The first two are also checked independently. Coefficients at
conductors above 80 are signed real/rational unknowns; all cross terms are
retained. For `ell=lcm(d,e)`, the complete Gram entry is

```
G_de = (1/zeta(2)) sum_(r=1)^ell
  (r mod d)/d * (r mod e)/e * polygamma(1,r/ell)/ell^2.
```

The free constrained system is the same reduced signed system as in the
previous packet: fixed low coefficients `-mu(d)`, one remaining normalization,
and the full quadratic form. Independently evaluating all entries by this
pairwise-LCM formula gives numerical minimum
`1.0025777204044914` over the 126-atom dictionary.
This is a numerical minimum of the restricted dictionary, not a claimed
minimum over every divisor of L. Enlarging to the full divisor dictionary
can only decrease its constrained minimum.

The initial discovery script used a finite prefix through 200000 plus the
periodic mean tail approximation. For clarity, that approximation is not
used as a rigorous tail bound. The independent complete-Gram computation
and the exact certificate are separate checks.

## Exact infinite-tail certificate

The witness coefficients have one common rational denominator. Setting
`F(n)=P(n)/T` gives exact integer `P(n)` and

```
T = 32176447673406729078990845541300000
K = 524288
S = 1000000000000
sum_(n=1)^K ceil(S*P(n)^2/(T^2*n^2)) = 1649169597159.
```

The exact signed atom estimates give

```
positive coefficient bound = 283089633417982353133749333953864281/6435289534681345815798169108260000
negative coefficient bound = 1404989348117263043005930822592739181/32176447673406729078990845541300000
```

Both are below 44, so `|F(n)|<=44` for all n. By the integral test,
`sum_(n>K) F(n)^2/n^2 <= 44^2/K`. Thus the complete raw energy is at most
`13222897792897/8000000000000`. The rational bound

```
zeta(2) > sum_(n=1)^200 1/n^2 + 1/201 > 16449/10000
```

then gives the stated complete Q-energy bound. Every finite arithmetic
operation is an unbounded Python integer or Fraction operation; floating
point is used only for discovery and the displayed decimal.

## Quantitative approximation consequence

Let `m=sum_(n>80) Q(n)`. Exact head matching gives the signed identity

```
||F-1||_Q^2 = ||F||_Q^2 - 1 + 2m - 2*sum_(n>80) F(n)Q(n).
```

Applying `(F(n)-1)^2 <= 2F(n)^2+2` only on the tail gives
`||F-1||_Q^2 <= 2(||F||_Q^2-1)+4m`. Since
`m < (76/125)/80`, the exact arithmetic consequence is

```
||F-1||_Q^2 < 263717632897/6579600000000
             < (201/1000)^2.
```

Thus this candidate has Q-error norm below 0.201. The checker verifies both
rational comparisons; Wolfram independently confirmed their arithmetic.
This consequence uses an ordinary mathematical tail argument and the external
certificate, and is not presented as a new kernel-checked instance.

## H=320 exploration

The target is `513/512=1.001953125`. For all squarefree conductors up to the
specified cutoff, restricted to primes at most the given bound, numerical
prefix-Gram optimization with a periodic-mean tail approximation gave:

| Conductor cutoff | Prime bound | Approximate complete energy |
|---:|---:|---:|
| 1000 | 317 | 1.008676278939 |
| 1000 | 337 | 1.008672430381 |
| 1000 | 499 | 1.008586220413 |
| 1000 | 1000 | 1.008559208893 |
| 1500 | 317 | 1.007054616746 |
| 1500 | 337 | 1.007048713234 |
| 1500 | 499 | 1.007002024622 |
| 1500 | 1500 | 1.006961949596 |

These tests did not produce an H=320 witness below the proposed target.
They are exploratory numerical computations, not rigorous lower bounds on
these restricted minima and not obstructions for larger dictionaries.
No H=320 feasibility or infeasibility assertion at energy 513/512 is made.

## Reproduction and extraction

The file blocks below are complete sources and data. Save each block under
its indicated filename in one directory. Exact checking needs Python's
standard library only:

```
python certify_head80.py witness_head80.json
```

This is read-only and compares recomputed output with the recorded certificate.
Numerical rediscovery additionally uses NumPy and SciPy:

```
OPENBLAS_NUM_THREADS=4 python explore.py 300 200000 80
OPENBLAS_NUM_THREADS=4 python complete_gram.py
OPENBLAS_NUM_THREADS=4 python explore.py 1000 200000 320
OPENBLAS_NUM_THREADS=4 python explore.py 1500 200000 320
```

To reconstruct the rounded witness after the first discovery run, use
`python make_head80.py`. This writes a new witness; it does not itself certify
its energy. The supplied JSON already contains the independently checked
certificate and is the authoritative exact witness.

## File: certify_head80.py

<!-- FILE: certify_head80.py -->
```python
"""Exact, read-only verification of the H=80 candidate against 129/128.
All certificate arithmetic uses Python unbounded integers and Fraction.
The complete infinite tail is bounded by B^2/K via the integral test.
"""
from fractions import Fraction as F
from pathlib import Path
import json,math,time,sys
ROOT=Path(__file__).parent

def verify(w):
 L=w['period'];H=w['head'];D=w['denominator'];K=w['prefix'];S=w['rounding_scale'];target=F(w['target'])
 assert L>0 and D>0 and S>0 and K>=H>0 and H<L
 primes=[p for p in range(2,80)if all(p%d for d in range(2,math.isqrt(p)+1))]
 assert w['period_primes']==primes
 assert L==math.prod(primes)
 cs={d:F(c,D)for d,c in w['coefficients']};assert len(cs)==len(w['coefficients'])
 for d in cs:
  assert d>1 and L%d==0
  assert all(d%(p*p)for p in range(2,math.isqrt(d)+1))
 assert sum(c/d for d,c in cs.items())==1
 for d,c in cs.items():
  if d<=H:
   m=d;mu=1;p=2
   while p<=m:
    if m%p==0:mu=-mu;m//=p
    p+=1
   assert c==-mu
 scaled={d:c/d for d,c in cs.items()};T=math.lcm(*(v.denominator for v in scaled.values()));terms=[(d,int(v*T))for d,v in scaled.items()]
 assert all(F(a,T)==cs[d]/d for d,a in terms)
 positive=sum((c*F(d-1,d)for d,c in cs.items()if c>0),F(0));negative=sum((-c*F(d-1,d)for d,c in cs.items()if c<0),F(0));B=math.ceil(max(positive,negative))
 total=0
 for n in range(1,K+1):
  P=sum(a*(n%d)for d,a in terms)
  if n<=H:assert P==T
  denominator=T*T*n*n;numerator=S*P*P
  total+=(numerator+denominator-1)//denominator
 zeta_lower=F(16449,10000)
 assert sum((F(1,n*n)for n in range(1,201)),F(1,201))>zeta_lower
 raw_upper=F(total,S)+F(B*B,K);upper=raw_upper/zeta_lower
 assert upper<=target
 error_sq_upper=2*(upper-1)+F(4*76,125*H)
 assert error_sq_upper==F(263717632897,6579600000000)
 assert error_sq_upper<F(201,1000)**2
 result={'prefix':K,'rounding_scale':S,'ceil_sum':total,'uniform_bound':B,'positive_coefficient_bound':str(positive),'negative_coefficient_bound':str(negative),'scaled_value_denominator':T,'raw_energy_upper':str(raw_upper),'complete_Q_energy_upper':str(upper),'target':str(target),'strict':upper<target}
 if 'certificate' in w:assert w['certificate']==result
 return result

if __name__=='__main__':
 p=Path(sys.argv[1])if len(sys.argv)>1 else ROOT/'witness_head80.json';w=json.loads(p.read_text());t=time.time();out=verify(w);print(json.dumps(out,indent=2));print('ELAPSED_SECONDS',time.time()-t)
```

## File: witness_head80.json

<!-- FILE: witness_head80.json -->
```json
{
  "period": 3217644767340672907899084554130,
  "period_primes": [
    2,
    3,
    5,
    7,
    11,
    13,
    17,
    19,
    23,
    29,
    31,
    37,
    41,
    43,
    47,
    53,
    59,
    61,
    67,
    71,
    73,
    79
  ],
  "head": 80,
  "target": "129/128",
  "prefix": 524288,
  "rounding_scale": 1000000000000,
  "denominator": 392395703334228403402327384650000,
  "coefficients": [
    [
      2,
      392395703334228403402327384650000
    ],
    [
      3,
      392395703334228403402327384650000
    ],
    [
      5,
      392395703334228403402327384650000
    ],
    [
      6,
      -392395703334228403402327384650000
    ],
    [
      7,
      392395703334228403402327384650000
    ],
    [
      10,
      -392395703334228403402327384650000
    ],
    [
      11,
      392395703334228403402327384650000
    ],
    [
      13,
      392395703334228403402327384650000
    ],
    [
      14,
      -392395703334228403402327384650000
    ],
    [
      15,
      -392395703334228403402327384650000
    ],
    [
      17,
      392395703334228403402327384650000
    ],
    [
      19,
      392395703334228403402327384650000
    ],
    [
      21,
      -392395703334228403402327384650000
    ],
    [
      22,
      -392395703334228403402327384650000
    ],
    [
      23,
      392395703334228403402327384650000
    ],
    [
      26,
      -392395703334228403402327384650000
    ],
    [
      29,
      392395703334228403402327384650000
    ],
    [
      30,
      392395703334228403402327384650000
    ],
    [
      31,
      392395703334228403402327384650000
    ],
    [
      33,
      -392395703334228403402327384650000
    ],
    [
      34,
      -392395703334228403402327384650000
    ],
    [
      35,
      -392395703334228403402327384650000
    ],
    [
      37,
      392395703334228403402327384650000
    ],
    [
      38,
      -392395703334228403402327384650000
    ],
    [
      39,
      -392395703334228403402327384650000
    ],
    [
      41,
      392395703334228403402327384650000
    ],
    [
      42,
      392395703334228403402327384650000
    ],
    [
      43,
      392395703334228403402327384650000
    ],
    [
      46,
      -392395703334228403402327384650000
    ],
    [
      47,
      392395703334228403402327384650000
    ],
    [
      51,
      -392395703334228403402327384650000
    ],
    [
      53,
      392395703334228403402327384650000
    ],
    [
      55,
      -392395703334228403402327384650000
    ],
    [
      57,
      -392395703334228403402327384650000
    ],
    [
      58,
      -392395703334228403402327384650000
    ],
    [
      59,
      392395703334228403402327384650000
    ],
    [
      61,
      392395703334228403402327384650000
    ],
    [
      62,
      -392395703334228403402327384650000
    ],
    [
      65,
      -392395703334228403402327384650000
    ],
    [
      66,
      392395703334228403402327384650000
    ],
    [
      67,
      392395703334228403402327384650000
    ],
    [
      69,
      -392395703334228403402327384650000
    ],
    [
      70,
      392395703334228403402327384650000
    ],
    [
      71,
      392395703334228403402327384650000
    ],
    [
      73,
      392395703334228403402327384650000
    ],
    [
      74,
      -392395703334228403402327384650000
    ],
    [
      77,
      -392395703334228403402327384650000
    ],
    [
      78,
      392395703334228403402327384650000
    ],
    [
      79,
      392395703334228403402327384650000
    ],
    [
      82,
      -67277893868264857620769605300893
    ],
    [
      85,
      -109713838652250261591290736748140
    ],
    [
      86,
      -226451560394183211603483133681515
    ],
    [
      87,
      -147972419727337530923017656751515
    ],
    [
      91,
      -40926871857760022474862746218995
    ],
    [
      93,
      -247052334819230202782105321375640
    ],
    [
      94,
      -294689173204005530955147865872150
    ],
    [
      95,
      -19266629033710614607054274586315
    ],
    [
      102,
      660715885274173785648838850273670
    ],
    [
      105,
      554141212248597351284766732602730
    ],
    [
      106,
      -175165441968399559278798944507760
    ],
    [
      110,
      422767130772297681825667524221910
    ],
    [
      111,
      -276638970850631024398640806178250
    ],
    [
      114,
      490416150027118658572228765335570
    ],
    [
      115,
      -138084048003314975157279006658335
    ],
    [
      118,
      -234495672312534893873230845066840
    ],
    [
      119,
      -164806195400375929428977501553000
    ],
    [
      122,
      -255057207167248462211512800022500
    ],
    [
      123,
      -179207117712742111833842916569655
    ],
    [
      129,
      -86680210866531054311574119269185
    ],
    [
      130,
      342482969870114550489551341322520
    ],
    [
      133,
      -143459869138993904283890891828040
    ],
    [
      134,
      -221585853672838779401294274111855
    ],
    [
      138,
      557476575726938292713686515372255
    ],
    [
      141,
      -235358942859870196360715965313070
    ],
    [
      142,
      -280994563157640959676406640147865
    ],
    [
      143,
      -162844216883704787411965864629750
    ],
    [
      145,
      -73260277812500442915214522714155
    ],
    [
      146,
      -74672902344503665167462901298895
    ],
    [
      154,
      469030584195403210586801922872145
    ],
    [
      155,
      -47283682251774522609980449850325
    ],
    [
      158,
      -264435464476936521052828424515635
    ],
    [
      159,
      -270988472722618135389647291839290
    ],
    [
      161,
      -96097707746552535993229976500785
    ],
    [
      165,
      186544917365092182977466438662610
    ],
    [
      170,
      105358246345240326313524902778525
    ],
    [
      174,
      345112021082453880792346934799675
    ],
    [
      177,
      -82442337270521387554828983514965
    ],
    [
      182,
      158449385006361429293859797921670
    ],
    [
      183,
      -256391352558584838783080713130310
    ],
    [
      185,
      -195844695534113396138101597678815
    ],
    [
      186,
      293355027812669154383579952764340
    ],
    [
      187,
      -96764780442220724279013933054690
    ],
    [
      190,
      220958020547504013955850550296415
    ],
    [
      195,
      396162702086236996074989727542640
    ],
    [
      201,
      -67138904840486479822138215513615
    ],
    [
      203,
      -228217341059187239418793606912440
    ],
    [
      205,
      -313877323097049299881521674981535
    ],
    [
      209,
      -59840344758469831518854926159125
    ],
    [
      210,
      -490887024871119732656311558197150
    ],
    [
      213,
      -223351634337842807216604747342780
    ],
    [
      215,
      -57132814405463655535378867205040
    ],
    [
      217,
      -129176665537627990400046175026780
    ],
    [
      219,
      -308344543680036679393548858857970
    ],
    [
      221,
      -77655109689843801033320589422235
    ],
    [
      222,
      385607257666546252023467120895555
    ],
    [
      230,
      231866621100195563570435251589685
    ],
    [
      231,
      285075478472316935071790844948225
    ],
    [
      235,
      -192352373774438763347820883955430
    ],
    [
      237,
      -288371602380324453660370394979285
    ],
    [
      238,
      327179537440079642756860573321170
    ],
    [
      246,
      72553965546498831789090333421785
    ],
    [
      247,
      -36728237832083778558457843203240
    ],
    [
      253,
      -8122591059018527950428176862255
    ],
    [
      255,
      56348022998795198728574212435740
    ],
    [
      258,
      54856919326125130795645368374070
    ],
    [
      259,
      -199533215145455143130083475094525
    ],
    [
      265,
      -221193457969504550997891946727205
    ],
    [
      266,
      126979249598956311340993141672740
    ],
    [
      273,
      151621699768345855074659301428760
    ],
    [
      282,
      314308958370716951125264235104650
    ],
    [
      285,
      29939792164401627179597579448795
    ],
    [
      286,
      208872232884809779131058866849195
    ],
    [
      287,
      -170260495676721704236269852199635
    ],
    [
      290,
      -30567625289736392625041303264235
    ],
    [
      295,
      -193568800454774871398368098847845
    ],
    [
      299,
      -427985993626642919590918478437755
    ]
  ],
  "discovery": "signed prefix Gram through 200000 plus periodic-mean tail approximation; certification independent of discovery",
  "certificate": {
    "prefix": 524288,
    "rounding_scale": 1000000000000,
    "ceil_sum": 1649169597159,
    "uniform_bound": 44,
    "positive_coefficient_bound": "283089633417982353133749333953864281/6435289534681345815798169108260000",
    "negative_coefficient_bound": "1404989348117263043005930822592739181/32176447673406729078990845541300000",
    "scaled_value_denominator": 32176447673406729078990845541300000,
    "raw_energy_upper": "13222897792897/8000000000000",
    "complete_Q_energy_upper": "13222897792897/13159200000000",
    "target": "129/128",
    "strict": true
  }
}
```

## File: explore.py

<!-- FILE: explore.py -->
```python
"""Signed finite-prefix Gram discovery with explicit periodic-mean tail approximation.
This is not an exact complete Gram computation; candidates require certification.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='4'
import numpy as np,math,json,time
from scipy.linalg import solve
from pathlib import Path
OUT=Path(__file__).parent

def factor(n):
 p=2;fs=[]
 while p*p<=n:
  while n%p==0:fs.append(p);n//=p
  p+=1
 if n>1:fs.append(n)
 return fs

def dictionary(M):
 ds=[];mu={};maxp={}
 for n in range(2,M+1):
  fs=factor(n)
  if len(fs)==len(set(fs)):ds.append(n);mu[n]=(-1)**len(fs);maxp[n]=max(fs)
 return np.array(ds,dtype=np.int64),mu,maxp

def gram(M,N):
 ds,mu,maxp=dictionary(M);path=OUT/f'prefix_gram_{M}_{N}.npz'
 if path.exists():return ds,mu,maxp,np.load(path)['G']
 G=np.zeros((len(ds),len(ds)));t=time.time()
 for st in range(1,N+1,8192):
  ns=np.arange(st,min(st+8192,N+1),dtype=np.int64)
  A=(ns[:,None]%ds)/ds/ns[:,None];G+=A.T@A
 np.savez(path,G=G);print('GRAM',M,N,len(ds),time.time()-t,flush=True)
 return ds,mu,maxp,G

def minimize(ds,mu,G,H):
 fixed=ds<=H;free=~fixed;c=np.zeros(len(ds));c[fixed]=[-mu[int(d)]for d in ds[fixed]]
 b=G[np.ix_(free,fixed)]@c[fixed];a=1/ds[free];target=1-np.dot(1/ds[fixed],c[fixed])
 x=solve(G[np.ix_(free,free)],np.column_stack([b,a]),assume_a='pos')
 lam=(target+a@x[:,0])/(a@x[:,1]);c[free]=-x[:,0]+lam*x[:,1]
 return c,float(c@G@c)

if __name__=='__main__':
 import sys
 M=int(sys.argv[1])if len(sys.argv)>1 else 500;N=int(sys.argv[2])if len(sys.argv)>2 else 200000
 H=int(sys.argv[3])if len(sys.argv)>3 else 80
 ds,mu,maxp,G=gram(M,N);gcd=np.gcd(ds[:,None],ds[None,:]).astype(float)
 means=((ds[:,None]-1)*(ds[None,:]-1)/4+(gcd*gcd-1)/12)/(ds[:,None]*ds[None,:]);approxG=G+means/N
 rows=[]
 for P in sorted(set(([79,83,97,149,M] if H==80 else [317,337,499,M]))):
  ids=np.array([i for i,d in enumerate(ds)if maxp[int(d)]<=P]);d=ds[ids];g=approxG[np.ix_(ids,ids)]
  c,e=minimize(d,mu,g,H);Bp=sum(max(v,0)*(1-1/int(dd))for dd,v in zip(d,c));Bn=sum(max(-v,0)*(1-1/int(dd))for dd,v in zip(d,c))
  print('MIN H'+str(H),'M',M,'P',P,'Eapprox',e/(math.pi*math.pi/6),'B',max(Bp,Bn),'D',len(ids),flush=True)
  rows.append({'head':H,'max_conductor':M,'max_prime':P,'prefix_used':N,'numerical_approx_complete_energy':e/(math.pi*math.pi/6),'numerical_prefix_energy':float(c@G[np.ix_(ids,ids)]@c)/(math.pi*math.pi/6),'coefficient_absolute_bound':max(Bp,Bn),'coefficients':[[int(dd),float(v)]for dd,v in zip(d,c)]})
 (OUT/(f'candidates_{M}_{N}.json' if H==80 else f'candidates_{M}_{N}_H{H}.json')).write_text(json.dumps(rows,indent=2))
```

## File: complete_gram.py

<!-- FILE: complete_gram.py -->
```python
"""Complete signed Gram by pairwise LCM periodic tails (numerical discovery)."""
from explore import *
from scipy.special import polygamma
M=300;P=79;ds,mu,maxp=dictionary(M);ds=np.array([d for d in ds if maxp[int(d)]<=P]);G=np.zeros((len(ds),len(ds)));t=time.time()
for i,d in enumerate(ds):
 for j,e in enumerate(ds[:i+1]):
  ell=math.lcm(int(d),int(e));ns=np.arange(1,ell+1,dtype=np.int64)
  weights=polygamma(1,ns/ell)/ell**2
  G[i,j]=G[j,i]=np.sum((ns%d)/d*(ns%e)/e*weights)
np.savez(OUT/f'complete_gram_{M}_{P}.npz',G=G,ds=ds)
c,E=minimize(ds,mu,G,80)
result={'head':80,'max_conductor':M,'max_prime':P,'dictionary_size':len(ds),'complete_energy_numerical':E/(math.pi*math.pi/6),'seconds':time.time()-t,'coefficients':[[int(d),float(v)]for d,v in zip(ds,c)],'method':'pairwise LCM sum with full trigamma weights; numerical only'}
(OUT/'complete_gram_result.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items()if k!='coefficients'},flush=True)
```

## File: make_head80.py

<!-- FILE: make_head80.py -->
```python
from pathlib import Path
from fractions import Fraction as F
import json,math
from explore import factor
ROOT=Path(__file__).parent
row=next(x for x in json.loads((ROOT/'candidates_300_200000.json').read_text())if x['max_prime']==79)
cs={d:F(round(c*10000),10000)for d,c in row['coefficients']};pivot=min(d for d in cs if d>80);cs[pivot]=pivot*(1-sum(c/d for d,c in cs.items()if d!=pivot))
D=math.lcm(*(v.denominator for v in cs.values()));primes=[n for n in range(2,80)if factor(n)==[n]];L=math.prod(primes)
w={'period':L,'period_primes':primes,'head':80,'target':'129/128','prefix':524288,'rounding_scale':10**12,'denominator':D,'coefficients':[[d,int(c*D)]for d,c in cs.items()],'discovery':'signed prefix Gram through 200000 plus periodic-mean tail approximation; certification independent of discovery'}
(ROOT/'witness_head80.json').write_text(json.dumps(w,indent=2)+'\n')
print('period',L,'coefficients',len(cs),'denominator digits',len(str(D)))
```

## File: head320_numerical_summary.json

<!-- FILE: head320_numerical_summary.json -->
```json
[
  {
    "head": 320,
    "max_conductor": 1000,
    "max_prime": 317,
    "prefix_used": 200000,
    "numerical_approx_complete_energy": 1.0086762789393326,
    "numerical_prefix_energy": 1.0086469250542283,
    "coefficient_absolute_bound": 177.18711688224124
  },
  {
    "head": 320,
    "max_conductor": 1000,
    "max_prime": 337,
    "prefix_used": 200000,
    "numerical_approx_complete_energy": 1.008672430381253,
    "numerical_prefix_energy": 1.0086430100148485,
    "coefficient_absolute_bound": 177.92996168018573
  },
  {
    "head": 320,
    "max_conductor": 1000,
    "max_prime": 499,
    "prefix_used": 200000,
    "numerical_approx_complete_energy": 1.0085862204128038,
    "numerical_prefix_energy": 1.0085558516498974,
    "coefficient_absolute_bound": 186.5004001091158
  },
  {
    "head": 320,
    "max_conductor": 1000,
    "max_prime": 1000,
    "prefix_used": 200000,
    "numerical_approx_complete_energy": 1.0085592088927389,
    "numerical_prefix_energy": 1.0085284952694347,
    "coefficient_absolute_bound": 193.40348899772084
  },
  {
    "head": 320,
    "max_conductor": 1500,
    "max_prime": 317,
    "prefix_used": 200000,
    "numerical_approx_complete_energy": 1.0070546167463688,
    "numerical_prefix_energy": 1.0070206182004822,
    "coefficient_absolute_bound": 222.523114163847
  },
  {
    "head": 320,
    "max_conductor": 1500,
    "max_prime": 337,
    "prefix_used": 200000,
    "numerical_approx_complete_energy": 1.0070487132342436,
    "numerical_prefix_energy": 1.007014630496238,
    "coefficient_absolute_bound": 223.5671016308863
  },
  {
    "head": 320,
    "max_conductor": 1500,
    "max_prime": 499,
    "prefix_used": 200000,
    "numerical_approx_complete_energy": 1.0070020246222449,
    "numerical_prefix_energy": 1.0069677076667058,
    "coefficient_absolute_bound": 235.57283135505673
  },
  {
    "head": 320,
    "max_conductor": 1500,
    "max_prime": 1500,
    "prefix_used": 200000,
    "numerical_approx_complete_energy": 1.00696194959582,
    "numerical_prefix_energy": 1.0069265369801257,
    "coefficient_absolute_bound": 257.2475144430813
  }
]
```
