# Exact-rational centered-moment probe certificates

Date: 2026-11-16. Cutoffs: 5, 7, 11, 13.

Status: external exact-rational certificates. The generic observation identity
and deficit implication are proved in `RH/ExactHeadAtomMoment.lean`.
These individual endpoint computations have not been replayed in Lean.

For alpha=1/2, each record gives rational proper-upper-divisor coefficients v
and encloses the complete weighted energy of psi_x-alpha*C_P-v.
Every nonterminal residue and every infinite progression tail is included.
The complete weight intervals are the same proved formulas reproduced in
`rational_certification_sources.md`. Their endpoints and every final
sum are exact rationals. The previously proposed inverse supplies only a
trial correction: acceptance checks that correction's actual energy directly.
It does not assume the inverse is accurate or that the correction is optimal.

| x | P | Conservative upper bound |
|---|---:|---:|
| 5 | 30 | 0.628954 |
| 7 | 210 | 0.510332 |
| 11 | 2310 | 0.365700 |
| 13 | 30030 | 0.364855 |

The exact upper endpoints are all below 2/3. This suggests the finite
falsification target alpha=1/2, M=2/3 for the centered-probe route.
With eps=1/4 the proved implication would give m <= (3/4)q+2/3.
A uniform or cofinal M bound is **not** established.

## Reproduction

Extract the Python block in `rational_certification_sources.md` as
`green_rational_certificates.py`, and run it with arguments `5 7 11 13`.
That regenerates the full `green_rational_certificates.json`, including
the rational preconditioners omitted from the compact summary file.
Save the block below as `green_moment_probe_certificates.py` in the same
directory and run it. The generated JSON retains every trial coefficient,
exact energy endpoints, and source hashes.

```python
from pathlib import Path
from fractions import Fraction as F
from math import gcd, lcm
import json, time, hashlib
import numpy as np
from green_rational_certificates import weight_interval, mobius, S, enc

# Only rational trial upper-span corrections are accepted. The previously
# proposed inverse supplies a trial vector; acceptance uses its complete energy.
root=Path(__file__).resolve().parent
records=json.loads((root/'green_rational_certificates.json').read_text())['stages']
out=[]
for rec in records:
    start=time.time(); x=rec['cutoff']; P=rec['period']
    D=rec['proper_upper_divisors']; index={d:i for i,d in enumerate(D)}
    assert P=={5:30,7:210,11:2310,13:30030}[x]
    assert D==[d for d in range(x+1,P) if P%d==0]
    w={d:F(mobius(d)**2,d) for d in range(1,x+1)}
    t={d:F(d,x) for d in w}; a={d:F(mobius(d),d) for d in w}
    W=sum(w.values(),F(0)); V=sum((w[d]*t[d] for d in w),F(0))
    U=sum((w[d]*t[d]**2 for d in w),F(0))
    m0=sum(a.values(),F(0)); m1=sum((a[d]*t[d] for d in w),F(0))
    det=W*U-V*V; assert det>0
    lam={d:w[d]*((U*m0-V*m1)+(W*m1-V*m0)*t[d])/det for d in w}
    alpha=F(1,2); den=lcm(2,*[(lam[d]*d).denominator for d in w])
    lc={d:int(den*lam[d]*d) for d in w}
    counts=[0]*len(D); coprime=0; rows=[]; fnums=[]
    for r in range(1,P):
        g=gcd(r,P)
        if g==1: coprime+=1
        if g in index: counts[index[g]]+=1
        rows.append(counts[:])
        fnums.append(sum(lc[d]*(r//d) for d in w)-int(alpha*den)*(coprime-1))
    A=np.array(rows,dtype=object); fv=np.array(fnums,dtype=object)
    wi=[weight_interval(r,P) for r in range(1,P)]
    wl=np.array([int(lo*S) for lo,hi in wi],dtype=object)
    wh=np.array([int(hi*S) for lo,hi in wi],dtype=object)
    rhs=A.T@((wl+wh)*fv)
    b=[F(int(v),2*S*den) for v in rhs]
    R=[[F(v) for v in row] for row in rec['rational_preconditioner']]
    Z=10**20
    znums=[round(sum((R[i][j]*b[j] for j in range(len(D))),F(0))*Z)
           for i in range(len(D))]
    residual=fv*Z-den*(A@np.array(znums,dtype=object))
    squares=residual*residual
    denom=S*(den*Z)**2
    energy=(F(int(wl@squares),denom),F(int(wh@squares),denom))
    assert 0<=energy[0]<=energy[1]<=F(2,3)
    item={'cutoff':x,'period':P,'alpha':str(alpha),'proper_upper_divisors':D,
          'upper_span_coefficients':[str(F(z,Z)) for z in znums],
          'centered_probe_energy':enc(energy),'seconds':time.time()-start,
          'status':'external_exact_rational_certificate_not_kernel_replayed'}
    out.append(item)
    print(json.dumps({'cutoff':x,'energy_lo':float(energy[0]),
                      'energy_hi':float(energy[1]),'seconds':item['seconds']}),flush=True)
result={'definition':'energy of fittedMomentProbe x - (1/2)*target P - upper atom synthesis',
        'scope':'All nonterminal residues and complete infinite progression weights.',
        'finite_candidate_M':'2/3','finite_candidate_alpha':'1/2',
        'weights_source_sha256':hashlib.sha256((root/'green_rational_certificates.py').read_bytes()).hexdigest(),
        'uniform_status':'Finite stages only; no cofinal or uniform bound is proved.',
        'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'stages':out}
(root/'green_moment_probe_certificates.json').write_text(json.dumps(result,indent=2)+'\n')
```
