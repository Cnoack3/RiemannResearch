# Exact rational certification of the finite Green agenda

Date: 2026-11-16. Cutoffs: 5, 7, 11, 13.

These are external exact-rational certificates. Generic soundness is already
formalized in `Analysis/ParetoProgressionCertificates.lean` and
`LinearAlgebra/RationalLinearSolveCertificate.lean`; the stage endpoint
computations below have not been replayed by the Lean kernel.

Every nonterminal residue is included. Complete infinite progression weights
use 16 exact prefix terms, twelve positive logarithm terms, and lower-ten /
upper-nine signed Bernoulli corrections. Every interval operation rounds
outward to an exact rational grid with denominator 10^30. mpmath at 70 digits
only proposes centers and preconditioners. Acceptance checks the rational
Neumann row defect theta<1 and the rational preconditioned residual rho;
every actual normal solution is enclosed within rho/(1-theta) of the center.
A second optimized-energy enclosure uses the proved inverse-free normal-defect
bound with K=4 sum(d^2). Its trial energy and defect intervals involve rational
trial coefficients only; no preconditioner is used for that enclosure.
The normal solution exists by finite weighted least squares. All profile,
affine fit, energy and signed-moment intervals are then propagated outward.

The summary retains exact rational conclusion bounds, coefficients and defect
margins. Running this source recreates the full rational Gram, right-hand-side,
center and preconditioner witnesses in `green_rational_certificates.json`.
Command: `python green_rational_certificates.py 5 7 11 13`.
The finite interval calculations do not supply a cofinal or uniform estimate.

As a separate implementation check, 24 complete weight intervals at the four
periods contained independently evaluated 70-digit digamma values. That check
is numerical corroboration, not the proof of the enclosures.

```python
from fractions import Fraction as F
from math import gcd, prod
import json, time, sys
import numpy as np
import mpmath as mp

# Exact rational interval endpoints. Floating arithmetic proposes witnesses only.
mp.mp.dps = 70
S = 10**30
BERN = [F(1,6),F(-1,30),F(1,42),F(-1,30),F(5,66),F(-691,2730),
        F(7,6),F(-3617,510),F(43867,798),F(-174611,330)]
def down(q): return F(q.numerator*S//q.denominator,S)
def up(q): return -down(-q)
def rounded(lo,hi): return (down(lo),up(hi))
def pt(q): return (F(q),F(q))
def add(a,b): return rounded(a[0]+b[0],a[1]+b[1])
def sub(a,b): return rounded(a[0]-b[1],a[1]-b[0])
def mul(a,b):
    v=[x*y for x in a for y in b]
    return rounded(min(v),max(v))
def scale(q,a): return mul(pt(q),a)
def isum(xs):
    a=b=F(0)
    for x,y in xs: a+=x; b+=y
    return rounded(a,b)
def sq(a):
    l,h=a
    return rounded(0 if l<=0<=h else min(l*l,h*h),max(l*l,h*h))
def div(a,b):
    assert b[0]>0
    return mul(a,(1/b[1],1/b[0]))
def ab(a): return max(abs(a[0]),abs(a[1]))
def enc(a): return {'lo':str(a[0]),'hi':str(a[1]),'decimal_lo':float(a[0]),'decimal_hi':float(a[1])}

def weight_interval(r,P,K=16):
    # Matches Lean paretoProgressionInterval: exact prefix, 12 log terms,
    # lower ten and upper nine Bernoulli corrections, COMPLETE infinite tail.
    a=F(r+P*K); L=F(P)
    prefix=sum((F(1,(r+P*n)*(r+P*n+1)) for n in range(K)),F(0))
    z=1/(2*a+1)
    lp=sum((z**(2*j+1)/F(2*j+1) for j in range(12)),F(0))
    loglo=2*lp; loghi=2*(lp+z**25/(1-z*z))
    terms=[BERN[j]*L**(2*j+1)*(a**(-2*j-2)-(a+1)**(-2*j-2))/F(2*j+2) for j in range(10)]
    common=prefix+(1/a-1/(a+1))/2+sum(terms[:9],F(0))
    lo=common+terms[9]+loglo/L; hi=common+loghi/L
    assert lo<=hi and lo>0
    return rounded(lo,hi)

def mobius(n):
    sign=1; d=2
    while d*d<=n:
        if n%d==0:
            n//=d; sign=-sign
            if n%d==0: return 0
        d+=1
    return -sign if n>1 else sign

def stage(x):
    start=time.time()
    primes=[p for p in range(2,x+1) if all(p%d for d in range(2,int(p**.5)+1))]
    P=prod(primes)
    D=[d for d in range(x+1,P) if P%d==0]
    m=len(D); index={d:i for i,d in enumerate(D)}
    counts=[0]*m; coprime=0; rows=[]; targets=[]
    for r in range(1,P):
        g=gcd(r,P)
        if g==1: coprime+=1
        if g in index: counts[index[g]]+=1
        rows.append(counts[:]); targets.append(coprime-1)
    wi=[weight_interval(r,P) for r in range(1,P)]
    A=np.array(rows,dtype=object); y=np.array(targets,dtype=object)
    wl=np.array([int(w[0]*S) for w in wi],dtype=object)
    wh=np.array([int(w[1]*S) for w in wi],dtype=object)
    gl=A.T@(wl[:,None]*A); gh=A.T@(wh[:,None]*A)
    bl=A.T@(wl*y); bh=A.T@(wh*y)
    GI=[[(F(gl[i,j],S),F(gh[i,j],S)) for j in range(m)] for i in range(m)]
    bI=[(F(bl[i],S),F(bh[i],S)) for i in range(m)]
    def mpf(q): return mp.mpf(q.numerator)/q.denominator
    Gm=mp.matrix([[mpf(sum(GI[i][j],F(0))/2) for j in range(m)] for i in range(m)])
    bm=mp.matrix([mpf(sum(bI[i],F(0))/2) for i in range(m)])
    inv=Gm**-1; center=inv*bm
    def witness(v): return F(str(mp.nstr(v,40)))
    R=[[witness(inv[i,j]) for j in range(m)] for i in range(m)]
    c=[witness(center[i]) for i in range(m)]
    defect=[[sub(pt(int(i==j)),isum(scale(R[i][k],GI[k][j]) for k in range(m)))
              for j in range(m)] for i in range(m)]
    rb=[sub(bI[k],isum(scale(c[j],GI[k][j]) for j in range(m))) for k in range(m)]
    pre=[isum(scale(R[i][k],rb[k]) for k in range(m)) for i in range(m)]
    theta=max(sum((ab(e) for e in row),F(0)) for row in defect)
    rho=max(ab(v) for v in pre)
    assert theta<1
    eps=up(rho/(1-theta))
    ci=[rounded(v-eps,v+eps) for v in c]
    residual=[sub(pt(targets[r]),isum(scale(rows[r][j],ci[j]) for j in range(m)))
              for r in range(P-1)]
    q=isum(mul(w,sq(v)) for w,v in zip(wi,residual))
    trial_residual=[sub(pt(targets[r]),isum(scale(rows[r][j],pt(c[j])) for j in range(m)))
                    for r in range(P-1)]
    trial_q=isum(mul(w,sq(v)) for w,v in zip(wi,trial_residual))
    coercivity=4*sum(d*d for d in D)
    defect_gap=up(coercivity*sum((ab(v)**2 for v in rb),F(0)))
    q_defect=rounded(trial_q[0]-defect_gap,trial_q[1])
    assert max(q_defect[0],q[0])<=min(q_defect[1],q[1])
    tau=isum(mul(w,v) for w,v in zip(wi,residual))
    assert q[0]>0
    profiles={d:isum(scale(d*(r//d),mul(wi[r-1],residual[r-1])) for r in range(1,P))
              for d in range(1,x+1)}
    mu={d:mobius(d) for d in profiles}
    w={d:F(mu[d]**2,d) for d in profiles}
    W=sum(w.values(),F(0)); V=sum((w[d]*F(d,x) for d in profiles),F(0))
    U=sum((w[d]*F(d,x)**2 for d in profiles),F(0)); det=W*U-V*V
    assert det>0
    y0=isum(scale(w[d],profiles[d]) for d in profiles)
    y1=isum(scale(w[d]*F(d,x),profiles[d]) for d in profiles)
    c0=scale(1/det,sub(scale(U,y0),scale(V,y1)))
    c1=scale(1/det,sub(scale(W,y1),scale(V,y0)))
    fit={d:add(c0,scale(F(d,x),c1)) for d in profiles}
    ea=isum(scale(w[d],sq(sub(profiles[d],fit[d]))) for d in profiles)
    moment=isum(scale(F(mu[d],d),fit[d]) for d in profiles)
    root=isum(scale(F(mu[d],d),profiles[d]) for d in profiles)
    rootdiff=sub(root,add(q,tau)); assert rootdiff[0]<=0<=rootdiff[1]
    result={'cutoff':x,'period':P,'proper_upper_divisors':D,'prefix_K':16,
      'rational_rounding_scale':str(S),'status':'external_exact_rational_certificate',
      'theta':str(theta),'rho':str(rho),'coefficient_error_radius':str(eps),
      'q':enc(q),'q_from_normal_defect':enc(q_defect),
      'normal_defect_energy_gap_bound':str(defect_gap),
      'coercivity_constant':coercivity,'trial_energy':enc(trial_q),'affine_energy':enc(ea),'affine_c0':enc(c0),'affine_c1':enc(c1),
      'signed_moment':enc(moment),'x_E_over_q':enc(scale(x,div(ea,q))),
      'W_E_over_q':enc(scale(W,div(ea,q))),
      'moment_deficit':enc(sub(pt(1),div(moment,q))),
      'signed_root_difference':enc(rootdiff),'wall_seconds':time.time()-start,
      'coefficient_intervals':[enc(v) for v in ci],
      'rational_center':[str(v) for v in c],
      'rational_preconditioner':[[str(v) for v in row] for row in R],
      'gram_intervals':[[{'lo':str(v[0]),'hi':str(v[1])} for v in row] for row in GI],
      'rhs_intervals':[{'lo':str(v[0]),'hi':str(v[1])} for v in bI]}
    print(json.dumps({k:result[k] for k in ['cutoff','period','q','x_E_over_q','W_E_over_q','signed_moment','theta','wall_seconds']}),flush=True)
    return result

if __name__=='__main__':
    result=[stage(x) for x in map(int,sys.argv[1:])]
    with open('green_rational_certificates.json','w') as f:
        json.dump({'algorithm':'complete-period exact rational interval regression; witnesses untrusted, Neumann defect checked',
          'lean_status':'Generic enclosure and Neumann soundness theorems exist in repository; these stage endpoint computations have NOT been replayed in Lean.',
          'stages':result},f,indent=2)
```
