# Signed short-head Schur diagnostics

Date: 30 October 2026.

Status: exploratory NumPy/SciPy float64 calculations; no interval certification,
asymptotic inference, or Lean verification. The paper proofs and open
arithmetic target are in [SquarefreeShortHeadSchurResearch20261030.md](SquarefreeShortHeadSchurResearch20261030.md).

The code below uses complete-period digamma/trigamma formulas for the full Q
Gram and multiplier moments, inherited from
[SquarefreePrefixResponseDiagnostics20261030.md](SquarefreePrefixResponseDiagnostics20261030.md).
It does not substitute a finite physical sum for the canonical optimizer.
Finite heads are used only for the explicitly finite source.

## Selected sites and compressed inverse bounds

These are selected sites, not claims about stage maxima.

| N | n | H | Full dimension | Compressed dimension | Signed short response | Inverse Schur norm | Proved upper constant |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 40 | 37 | 3 | 26 | 3 | 0.00111868864924 | 3.679566489 | 22.11522468 |
| 80 | 77 | 7 | 49 | 6 | -0.00674357912868 | 3.739636187 | 36.11603809 |
| 160 | 143 | 13 | 98 | 9 | -0.0132980852488 | 3.902454560 | 44.84549977 |
| 240 | 221 | 19 | 149 | 13 | -0.0426665815001 | 4.150893163 | 53.82863091 |

The upper constant is 4*zeta(2)*L_H^2, where L_H=sum_{k<=H}|mu(k)|/k.
It is a proved analytical bound in the specific normalized basis of the
paper, not an empirical fit. In each row the Schur matrix minus the finite
head Gram has positive numerically computed minimum eigenvalue. These
float64 signs are consistency checks, not certified matrix enclosures.

## Required N=240, n=221 example

All eight signed lower-range contributions are reproduced:

| Range | Signed contribution |
|---|---:|
| [1,1] | -0.00637989555610 |
| [2,3] | -0.00147732211631 |
| [4,7] | -0.01738282248365 |
| [8,15] | -0.01225607321426 |
| [16,31] | -0.00799261242043 |
| [32,63] | -0.00244179318703 |
| [64,127] | -0.00122475486832 |
| [128,220] | -0.00004226689643 |

The lower response is -0.0491975407425, the upper response
0.000291999510452, and the full response -0.0489055412321.
At H=19 the weighted divisor expansion is

    -0.0426665815001 = -0.00593172228845 - 0.0367348592116.

The floor term is subtracted. No cross-range cancellation was assumed.

For the normalized full Gram, the inverse operator norm is about
4.487674818, below the analytical constant 126.724127809.
For the 13-dimensional Schur matrix it is about 4.150893163,
below 53.828630909.

The actual inverse-Gram source energy is approximately 1.71548543318e-5.
The residual-centered multiplier variance is 1.91983142769e-5, leaving
the projection-loss square 2.04345994518e-6.
The signed interval in Proposition 3 is about [-0.38707719,0.31820642],
and its center is -0.03443538448. Its width does not establish the sign
or the required uniform response estimate.

## Moving-stage check at a fixed physical head

For stages M=160 and N=240, with n=221 and H=19 held fixed, the exact
two-stage identity gives the following exploratory values:

| Quantity | Value |
|---|---:|
| Response difference S_N-S_M | 0.01742207088198 |
| First signed term, inner(w r_N, k_N-k_M) | 0.01008901273045 |
| Subtracted term, inner(w(F_N-F_M), k_M) | -0.00733305815152 |
| Identity discrepancy | 3.47e-18 |
| General two-stage upper bound (22) | 5.053682001 |

The second term is negative before subtraction. Keeping it is essential.
The large bound demonstrates that residual energy and generic evaluation
control alone are too loose in this example.

## Reproduction

NumPy 2.3.5, SciPy 1.17.0, and threadpoolctl were used. Save the code below
as short_head_analysis.py and run python short_head_analysis.py.
It rebuilds every complete-period moment through N=240, tests the four
selected sites, and writes short_head_results.json. The two additional
checks following it reproduce the lower ranges and the moving-stage identity.

The returned matrix inequalities are diagnostic comparisons with the paper
theorems. Floating-point roundoff, moment subtraction, and conditioning remain;
no rigorous enclosure is claimed. Across the four selected sites, the largest
absolute raw/Schur response discrepancy was below 4e-16 and the largest head
residual discrepancy below 3.6e-14.

```python
#!/usr/bin/env python3
"""Actual canonical squarefree projections; complete Q Gram, float64 only.

The period formulas follow ArithmeticKernelScreeningDiagnostics20261025.md.
This computes new multiplicative-shell and normal-prefix diagnostics.
No finite physical tail is substituted for a Gram, target moment, or b_N.
"""
import argparse
import json
import math
import time
import numpy as np
import scipy.linalg as la
from scipy.special import digamma, polygamma
from threadpoolctl import threadpool_limits

ZETA2 = math.pi**2 / 6


def squarefree(n):
    return all(n % (p*p) for p in range(2, math.isqrt(n)+1))


def weights(L):
    x = np.arange(1,L+1,dtype=float)
    q = polygamma(1,x/L)/(ZETA2*L*L)
    qb = q + (digamma(x/L)-digamma((x+1)/L))/(ZETA2*L)
    return x,q,qb


class CompleteGram:
    def __init__(self, maximum):
        self.ds = np.array([d for d in range(2,maximum+2) if squarefree(d)],dtype=int)
        k = len(self.ds)
        self.G, self.H = np.zeros((k,k)),np.zeros((k,k))
        self.mu, self.nu = np.zeros(k),np.zeros(k)
        self.built = 0

    def through(self,N):
        count = int(np.searchsorted(self.ds,N+1,side='right'))
        for i in range(self.built,count):
            d = int(self.ds[i])
            x,q,qb = weights(d)
            gd = np.remainder(x,d)/d
            self.mu[i], self.nu[i] = gd@q, gd@qb
            for j in range(i+1):
                e = int(self.ds[j])
                x,q,qb = weights(math.lcm(d,e))
                both = (np.remainder(x,d)/d)*(np.remainder(x,e)/e)
                self.G[i,j] = self.G[j,i] = both@q
                self.H[i,j] = self.H[j,i] = both@qb
        self.built = count
        return (self.ds[:count],self.G[:count,:count],self.H[:count,:count],
                self.mu[:count],self.nu[:count])



"""Exploratory float64 diagnostics; full-Q Gram from complete period sums."""
import json, math
import numpy as np
import scipy.linalg as la
from threadpoolctl import threadpool_limits

Z=math.pi**2/6

def mobius(k):
    ans=1
    p=2
    while p*p<=k:
        if k%p==0:
            k//=p
            ans=-ans
            if k%p==0:
                return 0
        p+=1
    return -ans if k>1 else ans

def calculate(N,n,cache):
    ds0=cache['ds']; count=int(np.searchsorted(ds0,N+1,side='right'))
    ds=ds0[:count]; G=cache['G'][:count,:count]
    M=cache['M'][:count,:count]; mu=cache['mu'][:count]; nu=cache['nu'][:count]
    chol=la.cho_factor(G); solve=lambda z:la.cho_solve(chol,z)
    alpha=solve(mu); eps=float(1-mu@alpha)
    m=np.arange(1,n+1,dtype=float); Q=1/(Z*m*m)
    R=np.remainder(m[:,None],ds)/ds
    r=1-R@alpha; vn=R[-1]; x=solve(vn); k=R@x; knn=float(k[-1])
    b=float(vn@solve(nu-M@alpha))
    H=int(n/(6+math.log(n)))
    w=1/(m[:H]+1)-1/(n+1)
    rh=r[:H]; qh=Q[:H]; kh=k[:H]
    source=R[:H].T@(qh*w*rh)
    value=float(vn@solve(source))
    E1=float(np.sum(qh*w*rh*rh)); E2=float(np.sum(qh*w*w*rh*rh))
    V=E2-E1*E1/eps
    projected_energy=float(source@solve(source))
    loss=V-projected_energy
    diag_comp=Z*n*n-knn-r[-1]*r[-1]/eps
    center=-r[-1]*E1/eps
    radius=math.sqrt(max(0,diag_comp*loss))
    # Head-slope and low-conductor coordinates, with all high conductors
    # retained in the exact Schur complement.
    low=np.flatnonzero(ds<=H); high=np.flatnonzero(ds>H)
    d0=int(ds[high[0]]); anchor=int(high[0]); high_other=high[1:]
    J=1+len(low); T=np.zeros((count,count)); T[anchor,0]=d0
    for j,i in enumerate(low,1):
        T[i,j]=ds[i]; T[anchor,j]=-d0
    for j,i in enumerate(high_other,J):
        T[i,j]=1; T[anchor,j]=-d0/ds[i]
    Gt=T.T@G@T; mt=T.T@mu; ev=vn@T
    A=Gt[:J,:J]; C=Gt[:J,J:]; D=Gt[J:,J:]
    dc=la.cho_factor(D)
    invC=la.cho_solve(dc,C.T)
    S=A-C@invC
    psi=ev[:J]-ev[J:]@invC
    meff=mt[:J]-C@la.cho_solve(dc,mt[J:])
    rho=R[:H]@T[:,:J]
    sc=la.cho_factor(S)
    aschur=la.cho_solve(sc,meff)
    rschur=1-rho@aschur
    q=rho.T@(qh*w*rh)
    compressed=float(psi@la.cho_solve(sc,q))
    headgram=rho.T@(qh[:,None]*rho)
    LH=sum(abs(mobius(k))/k for k in range(1,H+1))
    bound=4*Z*LH*LH
    inverse_norm=1/float(la.eigvalsh(S)[0])
    full_scaled=ds[:,None]*G*ds[None,:]
    full_inverse_norm=1/float(la.eigvalsh(full_scaled)[0])
    # Full signed divisor expansion of the weighted short response.
    z0=float(np.sum(m[:H]*qh*w*rh)); slope=float(k[0]*z0)
    floor=float(sum(x[i]*np.sum(qh*w*rh*np.floor(m[:H]/d)) for i,d in enumerate(ds) if d<=H))
    lower=float(np.sum(Q[:-1]*r[:-1]*k[:-1]*(1/(m[:-1]+1)-1/(n+1))))
    upper=b-lower
    return {'N':N,'n':n,'H':H,'dimension':count,'compressed_dimension':J,
        'epsilon':eps,'r_n':float(r[-1]),'K_nn':knn,'leverage':float(Q[-1]*knn),
        'b':b,'lower':lower,'upper':upper,'short_response':value,'complement':b-value,
        'weighted_slope_term':slope,'weighted_floor_term':floor,
        'divisor_error':value-slope+floor,'schur_response':compressed,
        'schur_response_error':compressed-value,
        'schur_residual_error':float(np.max(np.abs(rschur-rh))),
        'head_source_energy':projected_energy,'variance':V,'projection_loss_square':loss,
        'variance_response_bound':math.sqrt(max(0,knn*V)),
        'source_energy_response_bound':math.sqrt(max(0,knn*projected_energy)),
        'signed_interval_center':float(center),'signed_interval_radius':radius,
        'signed_interval_lower':float(center-radius),'signed_interval_upper':float(center+radius),
        'inverse_schur_operator_norm':inverse_norm,'inverse_schur_upper_bound':bound,
        'head_gram_min_eigenvalue':float(la.eigvalsh(headgram)[0]),
        'schur_min_eigenvalue':float(la.eigvalsh(S)[0]),
        'schur_minus_head_min_eigenvalue':float(la.eigvalsh(S-headgram)[0]),
        'full_scaled_inverse_norm':full_inverse_norm,
        'full_scaled_inverse_bound':4*Z*sum(abs(mobius(k))/k for k in range(1,N+2))**2}

if __name__=='__main__':
    with threadpool_limits(limits=4):
        full=CompleteGram(240)
        ds,G,M,mu,nu=full.through(240)
        cache={'ds':ds,'G':G,'M':M,'mu':mu,'nu':nu}
        rows=[calculate(N,n,cache) for N,n in [(40,37),(80,77),(160,143),(240,221)]]
        out={'status':'Exploratory float64; no interval or Lean certification','rows':rows}
        with open('short_head_results.json','w') as f: json.dump(out,f,indent=2)
        print(json.dumps(out,indent=2))

```

The following may be appended inside the threadpool_limits block, after
the cache is constructed, to reproduce the ranges and the two-stage check:

```python
ds,G,mu=cache['ds'],cache['G'],cache['mu']
alpha=la.solve(G,mu,assume_a='pos')
n=221
m=np.arange(1,n+1,dtype=float)
R=np.remainder(m[:,None],ds)/ds
r=1-R@alpha
k=R@la.solve(G,R[-1],assume_a='pos')
Q=1/(Z*m*m)
terms=Q*r*k*(1/(m+1)-1/(n+1))
print('Lower ranges:',[
    float(np.sum(terms[a-1:min(2*a-1,n-1)]))
    for a in [1,2,4,8,16,32,64,128]])
H=19
w=1/(m[:H]+1)-1/(n+1)
M=160
j=int(np.searchsorted(ds,M+1,side='right'))
GM=G[:j,:j]
aM=la.solve(GM,mu[:j],assume_a='pos')
rM=1-R[:,:j]@aM
kM=R[:,:j]@la.solve(GM,R[-1,:j],assume_a='pos')
sN=float(np.sum(Q[:H]*w*r[:H]*k[:H]))
sM=float(np.sum(Q[:H]*w*rM[:H]*kM[:H]))
t1=float(np.sum(Q[:H]*w*r[:H]*(k-kM)[:H]))
t2=float(np.sum(Q[:H]*w*(rM-r)[:H]*kM[:H]))
epsN=1-mu@alpha
epsM=1-mu[:j]@aM
bound=(.5-1/(n+1))*(
    math.sqrt(epsN*(k[-1]-kM[-1]))
    +math.sqrt(kM[-1]*(epsM-epsN)))
print({'difference':sN-sM,'first_signed_term':t1,
       'subtracted_term':t2,'identity_error':sN-sM-t1+t2,
       'bound':bound})
```
