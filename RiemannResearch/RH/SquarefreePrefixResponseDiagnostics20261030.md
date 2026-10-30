# Squarefree prefix response diagnostics

Date: 30 October 2026.

Status: exploratory float64 arithmetic. No interval certification, Lean verification, or asymptotic estimate is claimed. The paper identities and open arithmetic target are in [SquarefreePrefixResponseResearch20261030.md](SquarefreePrefixResponseResearch20261030.md).

## Complete objects

The dictionary is every squarefree conductor $2\le d\le N+1$, including composites. The target is the ordinary canonical projection of the constant function in the full $Q$ inner product, not a constrained exact-head minimum-energy optimizer.

Each pairwise Gram entry is summed over a complete period $L=\operatorname{lcm}(d,e)$ using the weights

$$
w_L(r)=\frac{\psi_1(r/L)}{\zeta(2)L^2},\qquad
\widetilde w_L(r)=w_L(r)+\frac{\psi(r/L)-\psi((r+1)/L)}{\zeta(2)L},\quad 1\le r\le L.
$$

Here $w_L(r)=\sum_{j\ge0}Q(r+jL)$ and $\widetilde w_L(r)=\sum_{j\ge0}Q(r+jL)/(r+jL+1)$. The latter follows from $1/(m^2(m+1))=1/m^2-1/m+1/(m+1)$. These formulas evaluate the full Gram $G$, the multiplier matrix $M_{de}=\langle g_d,Bg_e\rangle_Q$, and the moments $\mu_d=\langle1,g_d\rangle_Q$, $\nu_d=\langle B1,g_d\rangle_Q$. The computed correction is

$$
b_N(n)=v(n)^TG^{-1}(\nu-MG^{-1}\mu).
$$

The formulas are complete infinite sums analytically; their numerical evaluation still incurs floating-point roundoff and cancellation. In particular the multiplier weights contain a subtraction, and the Gram becomes more ill-conditioned with stage.

## Recorded stages

| $N$ | Dictionary size | $\varepsilon_N$ | $\max_{1\le n\le N}\lvert b_N(n)\rvert$ | $\max_n\lvert L_N(n)\rvert$ | $\max_nJ_N(n)$ | $\max_{H<n}\lvert A_{N,n}(H)\rvert/(H+1)$ |
|---:|---:|---:|---:|---:|---:|---:|
| 20 | 13 | 0.010924075 | 0.009751819 | 0.010827263 | 0.000087828 | 0.013958488 |
| 40 | 26 | 0.008229810 | 0.018478847 | 0.019182219 | 0.000192147 | 0.015572218 |
| 80 | 49 | 0.007295689 | 0.027030305 | 0.025268087 | 0.000204164 | 0.015441969 |
| 160 | 98 | 0.006123772 | 0.037691236 | 0.038519092 | 0.000495816 | 0.018828121 |
| 240 | 149 | 0.005353393 | 0.048905541 | 0.049197541 | 0.000675948 | 0.021060193 |

Neither the maximum response nor the maximum prefix energy stabilizes in this table. The tested range is far too small to supply a uniform bound or an asymptotic rate.

## Same-sign range contributions at the largest sampled response

At $N=240$, the maximum of $|b_N(n)|$ over $1\le n\le N$ occurs at $n=221$. The lower response is approximately $-0.04919754074252445$ and the complete upper response is approximately $0.00029199951045483$.

| Lower-site range | Signed contribution |
|---|---:|
| [1, 1] | -0.006379895556 |
| [2, 3] | -0.001477322116 |
| [4, 7] | -0.017382822484 |
| [8, 15] | -0.012256073214 |
| [16, 31] | -0.007992612420 |
| [32, 63] | -0.002441793187 |
| [64, 127] | -0.001224754868 |
| [128, 220] | -0.000042266896 |

All these contributions are negative. Thus cross-range cancellation is absent in this sample, despite the exact Abel identities and the full normal equations. Other sampled sites have mixed signs; no universal sign assertion is made.

Here $J_{240}(221)\approx 0.000675948131$, and the bound $\sqrt{h_{221}J_{240}(221)}\approx 0.055042679748$ exceeds the actual lower-response magnitude. At prefix $H=110$, the two terms in the exact divisor expansion are

| Quantity | Approximate value |
|---|---:|
| $K_N(n,1)T_N(H)$ | -0.035819539785 |
| Complete floor term | 0.727792576912 |
| Their difference $A_{N,n}(H)$ | -0.763612116698 |

The floor term is subtracted. It must not be replaced by a prime-only or positive-only surrogate.

## Consistency checks

| Check | Maximum recorded error or positive violation |
|---|---:|
| Normal equation residual | 1.110e-16 |
| Lower-response Abel identity | 7.633e-17 |
| Prefix normal-equation identity | 1.325e-15 |
| Weighted Cauchy inequality | 5.294e-23 |
| Complete upper-tail inequality | 0.000e+00 |
| Two-region prefix variance inequality | 0.000e+00 |
| Individual range Abel identity | 6.939e-18 |
| Selected-prefix divisor identity | 1.388e-16 |

The largest recorded Gram condition number was approximately 85420.15. All recorded discrepancies and positive inequality violations were below $10^{-11}$. This is a consistency check, not a rigorous error enclosure. The analytical inequalities are proved on paper in the companion note; the numerical check does not prove them.

## Reproduction

Runtime packages used: NumPy 2.3.5, SciPy 1.17.0, threadpoolctl 3.6.0. Save the following code as `squarefree_prefix_flux_diagnostics.py` and run:

```sh
python squarefree_prefix_flux_diagnostics.py --stages 20 40 80 160 240
```

The output JSON includes the table, the signed range contributions at selected sites, conditioning, and consistency checks. The variable name `flux_energy` in the code denotes the paper quantity $J_N(n)$.

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


def stage(N,cache):
    start = time.monotonic()
    ds,G,H,mu,nu = cache.through(N)
    chol = la.cho_factor(G,lower=True)
    solve = lambda a: la.cho_solve(chol,a)
    a = solve(mu)
    epsilon = float(1-mu@a)
    m = np.arange(1,N+1,dtype=float)
    Q = 1/(ZETA2*m*m)
    beta = 1/(m+1)
    R = np.remainder(m[:,None],ds)/ds
    X = solve(R.T)
    K = R@X
    r = 1-R@a
    full_source = nu-H@a
    b = R@solve(full_source)
    # Rows are physical m/H, columns are evaluation sites n.
    terms = (Q*r)[:,None]*K
    A = np.cumsum(terms,axis=0)
    below = m[:,None] < m[None,:]
    direct = np.sum(np.where(below,terms*(beta[:,None]-beta[None,:]),0),axis=0)
    abel = np.sum(np.where(below,A/((m+1)*(m+2))[:,None],0),axis=0)
    flux_energy = np.sum(np.where(below,A*A/((m+1)**2*(m+2))[:,None],0),axis=0)
    harmonic = np.array([sum(1/(h+2) for h in range(1,n)) for n in range(1,N+1)])
    prefix_ratio = np.where(below,np.abs(A)/(m+1)[:,None],0)
    head_error = np.cumsum(Q*r*r)
    kernel_head = np.cumsum(Q[:,None]*K*K,axis=0)
    kernel_diag = np.diag(K)
    tail_r = np.maximum(0,epsilon-head_error)
    tail_k = np.maximum(0,kernel_diag-np.diag(kernel_head))
    upper = b-direct
    upper_bound = np.sqrt(tail_r*tail_k)/(m+1)
    variance_bound = (head_error*(epsilon-head_error)/epsilon)[:,None]*kernel_diag[None,:]
    target_normals = R.T@(Q*r)
    selected = sorted(set([int(np.argmax(np.abs(b)))+1,
                           int(np.argmax(flux_energy))+1,N]))
    selected_rows = []
    for n in selected:
        col = n-1
        shells=[]
        lo=1
        while lo<n:
            hi=min(2*lo-1,n-1)
            idx=slice(lo-1,hi)
            shell=float(np.sum(terms[idx,col]*(beta[idx]-beta[col])))
            # Explicit shell Abel formula retains both endpoints.
            right=(beta[hi-1]-beta[col])*A[hi-1,col]
            left=(beta[lo-1]-beta[col])*(A[lo-2,col] if lo>1 else 0)
            interior=sum(A[h-1,col]/((h+1)*(h+2)) for h in range(lo,hi))
            shells.append({'range':[lo,hi], 'signed_response':shell,
                           'abel_endpoint_error':float(shell-right+left-interior)})
            lo*=2
        # Expand one prefix at H=floor((n-1)/2), retaining every conductor.
        cutoff=max(1,(n-1)//2) if n>1 else 0
        T=float(np.sum(Q[:cutoff]*r[:cutoff]*m[:cutoff]))
        slope=float(np.sum(X[:,col]/ds))
        floor_part=0.0
        for j,d in enumerate(ds):
            if d<=cutoff:
                floor_part += X[j,col]*np.sum(Q[:cutoff]*r[:cutoff]*np.floor(m[:cutoff]/d))
        prefix=float(A[cutoff-1,col]) if cutoff else 0.0
        selected_rows.append({'n':n,'b':float(b[col]),'lower':float(direct[col]),
            'upper':float(upper[col]),'upper_bound':float(upper_bound[col]),
            'flux_energy':float(flux_energy[col]),'flux_Cauchy_bound':float(math.sqrt(max(0,harmonic[col]*flux_energy[col]))),
            'sum_abs_shells':sum(abs(s['signed_response']) for s in shells),
            'shells':shells,'prefix_cutoff':cutoff,'prefix_slope_term':float(T*slope),
            'prefix_floor_term':float(floor_part),'signed_prefix':prefix,
            'prefix_divisor_identity_error':float(prefix-T*slope+floor_part)})
    return {'N':N,'dimension':len(ds),'epsilon':epsilon,
        'gram_condition_number':float(np.linalg.cond(G)),
        'normal_equation_residual':float(np.max(np.abs(G@a-mu))),
        'max_abs_b':float(np.max(np.abs(b))),
        'max_abs_lower':float(np.max(np.abs(direct))),
        'max_flux_energy':float(np.max(flux_energy)),
        'max_prefix_ratio':float(np.max(prefix_ratio)),
        'max_abs_lower_over_log':float(np.max(np.abs(direct)/(6+np.log(m)))),
        'abel_identity_error':float(np.max(np.abs(direct-abel))),
        'Cauchy_inequality_violation':float(max(0,np.max(direct*direct-harmonic*flux_energy))),
        'upper_bound_violation':float(max(0,np.max(np.abs(upper)-upper_bound))),
        'prefix_variance_violation':float(max(0,np.max(A*A-variance_bound))),
        'prefix_normal_identity_error':float(np.max(np.abs(A[-1]-target_normals@X))),
        'selected_sites':selected_rows,'elapsed_seconds':time.monotonic()-start}


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--stages',type=int,nargs='+',default=[20,40,80,160,240])
    parser.add_argument('--output',default='squarefree_prefix_flux_diagnostics.json')
    args=parser.parse_args()
    out={'status':'Exploratory float64; complete Q sums; no interval or asymptotic certification','stages':[]}
    with threadpool_limits(limits=4):
        cache=CompleteGram(max(args.stages))
        for N in sorted(args.stages):
            row=stage(N,cache)
            out['stages'].append(row)
            print(json.dumps({k:v for k,v in row.items() if k!='selected_sites'}),flush=True)
            with open(args.output,'w') as f:
                json.dump(out,f,indent=2)
```
