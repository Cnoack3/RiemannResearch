# Complete Q endpoint-source diagnostics

Prepared 30 October 2026. **Exploratory floating point, not interval certified and not a Lean certificate.**

The full-period Gram construction and moving-optimizer solver are adapted from
[ScreenedMixedDiagnostics20261030.md](ScreenedMixedDiagnostics20261030.md) at
commit 3457cc758849b09d33ea428b64f087897d274e2b. Every squarefree divisor is retained;
trigamma period weights include the whole infinite physical tail.
The added calculation checks the signed band pairing, endpoint distance, and
squarefree-band dual difference energy derived in
[SignedDyadicArithmeticResearch20261030.md](SignedDyadicArithmeticResearch20261030.md).

## Reproducible source

Requires Python, NumPy, SciPy, and threadpoolctl. No asymptotic conclusion follows
from these three finite blocks.

```python
#!/usr/bin/env python3
"""Exploratory complete-Q full-squarefree trial diagnostics (not certified).

Periods are summed exactly in form via trigamma weights, then evaluated in float64.
Every divisor d>1 of primorial(2*i+2) is retained. The actual finite-dimensional
optimizer has head 1 through i+1. All physical tail coordinates enter the Gram.

The matrix construction streams period rows to limit memory. No truncated tail is
used. Floating-point energies, conditioning and head residuals are diagnostics,
not certified inequalities or asymptotic evidence.
"""
import json
from functools import lru_cache
from math import prod
import numpy as np
import scipy.linalg as la
from scipy.special import polygamma, zeta
from threadpoolctl import threadpool_limits

ZETA2 = float(zeta(2))
PRIMES = [2,3,5,7,11,13,17]
CHUNK = 8192


def divisors(L):
    return np.array([d for d in range(2,L+1) if L % d == 0], dtype=np.int64)


def rows(n, ds):
    return np.remainder(n[:,None],ds[None,:])/ds[None,:]


def weights(n, L):
    return polygamma(1,n/L)/(ZETA2*L*L)


@lru_cache(None)
def period_data(L):
    ds=divisors(L)
    G=np.zeros((len(ds),len(ds)))
    for begin in range(1,L+1,CHUNK):
        n=np.arange(begin,min(L+1,begin+CHUNK))
        X=rows(n,ds); w=weights(n,L)
        G += X.T@(w[:,None]*X)
    G=(G+G.T)/2
    return ds,G


@lru_cache(None)
def optimizer(L,H):
    ds,G=period_data(L)
    Ahead=rows(np.arange(1,H+1),ds)
    c0=la.lstsq(Ahead,np.ones(H),cond=1e-12)[0]
    N=la.null_space(Ahead,rcond=1e-12)
    if N.shape[1]:
        TG=N.T@G@N
        c=c0-N@la.solve(TG,N.T@G@c0,assume_a='pos')
    else:
        c=c0
    return c,N,float(c@G@c),float(np.max(np.abs(Ahead@c-1)))


def primorial(cutoff):
    return prod(p for p in PRIMES if p<=cutoff)


def squarefree(n):
    return all(n%(p*p) for p in PRIMES if p*p<=n)


def trial_gain(abar,B,C,u,v):
    det=abar*C-B*B
    alpha=(C*u-B*v)/det
    beta=(abar*v-B*u)/det
    gain=(C*u*u-2*B*u*v+abar*v*v)/det
    return float(gain),float(alpha),float(beta),float(det)


def stage(i):
    L=primorial(2*i+2); Lnew=primorial(2*i+4); H=i+1; p=2*i+3
    ds,G=period_data(L)
    cf,_,E,ef=optimizer(L,H)
    ch,N,Ehat,eh=optimizer(L,H+1)
    cn,_,En,en=optimizer(Lnew,H+1)
    result={'i':i,'head':H,'p':p,'old_period':L,'new_period':Lnew,
       'old_dictionary_dimension':len(ds),'new_dictionary_dimension':len(cn),
       'E':E,'Ehat':Ehat,'Enext':En,'old_head_cost':Ehat-E,
       'actual_full_gain':Ehat-En,'actual_increment':En-E,
       'new_observation_squarefree':squarefree(i+2),
       'max_head_residual':max(ef,eh,en)}
    if L==Lnew:
        result.update({k:En-E for k in ['raw_refined_certificate','screened_certificate',
            'mixed_certificate','mixed_regularized_screened_certificate',
            'mixed_regularized_upper_certificate']})
        return result
    # All needed pairings in the common period; old tangent uses the same Gold.
    cross_x=np.zeros(len(ds)); cross_q=np.zeros(len(ds))
    rawA=rawB=rawC=0.0
    for begin in range(1,Lnew+1,CHUNK):
        n=np.arange(begin,min(Lnew+1,begin+CHUNK)); w=weights(n,Lnew)
        X=rows(n,ds)
        raw=rows(n//p,ds)@cf
        prime=(n%p)/p-(L/p)*((n%L)/L)
        cross_x += X.T@(w*raw); cross_q += X.T@(w*prime)
        rawA += np.dot(w*raw,raw); rawB += np.dot(w*raw,prime); rawC += np.dot(w*prime,prime)
    vx=N.T@cross_x; vq=N.T@cross_q
    if N.shape[1]:
        TG=N.T@G@N
        px=la.solve(TG,vx,assume_a='pos'); pq=la.solve(TG,vq,assume_a='pos')
        screenA=float(vx@px); screenB=float(vx@pq); screenC=float(vq@pq)
    else:
        screenA=screenB=screenC=0.0
    A=float(rawA-screenA); B=float(rawB-screenB); C=float(rawC-screenC)
    u=float(ch@cross_x); v=float(ch@cross_q)
    D=sum(1/(ZETA2*k*k*p)-sum(1/(ZETA2*(p*k+r)**2) for r in range(p)) for k in range(1,H+1))
    A0=E/p-D
    tau=A0/1000  # Same explicit positive regularizer for both variants.
    gm,am,bm,dm=trial_gain(A,B,C,u,v)
    gs,ass,bss,dss=trial_gain(A+tau,B,C,u,v)
    gu,au,bu,du=trial_gain(A0+tau,B,C,u,v)
    result.update({'raw_norm_sq':float(rawA),'screening_energy':screenA,
      'screened_norm_sq':A,'screened_norm_ratio':A/rawA,'prime_norm_sq':C,
      'mixed_gram_entry':B,'self_source':u,'prime_source':v,'head_defect':D,
      'tail_defect':A0-rawA,'A0':A0,'tau':tau,'mixed_determinant':dm,
      'raw_refined_gain':u*u/A0,'raw_exact_gain':u*u/rawA,
      'screened_gain':u*u/A,'prime_gain':v*v/C,
      'mixed_exact_gain':gm,
      'mixed_regularized_screened_guaranteed_gain':gs,
      'mixed_regularized_screened_realized_gain':gs+tau*ass*ass,
      'mixed_regularized_upper_guaranteed_gain':gu,
      'mixed_regularized_upper_realized_gain':gu+(A0+tau-A)*au*au,
      'mixed_coefficients':[am,bm],
      'regularized_screened_coefficients':[ass,bss],
      'regularized_upper_coefficients':[au,bu],
      'raw_refined_certificate':Ehat-E-u*u/A0,
      'screened_certificate':Ehat-E-u*u/A,
      'mixed_certificate':Ehat-E-gm,
      'mixed_regularized_screened_certificate':Ehat-E-gs,
      'mixed_regularized_upper_certificate':Ehat-E-gu,
      'mixed_loss':Ehat-En-gm,
      'regularized_screened_loss':Ehat-En-(gs+tau*ass*ass),
      'regularized_upper_loss':Ehat-En-(gu+(A0+tau-A)*au*au),
      'old_gram_condition_number':float(np.linalg.cond(G)),
      'new_gram_condition_number':float(np.linalg.cond(period_data(Lnew)[1]))})
    return result


def main():
    with threadpool_limits(limits=4):
        stages=[stage(i) for i in range(1,8)]
        keys=['actual_increment','raw_refined_certificate','screened_certificate',
              'mixed_certificate','mixed_regularized_screened_certificate',
              'mixed_regularized_upper_certificate']
        blocks=[]
        for lo,hi in [(1,2),(2,4),(4,8)]:
            sub=[r for r in stages if lo<=r['i']<hi]
            row={'interval':[lo,hi]}
            row.update({k:sum(r[k] for r in sub) for k in keys})
            # Existing global adjusted certificates use the exact negative gain
            # at nonsquarefree observation sites; distinguish from raw trial bounds.
            for key in keys[1:]:
                row['global_adjusted_'+key]=sum(r[key] if r['new_observation_squarefree'] else r['actual_increment'] for r in sub)
            blocks.append(row)
        result={'classification':'Exploratory float64; complete periodic Q norm; not interval-certified',
                'regularizer':'tau=A0/1000 at each prime stage',
                'stages':stages,'dyadic_blocks':blocks}
        print(json.dumps(result,indent=2))


# Continuation: endpoint normal-equation diagnostics. Source formulas are
# independently derived; numerical values are exploratory, not interval proofs.
def mu_sf(d):
    return (-1)**sum(d%p==0 for p in PRIMES)

def endpoint_diagnostics():
    output=[]
    with threadpool_limits(limits=4):
        stages={i:stage(i) for i in range(1,8)}
        for M,N in [(1,2),(2,4),(4,8)]:
            LM,LN=primorial(2*M+2),primorial(2*N+2)
            dsM,GM=period_data(LM); ds,G=period_data(LN)
            ca,_,EA,_=optimizer(LM,M+1); cb,_,EB,_=optimizer(LN,N+1)
            a=np.zeros(len(ds)); a[np.searchsorted(ds,dsM)]=ca
            kappa=LN*(G@cb)[-1]
            eta=G@cb-kappa/ds
            band=(ds>M+1)&(ds<=N+1)
            vals=-(a[band]+np.array([mu_sf(int(d)) for d in ds[band]]))*eta[band]
            pairing=float(vals.sum())
            dist=float((cb-a)@G@(cb-a))
            cert=sum(stages[i]['mixed_certificate'] if squarefree(i+2)
                     else stages[i]['actual_increment'] for i in range(M,N))
            losses=cert-(EB-EA)
            output.append({'interval':[M,N], 'energy_initial':EA,'energy_final':EB,
                'dual_pairing':pairing,'endpoint_distance_squared':dist,
                'twice_pairing_minus_distance':2*pairing-dist,
                'energy_increment':EB-EA,'mixed_certificate':cert,'full_loss_sum':losses,
                'identity_error':2*pairing-dist-(EB-EA),
                'tail_normal_residual':float(np.max(np.abs(eta[ds>N+1]))),
                'band_contributions':[[int(d),float(v)] for d,v in zip(ds[band],vals)],
                'band_sources':[[int(d),float(v)] for d,v in zip(ds[band],eta[band])],
                'band_defects':[[int(d),float(v)] for d,v in zip(ds[band],a[band]+np.array([mu_sf(int(d)) for d in ds[band]]))],
                'band_dual_energy':sum(float((eta[band][j+1] if j+1<sum(band) else 0)-eta[band][j])**2 /
                    sum(1/(ZETA2*n*n) for n in range(int(ds[band][j]), int(ds[band][j+1]) if j+1<sum(band) else N+2))
                    for j in range(sum(band)))})
    for q in output:
        M,N=q['interval']
        points=[d for d,v in q['band_sources']]
        eta=[v for d,v in q['band_sources']]
        defects=[v for d,v in q['band_defects']]
        z=head=completion=0.0
        for j,d in enumerate(points):
            stop=points[j+1] if j+1<len(points) else N+2
            w=sum(1/(ZETA2*n*n) for n in range(d,stop))
            gamma=(eta[j+1] if j+1<len(points) else 0)-eta[j]
            z+=defects[j]
            head+=w*z*z
            completion+=w*(z-gamma/w)**2
        q['head_completion_square']=completion
        q['endpoint_tail_distance_squared']=q['endpoint_distance_squared']-head
        q['dual_completion_error']=q['band_dual_energy']-completion-q['endpoint_tail_distance_squared']-q['energy_increment']
    print(json.dumps({'classification':'Exploratory float64, complete Q norm, not rigorous bounds',
                      'endpoint_blocks':output},indent=2))
if __name__=='__main__':
    endpoint_diagnostics()

```

## Exploratory output

```json
{
  "classification": "Exploratory float64, complete Q norm, not rigorous bounds",
  "endpoint_blocks": [
    {
      "interval": [
        1,
        2
      ],
      "energy_initial": 0.8293945844066188,
      "energy_final": 0.896382777761702,
      "dual_pairing": 0.1359777666501851,
      "endpoint_distance_squared": 0.20496733994528685,
      "twice_pairing_minus_distance": 0.06698819335508335,
      "energy_increment": 0.06698819335508321,
      "mixed_certificate": 0.08786075488745468,
      "full_loss_sum": 0.020872561532371464,
      "identity_error": 1.3877787807814457e-16,
      "tail_normal_residual": 1.1102230246251565e-16,
      "band_contributions": [
        [
          3,
          0.1359777666501851
        ]
      ],
      "band_sources": [
        [
          3,
          -0.11213563405316823
        ]
      ],
      "band_defects": [
        [
          3,
          1.2126186987600418
        ]
      ],
      "band_dual_energy": 0.1861565366561474,
      "head_completion_square": 0.01352576173009778,
      "endpoint_tail_distance_squared": 0.10564258157096627,
      "dual_completion_error": 1.249000902703301e-16
    },
    {
      "interval": [
        2,
        4
      ],
      "energy_initial": 0.896382777761702,
      "energy_final": 0.9031263949319254,
      "dual_pairing": 0.02081160370464689,
      "endpoint_distance_squared": 0.034879590239071126,
      "twice_pairing_minus_distance": 0.006743617170222656,
      "energy_increment": 0.006743617170223315,
      "mixed_certificate": 0.006743617170223315,
      "full_loss_sum": 0.0,
      "identity_error": -6.591949208711867e-16,
      "tail_normal_residual": 2.7755575615628914e-16,
      "band_contributions": [
        [
          5,
          0.02081160370464689
        ]
      ],
      "band_sources": [
        [
          5,
          -0.024071990496159934
        ]
      ],
      "band_defects": [
        [
          5,
          0.864556826240308
        ]
      ],
      "band_dual_energy": 0.02382936723334109,
      "head_completion_square": 0.00038217115150145054,
      "endpoint_tail_distance_squared": 0.01670357891161699,
      "dual_completion_error": -6.661338147750939e-16
    },
    {
      "interval": [
        4,
        8
      ],
      "energy_initial": 0.9031263949319254,
      "energy_final": 0.9449542432997429,
      "dual_pairing": 0.04880771619918433,
      "endpoint_distance_squared": 0.055787584030541966,
      "twice_pairing_minus_distance": 0.041827848367826694,
      "energy_increment": 0.0418278483678175,
      "mixed_certificate": 0.0426718896589975,
      "full_loss_sum": 0.0008440412911800005,
      "identity_error": 9.194034422677078e-15,
      "tail_normal_residual": 2.4980018054066022e-15,
      "band_contributions": [
        [
          6,
          0.049708987839755
        ],
        [
          7,
          -0.0009012716405706699
        ]
      ],
      "band_sources": [
        [
          6,
          -0.04983700945813971
        ],
        [
          7,
          -0.029537619204826726
        ]
      ],
      "band_defects": [
        [
          6,
          0.9974311938100491
        ],
        [
          7,
          -0.030512670446485868
        ]
      ],
      "band_dual_energy": 0.054066501508585156,
      "head_completion_square": 0.000748376414249103,
      "endpoint_tail_distance_squared": 0.011490276726509367,
      "dual_completion_error": 9.18709552877317e-15
    }
  ]
}
```
