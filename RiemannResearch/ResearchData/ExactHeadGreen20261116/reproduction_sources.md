# Reproduction sources for the exact-head Green numerical agenda

These are external numerical programs, not Lean certificates. Save each code block under its shown filename. The C++ helper implements event summation by parts and uses extended-precision accumulators; SciPy weights and the linear solve remain floating point.

```bash
g++ -O3 -shared -fPIC profile_event.cpp -o profile_event.so
OPENBLAS_NUM_THREADS=2 python profile_diagnostics.py --cutoffs 5 7 11 13 17 19
OPENBLAS_NUM_THREADS=2 python profile_event.py --cutoffs 5 7 11 13 17 19 23
```

## profile_diagnostics.py

```python
"""Diagnostic exact-head Green regression; floating point, NOT a certificate.

Source: Best Nyman Beurling for RH.pdf, 27 July 2026, sections 8 and 13.
The full period is streamed twice. No Pareto tail is intentionally truncated.
Digamma evaluation, Gram solving and all error diagnostics are floating point.
"""
import argparse
import json
import math
import time
from pathlib import Path

import numpy as np
from scipy.linalg import solve
from scipy.special import digamma


def primes_upto(x):
    return [n for n in range(2, x + 1)
            if all(n % p for p in range(2, math.isqrt(n) + 1))]


def mobius(n):
    ans = 1
    for p in primes_upto(n):
        if n % p == 0:
            n //= p
            ans = -ans
            if n % p == 0:
                return 0
    return ans


def audit(x, chunk=16384):
    start = time.monotonic()
    primes = primes_upto(x)
    P = math.prod(primes)
    divisors = [1]
    for p in primes:
        divisors += [d * p for d in divisors]
    controls = np.array(sorted(d for d in divisors if x < d < P))
    m = len(controls)

    def blocks():
        counts = np.zeros(m)
        target_count = 0
        for lo in range(1, P, chunk):
            r = np.arange(lo, min(P, lo + chunk), dtype=np.int64)
            gcd = np.gcd(r, P)
            X = np.cumsum(gcd[:, None] == controls[None, :], axis=0, dtype=float)
            X += counts
            counts = X[-1].copy()
            target = np.cumsum(gcd == 1, dtype=float) + target_count - 1
            target_count = target[-1] + 1
            weight = (digamma((r + 1) / P) - digamma(r / P)) / P
            yield r, weight, X, target

    G = np.zeros((m, m))
    v = np.zeros(m)
    target_energy = 0.0
    for r, w, X, y in blocks():
        Z = np.sqrt(w)[:, None] * X
        G += Z.T @ Z
        v += X.T @ (w * y)
        target_energy += np.dot(w, y * y)
    scale = np.sqrt(np.diag(G))
    scaled = G / scale[:, None] / scale[None, :]
    coefficients = solve(scaled, v / scale, assume_a='pos') / scale
    d = np.arange(1, x + 1)
    mu = np.array([mobius(int(k)) for k in d])
    fit_weight = mu * mu / d
    Phi = np.stack((np.ones(x), d / x), axis=1)
    H = Phi.T @ (fit_weight[:, None] * Phi)
    q = tau = beta = 0.0
    scores = np.zeros(x)
    orthogonality = np.zeros(m)
    for r, w, X, y in blocks():
        R = y - X @ coefficients
        wr = w * R
        q += np.dot(wr, R)
        tau += wr.sum()
        beta += np.dot(wr, r)
        scores += wr @ (r[:, None] // d[None, :])
        orthogonality += X.T @ wr
    b = d * scores
    fitted = solve(H, Phi.T @ (fit_weight * b), assume_a='pos')
    canonical = np.array([beta + tau / 2, -x * tau / 2])
    ea = fit_weight * (b - Phi @ fitted) ** 2
    eg = fit_weight * (b - Phi @ canonical) ** 2
    root = float(np.dot(mu, scores))
    moment = float(np.dot(mu / d, Phi @ fitted))
    ledgers = []
    D = 1
    while D < x:
        mask = (d > D) & (d <= 2 * D)
        ledgers.append({'lower_exclusive': D, 'upper_inclusive': min(2*D,x),
                        'canonical_energy': float(eg[mask].sum()),
                        'best_affine_energy': float(ea[mask].sum())})
        D *= 2
    return dict(x=x, primorial=P, controls=m, q=q, tau=tau, beta=beta,
                root=root, root_identity_error=root-q-tau,
                terminal_weight=float((digamma(1+1/P)-digamma(1))/P),
                best_affine_coefficients=fitted.tolist(),
                canonical_coefficients=canonical.tolist(),
                E_aff=float(ea.sum()), E_green=float(eg.sum()),
                x_E_aff_over_q=float(x*ea.sum()/q),
                W_E_aff_over_q=float(fit_weight.sum()*ea.sum()/q),
                signed_moment=moment,
                scaled_gram_condition=float(np.linalg.cond(scaled)),
                affine_determinant=float(np.linalg.det(H)),
                normal_residual_max=float(np.max(np.abs(orthogonality))),
                loss_cancellation_check=float(target_energy-v@coefficients-q),
                dyadic_ledger=ledgers, seconds=time.monotonic()-start,
                status='floating_point_diagnostic_not_interval_certified')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--cutoffs', type=int, nargs='+', default=[5,7,11,13,17])
    parser.add_argument('--output', default='green_profile_diagnostics.json')
    parser.add_argument('--chunk', type=int, default=16384)
    args = parser.parse_args()
    result = []
    for x in args.cutoffs:
        entry = audit(x, args.chunk)
        result.append(entry)
        Path(args.output).write_text(json.dumps(result, indent=2)+'\n')
        print(json.dumps({k: entry[k] for k in ['x','q','E_aff','x_E_aff_over_q',
              'W_E_aff_over_q','signed_moment','root_identity_error','seconds']}), flush=True)
```

## profile_event.py

```python
"""Full-period floating-point Green audit using event summation by parts.

This is NOT interval-certified. The C++ helper changes complexity, not status.
Compare against profile_diagnostics.py to test the independent accumulation.
"""
import argparse
import ctypes
import json
import math
import time
from pathlib import Path
import numpy as np
from scipy.special import digamma
from scipy.linalg import solve
from profile_diagnostics import primes_upto, mobius

lib = ctypes.CDLL(str(Path(__file__).with_name('profile_event.so')))
dp = np.ctypeslib.ndpointer(dtype=np.float64, flags='C_CONTIGUOUS')
ip = np.ctypeslib.ndpointer(dtype=np.int32, flags='C_CONTIGUOUS')
lp = np.ctypeslib.ndpointer(dtype=np.longdouble, flags='C_CONTIGUOUS')
lib.gram_update.argtypes = [ctypes.c_int, ctypes.c_int, ip, dp, dp, lp]
lib.residual_update.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_int,
    ctypes.c_int64, ip, dp, dp, lp, lp, lp]


def audit(x, chunk=262144):
    start = time.monotonic()
    primes = primes_upto(x)
    P = math.prod(primes)
    divisors = [1]
    for p in primes:
        divisors += [d*p for d in divisors]
    keys = np.array([1]+sorted(d for d in divisors if x < d < P)+[P+1])
    m = len(keys)-1
    counts = np.zeros(m)
    B = np.zeros((m,m), dtype=np.longdouble)

    def block(lo, hi):
        r = np.arange(lo, hi, dtype=np.int64)
        gcd = np.gcd(r, P)
        ix = np.searchsorted(keys, gcd)
        ids = np.where(keys[ix] == gcd, ix, -1).astype(np.int32)
        if lo == 1:
            ids[0] = -1
        return r, ids

    for lo in range(1,P,chunk):
        r, ids = block(lo,min(lo+chunk,P))
        tail = np.ascontiguousarray((digamma(1.)-digamma(r/P))/P)
        lib.gram_update(len(r),m,ids,tail,counts,B)
    Gfull = (B+B.T).astype(float)
    G = Gfull[1:,1:]
    v = Gfull[1:,0]
    scale = np.sqrt(np.diag(G))
    scaled = G/scale[:,None]/scale[None,:]
    coefficients = solve(scaled,v/scale,assume_a='pos')/scale
    residual_coeff = np.ascontiguousarray(np.r_[1.,-coefficients])
    state = np.array([counts.astype(np.longdouble)@residual_coeff,0.,0.,0.],dtype=np.longdouble)
    normal = np.zeros(m,dtype=np.longdouble)
    scores = np.zeros(x,dtype=np.longdouble)
    gram_seconds = time.monotonic()-start
    print(json.dumps({'x':x,'phase':'Gram complete','seconds':gram_seconds}),flush=True)
    for hi in range(P,1,-chunk):
        lo = max(1,hi-chunk)
        r, ids = block(lo,hi)
        w = np.ascontiguousarray((digamma((r+1)/P)-digamma(r/P))/P)
        lib.residual_update(len(r),m,x,lo,ids,w,residual_coeff,state,normal,scores)
    residual_head_error,tau,q,beta = map(float,state)
    scores = scores.astype(float)
    d = np.arange(1,x+1)
    mu = np.array([mobius(int(k)) for k in d])
    fit_weight = mu*mu/d
    Phi = np.stack((np.ones(x),d/x),axis=1)
    H = Phi.T@(fit_weight[:,None]*Phi)
    b = d*scores
    fitted = solve(H,Phi.T@(fit_weight*b),assume_a='pos')
    canonical = np.array([beta+tau/2,-x*tau/2])
    ea = fit_weight*(b-Phi@fitted)**2
    eg = fit_weight*(b-Phi@canonical)**2
    root = float(mu@scores)
    moment = float((mu/d)@(Phi@fitted))
    ledger=[]
    D=1
    while D<x:
        mask=(d>D)&(d<=2*D)
        ledger.append({'lower_exclusive':D,'upper_inclusive':min(2*D,x),
                       'canonical_energy':float(eg[mask].sum()),
                       'best_affine_energy':float(ea[mask].sum())})
        D*=2
    return dict(x=x,primorial=P,controls=m-1,q=q,tau=tau,beta=beta,root=root,
        root_identity_error=root-q-tau,
        reconstructed_head_error=float(residual_head_error),
        terminal_weight=float((digamma(1+1/P)-digamma(1))/P),
        best_affine_coefficients=fitted.tolist(),canonical_coefficients=canonical.tolist(),
        E_aff=float(ea.sum()),E_green=float(eg.sum()),
        x_E_aff_over_q=float(x*ea.sum()/q),W_E_aff_over_q=float(fit_weight.sum()*ea.sum()/q),
        signed_moment=moment,scaled_gram_condition=float(np.linalg.cond(scaled)),
        normal_residual_max=float(np.max(np.abs(normal[1:]))),
        loss_cancellation_check=float(Gfull[0,0]-v@coefficients-q),
        dyadic_ledger=ledger,gram_seconds=gram_seconds,seconds=time.monotonic()-start,
        status='floating_point_diagnostic_not_interval_certified')


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--cutoffs',type=int,nargs='+',default=[5,7,11,13,17,19,23])
    parser.add_argument('--output',default='green_event_diagnostics.json')
    args=parser.parse_args()
    result=[]
    for x in args.cutoffs:
        entry=audit(x)
        result.append(entry)
        Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps({k:entry[k] for k in ['x','q','E_aff','x_E_aff_over_q',
            'W_E_aff_over_q','root_identity_error','seconds']}),flush=True)
```

## profile_event.cpp

```cpp
#include <cstdint>

// Summation by parts for cumulative one-hot atoms, retaining both cross terms.
extern "C" void gram_update(int n, int m, const int32_t* id,
                            const double* tail, double* count, long double* B) {
  for (int k=0; k<n; ++k) {
    int i=id[k]; if(i<0) continue;
    long double a=tail[k];
    for(int j=0;j<m;++j) B[i*m+j] += a*count[j];
    B[i*m+i] += a/2;
    count[i] += 1;
  }
}

extern "C" void residual_update(int n, int m, int x, int64_t lo,
     const int32_t* id, const double* w, const double* coef,
     long double* state, long double* normal, long double* scores) {
  // state = current residual, residual suffix, energy, first moment.
  for(int k=n-1;k>=0;--k) {
    int64_t r=lo+k;
    long double wr=w[k]*state[0];
    state[1] += wr;
    state[2] += wr*state[0];
    state[3] += wr*r;
    for(int d=1;d<=x;++d) if(r%d==0) scores[d-1] += state[1];
    int i=id[k];
    if(i>=0) { normal[i] += state[1]; state[0] -= coef[i]; }
  }
}
```

## Precision comparison

`green_event_diagnostics.json` used the same event algorithm with double accumulators. `green_event_extended_precision.json` used the retained C++ source with long-double accumulators. Digamma evaluation and Gram solving use double precision in both runs. The direct design implementation supplies the independent comparison through x=19. None of these runs supplies outward-rounded interval enclosures.
