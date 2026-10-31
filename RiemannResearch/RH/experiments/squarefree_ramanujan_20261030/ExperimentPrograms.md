# Reproducible complete-squarefree experiments

These programs accompany [the research memorandum](../../SquarefreeRamanujanCoefficientsResearch20261030.md).
Save each Python block under its indicated filename in the same directory.
The floating-point program uses NumPy and SciPy; the rational certificate uses
only the Python standard library. Run the programs with Python 3. The former
writes the coefficient data JSON and a reproducible intermediate NPZ file; the
latter writes the exact finite certificate JSON.

## squarefree_ramanujan.py

```python
"""Exploratory full-Q computations; floating-point, not Lean certificates.

Every Gram entry sums its entire period with trigamma progression masses.
No physical-tail cutoff is used. Conductors include all squarefree composites.
"""
import json, math, time
from pathlib import Path
import numpy as np
from scipy.special import polygamma
from scipy.linalg import solve, eigvalsh

OUT = Path(__file__).resolve().parent
Z2 = math.pi**2 / 6

def mobius(n):
    sign, p = 1, 2
    while p*p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
        p += 1
    return -sign if n > 1 else sign

def prime(n):
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n)+1))

def next_prime(n):
    n += 1
    while not prime(n): n += 1
    return n

def mean(d):
    r = np.arange(1, d+1, dtype=np.int64)
    w = polygamma(1, r.astype(float)/d)/(Z2*d*d)
    return np.dot(w, (r % d)/d)

def gram(d,e):
    L = math.lcm(d,e)
    r = np.arange(1,L+1,dtype=np.int64)
    w = polygamma(1,r.astype(float)/L)/(Z2*L*L)
    return np.dot(w, ((r % d)/d)*((r % e)/e))

def main():
    cuts = [2, 3, 6, 8, 16, 32, 64, 128, 256]
    largest = next_prime(max(cuts))
    ds = [d for d in range(2,largest+1) if mobius(d)]
    mus = np.array([mobius(d) for d in ds],dtype=float)
    means = np.array([mean(d) for d in ds])
    G = np.empty((len(ds),len(ds)))
    started = time.monotonic()
    for i,d in enumerate(ds):
        for j in range(i+1):
            G[i,j] = G[j,i] = gram(d,ds[j])
        if i % 20 == 0: print('Gram row',i,'/',len(ds),flush=True)
    result=[]
    coefficients={}
    for X in cuts:
        k = sum(d<=X for d in ds)
        D = np.array(ds[:k]); M = means[:k]; K = G[:k,:k]
        a = solve(K,M,assume_a='pos')
        eps = float(1-M@a)
        def err(c): return float(1-2*M@c+c@K@c)
        raw = -mus[:k]
        logw = raw * (1-np.log(D)/np.log(X))
        fejer = raw * (1-D/(X+1))
        quadratic_log = raw * (1-(np.log(D)/np.log(X))**2)
        qscale = float((M@quadratic_log)/(quadratic_log@K@quadratic_log)) if np.any(quadratic_log) else 0.0
        eta = float((M@logw)/(logw@K@logw)) if np.any(logw) else 0.0
        p = next_prime(X); kp = ds.index(p)+1
        cp=np.zeros(kp);cp[:k]=raw
        S = 1+float(np.dot(mus[:k],1/D))
        cp[-1] = p*S
        corr_err=float(1-2*means[:kp]@cp+cp@G[:kp,:kp]@cp)
        T=np.array([[float(d%q==0)/d for d in D] for q in D])
        A=T@a
        Sinv=np.array([[d*mobius(int(q//d)) if q%d==0 else 0 for q in D] for d in D],dtype=float)
        n=np.arange(1,2049,dtype=np.int64)
        vals=(n[:,None]%D[None,:])/D[None,:]
        B=vals@Sinv
        row={'cutoff':X,'dimension':k,'epsilon':eps,'raw_mobius_error':err(raw),
             'log_mobius_error':err(logw),'scaled_log_error':err(eta*logw),
             'fejer_mobius_error':err(fejer),'scaled_quadratic_log_error':err(qscale*quadratic_log),'quadratic_log_scale':qscale,'head_corrected_error':corr_err,'correction_prime':p,
             'coefficient_l1':float(np.abs(a).sum()),'min_eigenvalue':float(eigvalsh(K)[0]),
             'normal_equation_defect':float(np.max(np.abs(K@a-M))),
             'packet_transform_defect':float(np.max(np.abs(vals@a-B@A))),
             'inverse_transform_defect':float(np.max(np.abs(Sinv@T-np.eye(k))))}
        result.append(row)
        coefficients[str(X)]={'conductors':D.tolist(),'alpha':a.tolist(),'A':A.tolist()}
        print(json.dumps(row),flush=True)
    output={'method':'full-period trigamma; float64; exploratory, not rigorous interval certificates',
            'rows':result,'coefficients':coefficients,'seconds':time.monotonic()-started}
    (OUT/'squarefree_ramanujan_results.json').write_text(json.dumps(output,indent=2)+'\n')
    np.savez(OUT/'gram_data.npz',conductors=np.array(ds),means=means,gram=G)

if __name__=='__main__': main()
```

## squarefree_ramanujan_certificate.py

```python
"""Exact rational finite trial certificate. This is not a Lean certificate.

Uses the proved periodic tail upper bound: tail <= sum_period R^2/L^2.
The first period is bounded by 1/zeta(2) < 5/8 and outward dyadic rounding.
Only Python integer and Fraction arithmetic are used.
"""
from fractions import Fraction
from pathlib import Path
import json, math

conductors = [2, 3, 5, 6, 7, 10, 11, 13, 14, 15]
numerators = [99, 95, 82, -58, 69, -40, 49, 47, -35, -12]
denominator = 100
period = math.lcm(*conductors)
common = denominator * period
bits = 70
scale = 1 << bits
head_ceiling = 0
period_square_numerator = 0
for n in range(1, period + 1):
    residual_numerator = common - sum(
        b * (period // d) * (n % d)
        for b, d in zip(numerators, conductors)
    )
    square = residual_numerator ** 2
    period_square_numerator += square
    term_denominator = common**2 * n**2
    head_ceiling += (scale * square + term_denominator - 1) // term_denominator

zeta_lower = sum((Fraction(1, n*n) for n in range(1, 24)), Fraction(0))
assert zeta_lower > Fraction(8, 5)
upper = Fraction(5, 8) * Fraction(head_ceiling, scale) + Fraction(
    period_square_numerator, common**2 * period**2)
assert upper < Fraction(1, 75)
result = {
    "cutoff": 16, "conductors": conductors,
    "coefficient_numerators": numerators, "coefficient_denominator": denominator,
    "period": period, "residual_common_denominator": common,
    "dyadic_bits": bits, "head_ceiling_integer": str(head_ceiling),
    "period_square_numerator": str(period_square_numerator),
    "Q_error_upper_bound_numerator": str(upper.numerator),
    "Q_error_upper_bound_denominator": str(upper.denominator),
    "upper_bound_decimal": float(upper),
    "proved_comparison": "trial Q error < 1/75; hence epsilon_15 < 1/75",
    "verification": "exact integer/Fraction computation plus paper tail argument; not Lean checked"
}
Path(__file__).with_name('rational_trial_certificate.json').write_text(
    json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
```
