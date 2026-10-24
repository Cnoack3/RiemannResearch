# Reproducible exact-head certificate programs

Date: 24 October 2026. These Python programs were executed in the research session.
The complete rational outputs are the companion JSON files.

Extract the two source listings into Python files in this directory:

```sh
python - <<'EXTRACT'
import re
from pathlib import Path
s = Path("CertificatePrograms.md").read_text()
for name, body in re.findall(r"^<!-- file: ([A-Za-z0-9_]+\.py) -->\n```python\n(.*?)\n```", s, re.S | re.M):
    Path(name).write_text(body + "\n")
EXTRACT
```

Then run `python expanded_squarefree_primal_certificate.py --verify`.
Proposal generation requires NumPy and SciPy; verification uses only the standard library.

## exact_head_rational_certificates.py

<!-- file: exact_head_rational_certificates.py -->
```python
#!/usr/bin/env python3
"""Certified complete P/Q energies for squarefree Mobius exact-head families.

Only integer/Fraction arithmetic enters certificates. Decimal fields are display
approximations. Finite sums are enclosed by directed fixed-grid rounding, and
the entire infinite tail is bounded using an explicit residual amplitude.
This checks finite examples; it makes no assertion about uniform growth.
"""
import argparse
from fractions import Fraction as F
from math import gcd, isqrt
import json


def mobius(n):
    if n == 0:
        return 0
    x, count = n, 0
    p = 2
    while p * p <= x:
        if x % p == 0:
            x //= p
            count += 1
            if x % p == 0:
                return 0
            while x % p == 0:
                x //= p
        p += 1
    if x > 1:
        count += 1
    return -1 if count % 2 else 1


def next_prime(n):
    q = n + 1
    while any(q % d == 0 for d in range(2, isqrt(q) + 1)):
        q += 1
    return q


def encoded(x):
    x = F(x)
    return {"rational": f"{x.numerator}/{x.denominator}", "decimal": float(x)}


def interval(lo, hi):
    assert lo <= hi
    return {"lower": encoded(lo), "upper": encoded(hi),
            "width": encoded(hi - lo)}


def family(N, K):
    q = next_prime(N)
    mu = [mobius(d) for d in range(N + 1)]
    L = 1
    for d in range(1, N + 1):
        L = L * d // gcd(L, d)
    a = sum(mu[d] * (L // d) for d in range(1, N + 1))
    A = F(a, L)
    coefficients = {d: F(-mu[d]) for d in range(2, N + 1) if mu[d]}
    coefficients[q] = q * A
    # Exact term ranges: 0 <= g_d(n) <= (d-1)/d.
    rlo = -1 + sum(c * F(d-1, d) for d, c in coefficients.items() if c < 0)
    rhi = -1 + sum(c * F(d-1, d) for d, c in coefficients.items() if c > 0)
    U = max(abs(rlo), abs(rhi))
    # b[n] = L*(G_N(n)-1); this formula retains all signed cancellation.
    b = [L * (n - 1) - a * q * (n // q) for n in range(K + 1)]
    for d in range(2, N + 1):
        if mu[d]:
            ld = L * mu[d]
            for n in range(1, K + 1):
                b[n] += ld * (n // d)
    assert all(b[n] == 0 for n in range(1, N + 1))
    for n in {1, N, N+1, q, 2*q, K}:
        if n <= K:
            direct = -1 + sum(c * F(n % d, d) for d, c in coefficients.items())
            assert F(b[n], L) == direct
    assert all(abs(F(b[n], L)) <= U for n in range(1, K + 1))
    assert sum(c / d for d, c in coefficients.items()) == 1
    assert all(mobius(d) != 0 for d in coefficients)
    return {"N": N, "q": q, "L": L, "A": A, "U": U,
            "coefficients": coefficients, "b": b}


def zeta_two_interval(K, scale):
    total = sum(scale // (n*n) for n in range(1, K + 1))
    # Integral bounds: 1/(K+1) <= sum_{n>K} 1/n^2 <= 1/K.
    return F(total, scale) + F(1, K+1), F(total+K, scale) + F(1, K)


def rounded_bilinear(f, g, K, scale, measure):
    denominator = f["L"] * g["L"]
    total = 0
    for n in range(1, K + 1):
        weight_denominator = n * (n+1) if measure == "P" else n*n
        total += (scale * f["b"][n] * g["b"][n]) // (denominator * weight_denominator)
    finite_lo, finite_hi = F(total, scale), F(total + K, scale)
    tail = f["U"] * g["U"] / (K+1 if measure == "P" else K)
    if f is g:
        return max(F(0), finite_lo), finite_hi + tail, (finite_lo, finite_hi), (F(0), tail)
    return finite_lo-tail, finite_hi+tail, (finite_lo, finite_hi), (-tail, tail)


def divide_interval(lo, hi, zlo, zhi):
    quotients = [lo/zlo, lo/zhi, hi/zlo, hi/zhi]
    return min(quotients), max(quotients)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--heads", default="1,2,4,8,16,32,64")
    parser.add_argument("--cutoff", type=int, default=200000)
    parser.add_argument("--bits", type=int, default=96)
    parser.add_argument("--output", default="exact_head_rational_certificates.json")
    args = parser.parse_args()
    heads = [int(n) for n in args.heads.split(",")]
    assert min(heads) >= 1 and args.cutoff >= max(heads) and args.bits >= 1
    K, scale = args.cutoff, 1 << args.bits
    zlo, zhi = zeta_two_interval(K, scale)
    result = {"method": "Exact rational coefficients; directed fixed-grid finite sums; full amplitude tail bounds",
              "family": "G_N=-sum_(2<=d<=N) mu(d) g_d + q_N A_N g_(q_N), q_N=nextprime(N), A_N=sum_(d<=N) mu(d)/d",
              "cutoff": K, "rounding_denominator": str(scale), "zeta_two": interval(zlo,zhi),
              "normal_repair_cost": "Not computed: these are feasible explicit candidates, not complete-Q optimizers.",
              "families": [], "adjacent_signed_pairings": []}
    previous = None
    for N in heads:
        f = family(N, K)
        row = {"head": N, "repair_prime": f["q"], "A_N": encoded(f["A"]),
               "amplitude": encoded(f["U"]), "exact_head_checked": True,
               "squarefree_dictionary_checked": True,
               "coefficients": {str(d): encoded(c) for d,c in f["coefficients"].items()}}
        for measure in ["P", "Q_unnormalized"]:
            lo, hi, finite, tail = rounded_bilinear(f,f,K,scale,measure)
            row[measure] = {"complete": interval(lo,hi), "finite": interval(*finite), "tail": interval(*tail)}
            if measure == "Q_unnormalized":
                row["Q_complete"] = interval(*divide_interval(lo,hi,zlo,zhi))
                if N == 1:
                    qlo, qhi = divide_interval(lo,hi,zlo,zhi)
                    assert qlo <= F(1,4) <= qhi
        result["families"].append(row)
        print(N, f["q"], float(f["A"]), row["P"]["complete"]["lower"]["decimal"],
              row["P"]["complete"]["upper"]["decimal"], row["Q_complete"]["lower"]["decimal"],
              row["Q_complete"]["upper"]["decimal"])
        if previous is not None:
            pair = {"heads": [previous["N"], N]}
            for measure in ["P", "Q_unnormalized"]:
                lo, hi, finite, tail = rounded_bilinear(previous,f,K,scale,measure)
                pair[measure] = {"complete": interval(lo,hi), "finite": interval(*finite), "signed_tail": interval(*tail)}
                if measure == "Q_unnormalized":
                    pair["Q_complete"] = interval(*divide_interval(lo,hi,zlo,zhi))
            result["adjacent_signed_pairings"].append(pair)
        previous = f
    with open(args.output, "w") as out:
        json.dump(result, out, indent=2)
        out.write("\n")


if __name__ == "__main__":
    main()
```

## expanded_squarefree_primal_certificate.py

<!-- file: expanded_squarefree_primal_certificate.py -->
```python
#!/usr/bin/env python3
"""Numerically propose, then rationally certify, a larger squarefree exact head.

The output certifies the exhibited candidate's complete P and Q residuals.
It does not certify optimality or the normal repair minimum. NumPy/SciPy are
used only for proposing rational coefficients; all interval arithmetic is exact.
"""
import json
from fractions import Fraction as F
from math import lcm, log
from exact_head_rational_certificates import mobius, encoded, interval, zeta_two_interval, divide_interval


def proposal(head=64, bound=96):
    import numpy as np
    from scipy.special import digamma
    D = [d for d in range(2, bound + 1) if mobius(d)]
    H = np.empty((len(D), len(D)))
    for i, d in enumerate(D):
        for j, e in enumerate(D[:i+1]):
            p = lcm(d, e)
            n = np.arange(1, p+1, dtype=np.float64)
            mass = (digamma((n+1)/p) - digamma(n/p))/p
            H[i,j] = H[j,i] = np.dot((n % d)/d * (n % e)/e, mass)
    low = [i for i,d in enumerate(D) if d <= head]
    high = [i for i,d in enumerate(D) if d > head]
    fixed = np.array([-mobius(D[i]) for i in low],dtype=float)
    gram = H[np.ix_(high,high)]
    source = np.array([log(D[i])/D[i] for i in high]) - H[np.ix_(high,low)] @ fixed
    balance = np.array([1/D[i] for i in high])
    A = sum((F(mobius(d),d) for d in range(1,head+1)),F())
    x = np.linalg.solve(gram,source)
    direction = np.linalg.solve(gram,balance)
    x += direction * (float(A)-balance@x)/(balance@direction)
    coeff = {D[i]:F(-mobius(D[i])) for i in low}
    for i,v in zip(high[:-1],x[:-1]):
        coeff[D[i]]=F(round(float(v)*2**40),2**40)
    pivot=D[high[-1]]
    coeff[pivot]=pivot*(A-sum((coeff[D[i]]/D[i] for i in high[:-1]),F()))
    return coeff, {"gram_condition_number_unverified":float(np.linalg.cond(H)),
                   "proposed_floating_residual_unverified":float(1-2*np.array([log(d)/d for d in D])@np.array([float(coeff[d]) for d in D])+np.array([float(coeff[d]) for d in D])@H@np.array([float(coeff[d]) for d in D]))}


def certify(coeff, head=64, cutoff=400000, bits=96):
    # Sum c/d=1 and c_d=-mu(d) through the head are exact rational identities.
    assert sum((c/d for d,c in coeff.items()),F())==1
    assert all(c==F(-mobius(d)) for d,c in coeff.items() if d<=head)
    assert all(mobius(d) for d in coeff)
    den=1
    for d,c in coeff.items(): den=lcm(den,(c/d).denominator)
    numer={d:int(c/d*den) for d,c in coeff.items()}
    low=-1+sum((c*F(d-1,d) for d,c in coeff.items() if c<0),F())
    high=-1+sum((c*F(d-1,d) for d,c in coeff.items() if c>0),F())
    U=max(abs(low),abs(high))
    scale=2**bits
    p=q=0
    for n in range(1,cutoff+1):
        b=sum(a*(n%d) for d,a in numer.items())-den
        if n<=head: assert b==0
        assert abs(F(b,den))<=U
        p+=scale*b*b//(den*den*n*(n+1))
        q+=scale*b*b//(den*den*n*n)
    # Retain signed periodic means of every term in the residual square,
    # bounding only their centered Abel remainders. No whole-dictionary
    # period is enumerated. For 0<=f<=b of period L, the centered
    # partial sums are bounded by L*b, giving remainder L*b/((K+1)(K+2)).
    mean=F(1)
    abel=F()
    items=list(coeff.items())
    for d,c in items:
        bd=F(d-1,d)
        mean-=c*bd
        abel+=2*abs(c)*d*bd
    for i,(d,c) in enumerate(items):
        for j,(e,k) in enumerate(items[:i+1]):
            L=lcm(d,e)
            period_sum=sum((n%d)*(n%e) for n in range(1,L+1))
            factor=1 if i==j else 2
            mean+=factor*c*k*F(period_sum,d*e*L)
            abel+=factor*abs(c*k)*L*F((d-1)*(e-1),d*e)
    assert mean>=0
    tail_center=mean/(cutoff+1)
    tail_radius=abel/((cutoff+1)*(cutoff+2))
    tail_lo=max(F(),tail_center-tail_radius)
    tail_hi=min(U*U/(cutoff+1),tail_center+tail_radius)
    plo=F(p,scale)+tail_lo;phi=F(p+cutoff,scale)+tail_hi
    # For the unnormalized Q weight 1/n^2, the same centered-partial-sum
    # argument bounds the remainder by abel/(K+1)^2; its constant tail
    # mass is enclosed by 1/(K+1) and 1/K.
    qtail_radius=abel/(cutoff+1)**2
    qtail_lo=max(F(),mean/(cutoff+1)-qtail_radius)
    qtail_hi=min(U*U/cutoff,mean/cutoff+qtail_radius)
    qlo=F(q,scale)+qtail_lo;qhi=F(q+cutoff,scale)+qtail_hi
    zlo,zhi=zeta_two_interval(cutoff,scale)
    return {"head":head,"dictionary_size":len(coeff),"largest_conductor":max(coeff),
            "cutoff":cutoff,"rounding_denominator":str(scale),
            "coefficients":{str(d):encoded(c) for d,c in coeff.items()},
            "residual_amplitude_bound":encoded(U),"exact_head_checked":True,
            "squarefree_dictionary_checked":True,"P_complete_residual":interval(plo,phi),
            "P_signed_Abel_tail":interval(tail_lo,tail_hi),
            "P_absolute_amplitude_tail_upper":encoded(U*U/(cutoff+1)),
            "residual_period_mean_square":encoded(mean),
            "Q_complete_residual":interval(*divide_interval(qlo,qhi,zlo,zhi)),
            "Q_unnormalized_signed_Abel_tail":interval(qtail_lo,qtail_hi),
            "zeta_two":interval(zlo,zhi),
            "status":"Exact rational complete-norm certificate for exhibited candidate; NOT minimum or normal repair cost certificate"}


if __name__=='__main__':
    import argparse
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument('--verify',action='store_true')
    a.add_argument('--output',default='expanded_squarefree_primal_certificate.json')
    args=a.parse_args()
    if args.verify:
        old=json.load(open(args.output))
        coeff={int(d):F(v['rational']) for d,v in old['coefficients'].items()}
        new=certify(coeff,old['head'],old['cutoff'])
        for field in new: assert new[field]==old[field],field
        print('Complete rational P/Q primal certificate independently recomputed.')
    else:
        coeff,diagnostics=proposal()
        result=certify(coeff);result['numerical_diagnostics']=diagnostics
        with open(args.output,'w') as out: json.dump(result,out,indent=2);out.write('\n')
        print(result['P_complete_residual'])
        print(result['Q_complete_residual'])
```
