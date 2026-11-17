# Exact affine observer diagnostics

Date: 16 November 2026. External exact rational computation, not a kernel check.
Only the cutoff-5 normal-fit data are independently replayed in Lean in
`RH/MobiusAffineDuality.lean`. No uniform conclusion is inferred.

Run the following Python source and redirect stdout to
`affine_observer_exact_data.json`. All acceptance assertions use fractions;
the decimal ratios are display-only diagnostics.

```python
from fractions import Fraction as F
import json
N = 251
mu = [1] * (N + 1)
mu[0] = 0
primes = []
for p in range(2, N + 1):
    if all(p % q for q in primes if q * q <= p):
        primes.append(p)
        for k in range(p, N + 1, p):
            mu[k] *= -1
        for k in range(p * p, N + 1, p * p):
            mu[k] = 0
rows = []
for x in [3, 5, 7, 11, 13, 17, 19, 23, 31, 53, 101, 199, 251]:
    w = [F(mu[d] ** 2, d) for d in range(1, x + 1)]
    W = sum(w)
    V = F(sum(mu[d] ** 2 for d in range(1, x + 1)), x)
    U = F(sum(d * mu[d] ** 2 for d in range(1, x + 1)), x * x)
    m0 = sum(F(mu[d], d) for d in range(1, x + 1))
    m1 = F(sum(mu[1:x + 1]), x)
    D = W * U - V * V
    a0 = (U * m0 - V * m1) / D
    a1 = (W * m1 - V * m0) / D
    loss = sum(w[d-1] * (F(mu[d]) - a0 - a1 * F(d,x)) ** 2
               for d in range(1, x + 1))
    assert loss == W - (U*m0*m0 - 2*V*m0*m1 + W*m1*m1) / D
    assert F(0) <= loss <= W
    rows.append(dict(x=x, a0=str(a0), a1=str(a1), W=str(W), sigma=str(loss),
                     sigma_over_W=str(loss/W), ratio_float_diagnostic=float(loss/W)))
print(json.dumps(dict(status="external_exact_rational; cutoff 5 is separately replayed in Lean; no asymptotic theorem",
                     stages=rows), indent=2))
```
