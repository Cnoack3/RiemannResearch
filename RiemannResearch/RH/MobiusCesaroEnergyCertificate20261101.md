# External exact rational Cesaro energy certificate

The following Python 3 program was executed successfully using `fractions.Fraction`.
It uses no third-party dependencies and certifies the full tails analytically.
This calculation is external exact arithmetic, not a Lean-checked finite certificate.
Save the code as a Python file to reproduce the assertions.

```python
"""External exact-arithmetic certificate; this is not a Lean proof.

Uses the positive-index Cesaro formula and the complete-tail estimate proved
in SquarefreeMobiusCesaroEnergy.lean. All infinite-tail bounds are explicit.
Run with Python 3; no third-party dependencies are needed.
"""
from fractions import Fraction as Q
import json


def mu_values(n):
    mu = [1] * (n + 1)
    mu[0] = 0
    prime = [True] * (n + 1)
    prime[0] = False
    if n:
        prime[1] = False
    for p in range(2, n + 1):
        if prime[p]:
            for k in range(p, n + 1, p):
                mu[k] = -mu[k]
            for k in range(p * p, n + 1, p * p):
                mu[k] = 0
            for k in range(p * p, n + 1, p):
                prime[k] = False
    return mu


def cg(d, t):
    r = t % d
    return Q(d - 1, 2 * d) - Q(r * (d - 2 - r), 2 * d * t)


def certificate(H, repairs, T):
    mu = mu_values(H)
    a = sum((Q(mu[d], d) for d in range(1, H + 1)), Q(0))
    M = sum(mu)
    assert all(d > H and mu_values(d)[d] != 0 for d in repairs)
    assert sum((c / d for d, c in repairs.items()), Q(0)) == a
    center = (sum(repairs.values()) - M) / 2
    budget = Q(sum(abs(mu[d]) * d for d in range(1, H + 1)), 8)
    budget += sum((abs(c) * d / 8 for d, c in repairs.items()), Q(0))
    total = Q(0)
    for t in range(1, T + 1):
        mean = -sum((mu[d] * cg(d, t) for d in range(1, H + 1)), Q(0))
        mean += sum((c * cg(d, t) for d, c in repairs.items()), Q(0))
        if t <= H:
            assert mean == 1
        total += Q(2, (t + 1) * (t + 2)) * mean**2
    tail_upper = Q(2, T + 2) * (abs(center) + budget / (T + 1))**2
    return total, total + tail_upper, center, budget


def main():
    H, D, E = 16, 17, 65
    mu = mu_values(H)
    a = sum((Q(mu[d], d) for d in range(1, H + 1)), Q(0))
    M = sum(mu)
    alpha = D * (E * a - M) / (E - D)
    beta = E * (M - D * a) / (E - D)
    assert alpha / D + beta / E == a
    assert alpha + beta == M
    lo, hi, center, budget = certificate(H, {D: alpha, E: beta}, 256)
    assert center == 0
    assert Q(930, 1000) < lo <= hi < Q(931, 1000)
    single_lo, single_hi, _, _ = certificate(H, {D: D * a}, 1024)
    assert Q(1002, 1000) < single_lo <= single_hi < Q(1005, 1000)
    assert hi < single_lo
    print(json.dumps({
        "verification": "Python Fraction exact rational comparisons; not Lean",
        "H": H, "D": D, "E": E, "a": str(a), "M": M,
        "alpha": str(alpha), "beta": str(beta), "budget": str(budget),
        "two_repair_certificate": "0.930 < complete energy < 0.931",
        "two_repair_lower_float": float(lo), "two_repair_upper_float": float(hi),
        "single_repair_certificate": "1.002 < complete energy < 1.005",
        "single_repair_lower_float": float(single_lo),
        "single_repair_upper_float": float(single_hi)
    }, indent=2))


if __name__ == "__main__":
    main()
```
