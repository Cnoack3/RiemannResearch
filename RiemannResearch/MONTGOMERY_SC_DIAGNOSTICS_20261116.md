# Montgomery SC finite diagnostic code

Date: 2026-11-16. This is reproducible floating-point exploration, not Lean proof evidence.

Requires Python and NumPy. Run the following code as a Python script. See
[the continuation](THEOREM_CATALOG_MONTGOMERY_SC_PROGRESS_20261116.md) for the results and limitations.

```python
"""Finite numerical diagnostics for the Montgomery SC plan; not proof evidence.

Requires NumPy. All arrays use the actual von Mangoldt function, including
proper prime powers. The integer window is n=x+2,...,x+H+1, 0 <= x < N.
"""
import json
import math
import numpy as np


def arithmetic(limit):
    prime = np.ones(limit + 1, dtype=bool)
    prime[:2] = False
    for p in range(2, math.isqrt(limit) + 1):
        if prime[p]:
            prime[p * p::p] = False
    primes = np.flatnonzero(prime)
    lam = np.zeros(limit + 1)
    for p0 in primes:
        p = int(p0)
        power = p
        while power <= limit:
            lam[power] = math.log(p)
            power *= p
    return lam, primes


def windows(values, N, H):
    prefix = np.concatenate(([0.0], np.cumsum(values)))
    start = np.arange(N) + 2
    return prefix[start + H] - prefix[start]


def divisor_model(limit, R, primes):
    mu = np.ones(R + 1, dtype=int)
    mu[0] = 0
    for p0 in primes[primes <= R]:
        p = int(p0)
        mu[p::p] *= -1
        mu[p * p::p * p] = 0
    b = np.zeros(limit + 1)
    mean = 0.0
    for d in range(1, R + 1):
        c = float(mu[d]) * math.log(R / d)
        b[d::d] += c
        mean += c / d
    b -= mean
    return b


def diagnostic(N, H, cutoffs):
    limit = max(N + H + 2, max(cutoffs))
    lam, primes = arithmetic(limit)
    a = lam - 1.0
    W = windows(a, N, H)
    V = float(np.dot(W, W))
    D = float(np.sum(windows(a * a, N, H)))
    B = 0.0
    triangle = 0.0
    prefix_errors = [0.0]
    corr_prefix = 0.0
    for h in range(1, H):
        corr = float(np.dot(a[2:N+2], a[2+h:N+2+h]))
        triangle += 2 * (H - h) * corr
        corr_prefix += corr
        prev = h * math.log(h) if h else 0.0
        prefix_errors.append(corr_prefix + N / 2 * ((h+1)*math.log(h+1)-prev))
        k = H - h - 1
        x = np.arange(k)
        delta = a[N+x+2]*a[N+x+2+h] - a[x+2]*a[x+2+h]
        B += 2 * float(np.dot(k-x, delta))
    signed_prefix = 2 * sum(prefix_errors)
    M = N * H * math.log(N / H)
    result = {
        "N": N, "H": H, "variance_ratio": V/M,
        "diagonal_error_ratio": (D-N*H*math.log(N))/M,
        "signed_prefix_ratio": signed_prefix/M,
        "boundary_ratio": B/M,
        "identity_relative_error": abs(V-M-(D-N*H*math.log(N)+signed_prefix+B))/M,
        "offdiagonal_identity_relative_error": abs(V-D-triangle-B)/M,
        "models": [],
    }
    for R in cutoffs:
        b = divisor_model(limit, R, primes)
        WB = windows(b, N, H)
        WR = W-WB
        model = float(np.dot(WB, WB))
        mixed = 2 * float(np.dot(WB, WR))
        residual = float(np.dot(WR, WR))
        result["models"].append({
            "R": R, "model_energy_ratio": model/M,
            "twice_mixed_ratio": mixed/M, "residual_energy_ratio": residual/M,
            "identity_relative_error": abs(V-model-mixed-residual)/M,
        })
    return result


if __name__ == "__main__":
    results = [diagnostic(N, H, [10, 100, 1000])
               for N, H in [(10000, 22), (100000, 46), (1000000, 100)]]
    print(json.dumps({"kind": "floating_point_diagnostic_not_proof", "results": results}, indent=2))
```
