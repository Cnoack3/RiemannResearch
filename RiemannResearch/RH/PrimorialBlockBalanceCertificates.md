# Reproducible rational complete-tail certificates

This self-contained Python 3 program uses only the standard library. Save the fenced code as `PrimorialBlockBalanceCertificates.py` and run it. It reproduces `PrimorialBlockBalanceCertificates.json`; every printed decimal endpoint is rounded outwards. The proof of the variational and infinite-tail enclosures is in `QPrimorialBlockBalanceResearch20261019.md`. These host arithmetic certificates are separate from the Lean kernel checks of the general theorems.

```python
"""Exact rational enclosures of complete-Q constrained finite-stage minima.

All arithmetic used for certification is integer/Fraction arithmetic. The
printed decimal endpoints are rounded outwards. No floating point optimizer
or special-function evaluation enters a certificate.
"""
from fractions import Fraction as F
from functools import lru_cache
import json
from math import prod

SCALE = 1 << 100
PERIOD_TERMS = 256

def divisors(n):
    return [d for d in range(2, n + 1) if n % d == 0]

def mobius(n):
    result, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            result = -result
            if n % p == 0:
                return 0
        p += 1
    return -result if n > 1 else result

def round_down(q):
    return q.numerator // q.denominator

def round_up(q):
    return -((-q.numerator) // q.denominator)

@lru_cache(None)
def weights(L):
    lower, upper = [], []
    for a in range(1, L + 1):
        finite = sum(SCALE // ((a + k * L) ** 2) for k in range(PERIOD_TERMS))
        lo = finite + SCALE // (L * (a + PERIOD_TERMS * L))
        hi = finite + PERIOD_TERMS + round_up(F(SCALE, L * (a + (PERIOD_TERMS - 1) * L)))
        lower.append(lo)
        upper.append(hi)
    return lower, upper

def solve(A, b):
    n = len(b)
    M = [[F(x) for x in row] + [F(y)] for row, y in zip(A, b)]
    for i in range(n):
        assert M[i][i] > 0, 'Positive Gram pivot required'
        for j in range(i + 1, n):
            t = M[j][i] / M[i][i]
            for k in range(i + 1, n + 1):
                M[j][k] -= t * M[i][k]
            M[j][i] = F(0)
    x = [F(0)] * n
    for i in reversed(range(n)):
        x[i] = (M[i][-1] - sum(M[i][j] * x[j] for j in range(i + 1, n))) / M[i][i]
    return x

def constrained_minimum(H, L, w):
    D = divisors(L)
    assert mobius(L) != 0, 'Use a squarefree period'
    assert all(L % d == 0 for d in range(2, H + 1) if mobius(d))
    free = [d for d in D if d > H]
    assert free, 'No normalization anchor'
    r = free[0]
    assert H < r <= 2 * max(1, H), 'Nearby divisor anchor required'
    fixed = {d: F(-mobius(d), d) for d in D if d <= H}
    anchor_a = 1 - sum(fixed.values())
    columns = free[1:]
    # Use integer residue columns; a_d=c_d/d and sum a_d=1.
    denominator = prod(range(1, H + 1))
    rows, residuals = [], []
    for n in range(1, L + 1):
        f0 = sum(a * (n % d) for d, a in fixed.items()) + anchor_a * (n % r)
        residual = 1 - f0
        assert (residual * denominator).denominator == 1
        residuals.append(int(residual * denominator))
        rows.append([n % d - n % r for d in columns])
    size = len(columns)
    A = [[sum(wt * row[i] * row[j] for wt, row in zip(w, rows))
          for j in range(size)] for i in range(size)]
    b = [sum(wt * row[i] * z for wt, row, z in zip(w, rows, residuals))
         for i in range(size)]
    x = solve(A, b)
    assert all(sum(F(A[i][j]) * x[j] for j in range(size)) == b[i] for i in range(size))
    constant = sum(wt * z * z for wt, z in zip(w, residuals))
    minimum = (F(constant) - sum(F(v) * t for v, t in zip(b, x))) / (denominator ** 2 * SCALE)
    coeff = dict(fixed)
    coeff[r] = anchor_a - F(sum(x)) / denominator
    coeff.update({d: t / denominator for d, t in zip(columns, x)})
    assert all(sum(a * (n % d) for d, a in coeff.items()) == 1 for n in range(1, H + 1))
    return minimum, coeff, r

@lru_cache(None)
def raw_bounds(H, L):
    wl, wu = weights(L)
    lo, _, _ = constrained_minimum(H, L, wl)
    hi, _, _ = constrained_minimum(H, L, wu)
    assert 0 <= lo <= hi
    return lo, hi

def zeta_bounds(K=4096):
    finite = sum(SCALE // (n * n) for n in range(1, K + 1))
    return F(finite, SCALE) + F(1, K + 1), F(finite + K, SCALE) + F(1, K)

ZL, ZU = zeta_bounds()

@lru_cache(None)
def bounds(H, L):
    lo, hi = raw_bounds(H, L)
    return lo / ZU, hi / ZL

def diff(x, y):
    return x[0] - y[1], x[1] - y[0]

def display(interval, places=9):
    unit = 10 ** places
    lo, hi = interval
    def dec(integer):
        sign = '-' if integer < 0 else ''
        integer = abs(integer)
        return sign + str(integer // unit) + '.' + str(integer % unit).zfill(places)
    return [dec(round_down(lo * unit)), dec(round_up(hi * unit))]

def main():
    assert bounds(1, 2)[0] <= F(1, 4) <= bounds(1, 2)[1]
    stages = [(1, 6), (2, 6), (3, 6), (4, 6), (5, 30), (6, 30),
              (7, 210), (8, 210), (9, 210), (10, 210), (11, 2310), (12, 2310)]
    result = {'method': 'exact rational variational enclosures with integral progression tails',
              'scale_bits': 100, 'terms_per_progression': PERIOD_TERMS,
              'zeta_interval': display((ZL, ZU), 12), 'stages': []}
    for i, (H, L) in enumerate(stages):
        row = {'head': H, 'period': L, 'energy': display(bounds(H, L))}
        if i:
            oldH, oldL = stages[i - 1]
            oldE, refitE, newE = bounds(oldH, oldL), bounds(oldH, L), bounds(H, L)
            row['period_gain'] = display(diff(oldE, refitE)) if L != oldL else ['0', '0']
            row['head_cost'] = display(diff(newE, refitE)) if mobius(H) else ['0', '0']
            row['signed_balance_from_start'] = display(diff(newE, bounds(*stages[0])))
            # Check the head cost against a certified LOWER bound on the RHS
            # of the near-anchor inequality, using the upper-weight minimizer.
            _, c, anchor = constrained_minimum(oldH, L, weights(L)[1])
            delta = 1 - sum(a * (H % d) for d, a in c.items())
            gap = raw_bounds(oldH, L)[1] - raw_bounds(oldH, L)[0]
            # Any rational radius above H sqrt(gap) is certified by squaring.
            radius = F(1, 10**7)
            while radius * radius < H * H * gap:
                radius *= 2
            delta_abs_lower = max(F(0), abs(delta) - radius)
            rhs_lower = 4 * delta_abs_lower ** 2 / (ZU * (H - 1))
            row['delta_enclosure_radius'] = str(radius)
            row['near_anchor'] = next(d for d in divisors(L) if d > H)
            row['near_anchor_inequality_certified_by_intervals'] = (
                diff(newE, refitE)[1] <= rhs_lower if mobius(H) else True)
            assert row['near_anchor_inequality_certified_by_intervals']
            if not mobius(H):
                assert raw_bounds(H, L) == raw_bounds(oldH, L)
        result['stages'].append(row)
        print(json.dumps(row), flush=True)
    with open('PrimorialBlockBalanceCertificates.json', 'w') as f:
        json.dump(result, f, indent=2)

if __name__ == '__main__':
    main()
```
