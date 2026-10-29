# Exact integer check of two H=320 repairs

This reproducibility appendix contains the standalone Python 3 checker used in the accompanying research memorandum. It uses only the standard library. Save the fenced code as `ExactHeadRepair320Check20261029.py` and run it with Python 3.

Status: externally executed exact integer arithmetic, not a Lean numerical proof. Both specified candidates satisfy the head and fail the energy target; this does not rule out other H=320 witnesses.

```python
"""Exact external check: repairing the H=80 support through 300 to H=320.

This tests the specified repair choice p=331. It is not a Lean proof and
does not rule out other H=320 witnesses.
"""
from fractions import Fraction
from math import prod

H, p, K, S = 320, 331, 2048, 10**12
mu = [1] * (H + 1)
mu[0] = 0
primes = []
for k in range(2, H + 1):
    if all(k % q for q in primes if q * q <= k):
        primes.append(k)
for q in primes:
    for k in range(q, H + 1, q):
        mu[k] *= -1
    for k in range(q * q, H + 1, q * q):
        mu[k] = 0
assert all(p % q for q in primes if q * q <= p)
assert H < p < 2 * H

# Every original H=80 conductor is at most 300, so repair to H=320
# replaces all its coefficients by -mu(d); only the prime correction
# survives above the new head. This candidate is independent of the
# original coefficient values.
T = prod(primes)
head_mobius_slope = sum((Fraction(mu[d], d) for d in range(1, H + 1)), Fraction())
scaled = {d: -mu[d] * (T // d) for d in range(2, H + 1) if mu[d]}
scaled[p] = int(T * head_mobius_slope)
assert T * head_mobius_slope == scaled[p]
assert sum(scaled.values()) == T

P = 0
lower_integer_total = 0
for n in range(1, K + 1):
    P += T - sum(d * a for d, a in scaled.items() if n % d == 0)
    # An independent direct evaluation checks every recurrence value.
    assert P == sum(a * (n % d) for d, a in scaled.items())
    if n <= H:
        assert P == T
    lower_integer_total += (S * P * P) // (T * T * n * n)

raw_prefix_lower = Fraction(lower_integer_total, S)
assert raw_prefix_lower == Fraction(104700971949, 62500000000)
# Zeta(2) < 5/3, proved by the first five terms plus a telescoping tail.
assert sum((Fraction(1, n*n) for n in range(1, 6)), Fraction()) + Fraction(1, 5) < Fraction(5, 3)
q_energy_lower = Fraction(3, 5) * raw_prefix_lower
target = Fraction(513, 512)
assert q_energy_lower == Fraction(314102915847, 312500000000)
assert q_energy_lower - target == Fraction(1985128569, 625000000000) > 0
print("Exact-head equations 1..320: passed")
print("Raw prefix lower bound through 2048:", raw_prefix_lower)
print("Complete Q-energy is strictly above:", q_energy_lower)
print("This exceeds 513/512 by:", q_energy_lower - target)
print("Specified direct repair fails; other H=320 constructions remain open.")

# A correction conductor already dividing the primorial through 317.
D = 326
assert D == 2 * 163 and 163 in primes and T % D == 0
scaled.pop(p)
scaled[D] = int(T * head_mobius_slope)
P = 0
lower_integer_total = 0
for n in range(1, K + 1):
    P += T - sum(d * a for d, a in scaled.items() if n % d == 0)
    assert P == sum(a * (n % d) for d, a in scaled.items())
    if n <= H:
        assert P == T
    lower_integer_total += (S * P * P) // (T * T * n * n)
assert lower_integer_total == 1675647282981
q_lower_326 = Fraction(3 * lower_integer_total, 5 * S)
assert q_lower_326 - target == Fraction(17176223943, 5000000000000) > 0
print("Correction conductor 326 also fails; complete Q energy is strictly above:", q_lower_326)
```
