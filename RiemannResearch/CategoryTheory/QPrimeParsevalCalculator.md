# Finite native Q prime tower calculator

Save the Python listing as `q_prime_parseval.py` and run `python q_prime_parseval.py 2 3 5 7` with `mpmath` and `sympy` installed. The table uses 45 decimal places internally. For a chosen prime cutoff, `stage_fit` returns the period, ordered mixed conductors, signed projection coefficients, and captured squared norm. A finite period bounds exponents of the admitted primes. The cofinal sequence has the same limiting projection as the full largest-prime tower.

[Gram construction and computed stages](PhysicalParityObject.md#computing-finite-prime-stages)

```python
#!/usr/bin/env python3
"""Compute finite native-Q mixed-packet fits for the centered parity target.

A window at prime p contains all mixed divisors of lcm(1,...,p). These
finite windows exhaust the mixed space, including all prime-power lifts.
Dependencies: mpmath and sympy.
"""

import argparse
from dataclasses import dataclass
from functools import lru_cache
from math import lcm

import mpmath as mp
from sympy import divisors, factorint, isprime, mobius


@dataclass
class StageFit:
    period: int
    conductors: tuple[int, ...]
    coefficients: tuple
    captured: mp.mpf


@lru_cache(maxsize=None)
def mobius_row(conductor):
    terms = []
    for d in divisors(conductor):
        mu = int(mobius(conductor // d))
        if mu:
            terms.append((int(d), mu))
    return terms


def stage_fit(cutoff):
    """Return the signed Gram fit to h = 1_odd/log(2) - 1."""
    if not isprime(cutoff):
        raise ValueError("the cutoff must be prime")
    period = lcm(*range(1, cutoff + 1))
    conductors = tuple(int(d) for d in divisors(period) if len(factorint(d)) >= 2)
    if not conductors:
        return StageFit(period, conductors, (), mp.mpf(0))

    zeta_two = mp.zeta(2)
    log_two = mp.log(2)
    gram = mp.matrix(len(conductors))
    moments = mp.matrix(len(conductors), 1)
    packet_rows = [mobius_row(d) for d in conductors]
    for a in range(1, period + 1):
        weight = mp.zeta(2, mp.mpf(a) / period) / (zeta_two * period**2)
        target = (a % 2) / log_two - 1
        row = [sum(mu * (a % d) for d, mu in terms) for terms in packet_rows]
        for i, left in enumerate(row):
            if left:
                moments[i] += weight * target * left
                for j in range(i + 1):
                    gram[i, j] += weight * left * row[j]
    for i in range(len(conductors)):
        for j in range(i):
            gram[j, i] = gram[i, j]
    coefficients = mp.cholesky_solve(gram, moments)
    return StageFit(period, conductors, tuple(coefficients), (moments.T * coefficients)[0])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("primes", type=int, nargs="*", default=[2, 3, 5, 7])
    args = parser.parse_args()
    if any(not isprime(p) for p in args.primes) or args.primes != sorted(set(args.primes)):
        parser.error("give strictly increasing prime cutoffs")

    with mp.workdps(45):
        total = mp.mpf(3) / 4 * (1 / mp.log(2) - 1)**2 + mp.mpf(1) / 4
        previous = mp.mpf(0)
        print("prime  period  rows  captured  increment  residual")
        for prime in args.primes:
            fit = stage_fit(prime)
            print(prime, fit.period, len(fit.conductors), mp.nstr(fit.captured, 15),
                  mp.nstr(fit.captured - previous, 15), mp.nstr(total - fit.captured, 15))
            previous = fit.captured


if __name__ == "__main__":
    main()
```
