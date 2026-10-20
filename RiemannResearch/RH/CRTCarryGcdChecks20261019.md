# Exact gcd-tail finite checks — 19 October 2026

These Python standard-library Fraction calculations are independent finite
checks, not Lean certificates or an asymptotic RH estimate. All assertions
passed at L=2,6,30. Copy the following code to `gcd_tail_charge.py` and run
`python3 gcd_tail_charge.py`; its JSON output is reproduced below.

## Reproduction source

```python
"""Exact rational gcd-class, Jordan-charge, and fluctuation checks.

These are finite Python Fraction checks, not Lean verification or an
asymptotic estimate. Every divisor atom and every residue 1,...,L is used.
The least-squares solve uses exact Gaussian elimination from the prior
CRT-carry finite experiment. No floating-point value is used by an assertion.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import math

def divisors(L):
    return [d for d in range(2, L + 1) if L % d == 0]


def exact_solve(A, b):
    n = len(b)
    A = [list(row) + [v] for row, v in zip(A, b)]
    for j in range(n):
        pivot = next(i for i in range(j, n) if A[i][j])
        A[j], A[pivot] = A[pivot], A[j]
        z = A[j][j]
        A[j] = [v / z for v in A[j]]
        for i in range(n):
            if i != j:
                z = A[i][j]
                A[i] = [a - z * c for a, c in zip(A[i], A[j])]
    return [row[-1] for row in A]


def totient(n):
    return sum(math.gcd(a, n) == 1 for a in range(1, n + 1))


def check_stage(L):
    ds = divisors(L)
    all_divisors = [1] + ds
    sites = range(1, L + 1)
    rows = {a: [F(a % d, d) for d in ds] for a in sites}
    weights = {a: F(1, a * a) + F(2, L * (2 * a + L)) for a in sites}
    gram = [[sum(weights[a] * rows[a][i] * rows[a][j] for a in sites)
             for j in range(len(ds))] for i in range(len(ds))]
    means = [sum(weights[a] * rows[a][i] for a in sites)
             for i in range(len(ds))]
    coeff = exact_solve(gram, means)
    residual = {a: 1 - sum(x * y for x, y in zip(rows[a], coeff)) for a in sites}
    charge = {a: weights[a] * residual[a] for a in sites}
    energy = sum(weights[a] * residual[a] ** 2 for a in sites)
    moment = sum(a * charge[a] for a in sites)
    tails = {}
    accum = F(0)
    for k in reversed(list(sites)):
        accum += charge[k]
        tails[k] = accum
    assert moment == F(5, 3 * L)
    assert tails[1] == energy
    c = F(5, 3 * L * L)
    centered = {k: tails[k] - c for k in sites}
    classes = []
    for e in all_divisors:
        members = [k for k in sites if math.gcd(k, L) == e]
        total = sum(tails[k] for k in members)
        expected = F(5 * totient(L // e), 3 * L * L)
        assert len(members) == totient(L // e)
        assert total == expected == len(members) * c
        assert sum(centered[k] for k in members) == 0
        assert sum(tails[k] ** 2 for k in members) == (
            len(members) * c * c + sum(centered[k] ** 2 for k in members))
        classes.append(dict(gcd=e, cardinality=len(members),
                            charge=str(total), average=str(c),
                            centered_charge="0"))
    for d in all_divisors:
        assert sum(tails[k] for k in sites if k % d == 0) == moment / d
    coprime_noninitial = [k for k in range(2, L + 1) if math.gcd(k, L) == 1]
    positive = sum((max(tails[k], F(0)) for k in coprime_noninitial), F(0))
    negative = sum((max(-tails[k], F(0)) for k in coprime_noninitial), F(0))
    boundary = F(5 * totient(L), 3 * L * L)
    signed = sum((tails[k] for k in coprime_noninitial), F(0))
    assert signed == positive - negative
    assert energy + signed == boundary
    assert negative == energy - boundary + positive
    squares = sum(tails[k] ** 2 for k in sites)
    fluctuation_squares = sum(centered[k] ** 2 for k in sites)
    assert sum(centered.values()) == 0
    assert squares == L * c * c + fluctuation_squares
    assert centered[1] == energy - c
    abstract_checked = False
    if L > 2:
        # This is only a counterexample to extracting energy control from
        # the linear class equations. No energy/legality assertion is made.
        abstract = {k: F(0) for k in sites}
        abstract[1] = F(1)
        abstract[L - 1] = boundary - 1
        for e in ds:
            abstract[e] = F(5 * totient(L // e), 3 * L * L)
        for e in all_divisors:
            assert sum(abstract[k] for k in sites if math.gcd(k, L) == e) == (
                F(5 * totient(L // e), 3 * L * L))
        abstract_checked = True
    return dict(L=L, status="EXACT_FRACTION_ASSERTIONS_PASSED",
                energy=str(energy), common_average=str(c),
                coprime_positive_charge=str(positive),
                coprime_negative_charge=str(negative),
                coprime_boundary=str(boundary), gcd_classes=classes,
                squared_charge=str(squares),
                squared_within_class_fluctuation=str(fluctuation_squares),
                abstract_linear_counterexample_checked=abstract_checked)


if __name__ == "__main__":
    result = dict(status="FINITE_EXACT_CHECKS_NOT_LEAN_VERIFICATION",
                  stages=[check_stage(L) for L in (2, 6, 30)])
    destination = Path(__file__).with_name("gcd_tail_charge_results.json")
    destination.write_text(json.dumps(result, indent=2) + "\n")
    for stage in result["stages"]:
        print(f"L={stage['L']}: all gcd-class, Jordan-charge, and centered-square identities passed")
    print(destination)
```

## Exact output

```json
{
  "status": "FINITE_EXACT_CHECKS_NOT_LEAN_VERIFICATION",
  "stages": [
    {
      "L": 2,
      "status": "EXACT_FRACTION_ASSERTIONS_PASSED",
      "energy": "5/12",
      "common_average": "5/12",
      "coprime_positive_charge": "0",
      "coprime_negative_charge": "0",
      "coprime_boundary": "5/12",
      "gcd_classes": [
        {
          "gcd": 1,
          "cardinality": 1,
          "charge": "5/12",
          "average": "5/12",
          "centered_charge": "0"
        },
        {
          "gcd": 2,
          "cardinality": 1,
          "charge": "5/12",
          "average": "5/12",
          "centered_charge": "0"
        }
      ],
      "squared_charge": "25/72",
      "squared_within_class_fluctuation": "0",
      "abstract_linear_counterexample_checked": false
    },
    {
      "L": 6,
      "status": "EXACT_FRACTION_ASSERTIONS_PASSED",
      "energy": "8851285/96950304",
      "common_average": "5/108",
      "coprime_positive_charge": "13955/10772256",
      "coprime_negative_charge": "0",
      "coprime_boundary": "5/54",
      "gcd_classes": [
        {
          "gcd": 1,
          "cardinality": 2,
          "charge": "5/54",
          "average": "5/108",
          "centered_charge": "0"
        },
        {
          "gcd": 2,
          "cardinality": 2,
          "charge": "5/54",
          "average": "5/108",
          "centered_charge": "0"
        },
        {
          "gcd": 3,
          "cardinality": 1,
          "charge": "5/108",
          "average": "5/108",
          "centered_charge": "0"
        },
        {
          "gcd": 6,
          "cardinality": 1,
          "charge": "5/108",
          "average": "5/108",
          "centered_charge": "0"
        }
      ],
      "squared_charge": "42501583383925/2349840361423104",
      "squared_within_class_fluctuation": "12282442933525/2349840361423104",
      "abstract_linear_counterexample_checked": true
    },
    {
      "L": 30,
      "status": "EXACT_FRACTION_ASSERTIONS_PASSED",
      "energy": "1946337934241423244305102078066608048851013831922662056350392881857407813/46142685536595233303997611797032844933164858100604846930055566189216140512",
      "common_average": "1/540",
      "coprime_positive_charge": "0",
      "coprime_negative_charge": "6313712964792654495303465072034310989946561152161099398044144691567324953/230713427682976166519988058985164224665824290503024234650277830946080702560",
      "coprime_boundary": "2/135",
      "gcd_classes": [
        {
          "gcd": 1,
          "cardinality": 8,
          "charge": "2/135",
          "average": "1/540",
          "centered_charge": "0"
        },
        {
          "gcd": 2,
          "cardinality": 8,
          "charge": "2/135",
          "average": "1/540",
          "centered_charge": "0"
        },
        {
          "gcd": 3,
          "cardinality": 4,
          "charge": "1/135",
          "average": "1/540",
          "centered_charge": "0"
        },
        {
          "gcd": 5,
          "cardinality": 2,
          "charge": "1/270",
          "average": "1/540",
          "centered_charge": "0"
        },
        {
          "gcd": 6,
          "cardinality": 4,
          "charge": "1/135",
          "average": "1/540",
          "centered_charge": "0"
        },
        {
          "gcd": 10,
          "cardinality": 2,
          "charge": "1/270",
          "average": "1/540",
          "centered_charge": "0"
        },
        {
          "gcd": 15,
          "cardinality": 1,
          "charge": "1/540",
          "average": "1/540",
          "centered_charge": "0"
        },
        {
          "gcd": 30,
          "cardinality": 1,
          "charge": "1/540",
          "average": "1/540",
          "centered_charge": "0"
        }
      ],
      "squared_charge": "4505307191021524036608051814856370816003222359945463394401810942973275512211084044749586326847528580551758724684779905408304557704305262882502511/1774289523774262444691822073647640630474223708533526311865026308988720567912889016632177794612009004937354100998503454493039716875106178547439685120",
      "squared_within_class_fluctuation": "288184474437276757140867226109439531557456087998191892192870892021340997330444772965252409481110897105800690692301489890779702222295891472362721/118285968251617496312788138243176042031614913902235087457668420599248037860859267775478519640800600329156940066566896966202647791673745236495979008",
      "abstract_linear_counterexample_checked": true
    }
  ]
}
```
