# Finite native Q prime tower calculator

Save the Python listing as `q_prime_parseval.py` and run `python q_prime_parseval.py 2 3 5 7` with `mpmath` and `sympy` installed. The table uses 45 decimal places internally. To hold the prime cutoff fixed, run `python q_prime_parseval.py 3 --exponent 3` for the nine mixed rows in period 216. Raising the common exponent exhausts the full mixed space at that cutoff. For a chosen prime cutoff, `stage_fit` returns the period, ordered mixed conductors, signed projection coefficients, and captured squared norm. A finite period bounds exponents of the admitted primes. The cofinal sequence has the same limiting projection as the full largest-prime tower.

Run `python q_prime_parseval.py --certify-first-layer` to verify the positive prime-3 margin with exact rational arithmetic. The fixed integers in `prime_three_certificate` are the coefficients of a trial vector, scaled by one million. The sign of each trial summand selects a lower or upper enclosure of its complete residue-class mass.

[Gram construction and computed stages](PhysicalParityObject.md#computing-finite-prime-stages)

```python
#!/usr/bin/env python3
"""Compute finite native-Q mixed-packet fits for the centered parity target.

A window at prime p contains all mixed divisors of lcm(1,...,p). These
finite windows exhaust the mixed space, including all prime-power lifts.
With --exponent j, the period is the jth power of the primorial through p.
Dependencies: mpmath and sympy.
"""

import argparse
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import lcm, prod

import mpmath as mp
from sympy import divisors, factorint, isprime, mobius, primerange


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


def stage_fit(cutoff, *, exponent=None):
    """Return the signed Gram fit to h = 1_odd/log(2) - 1."""
    if not isprime(cutoff):
        raise ValueError("the cutoff must be prime")
    if exponent is None:
        period = lcm(*range(1, cutoff + 1))
    else:
        if not isinstance(exponent, int) or exponent < 1:
            raise ValueError("the common exponent must be a positive integer")
        period = prod(primerange(2, cutoff + 1))**exponent
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



def prime_three_certificate():
    """Lower bound for zeta(2) times the excess of the trial energy over 10149/100000."""
    integers = {
        6: -236707, 12: 89378, 18: -104781, 24: 32621, 36: 18122, 48: 11398,
        54: -33521, 72: 6051, 108: 7991, 144: 1771, 162: -10017, 216: 2626,
        324: 1738, 432: -1103, 648: 212, 1296: -84,
    }
    log_lower = sum(Fraction(2, (2*k + 1)*3**(2*k + 1)) for k in range(12))
    log_upper = log_lower + Fraction(2, 25*3**25) * Fraction(9, 8)
    odd_lower, odd_upper = 1/log_upper - 1, 1/log_lower - 1
    threshold = Fraction(10149, 100000)
    scale, period, blocks = 10**18, 1296, 64
    rows = [(c, mobius_row(d)) for d, c in integers.items()]
    margin = Fraction(0)
    for a in range(1, period + 1):
        value = Fraction(sum(c * sum(mu * (a % d) for d, mu in row)
                             for c, row in rows), 10**6)
        target = -1
        if a % 2:
            target = odd_lower if value >= 0 else odd_upper
        trial = 2*target*value - value**2 - threshold
        tail_start = a + blocks*period
        denominators = [(a + k*period)**2 for k in range(blocks)]
        denominators.append(period*tail_start)
        if trial >= 0:
            weight = sum(scale // d for d in denominators)
        else:
            denominators.append(tail_start**2)
            weight = sum((scale + d - 1) // d for d in denominators)
        margin += trial * Fraction(weight, scale)
    return margin


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("primes", type=int, nargs="*", default=[2, 3, 5, 7])
    parser.add_argument("--exponent", type=int,
                        help="give each admitted prime this maximum exponent")
    parser.add_argument("--certify-first-layer", action="store_true",
                        help="check the rational lower bound for the full prime-3 layer")
    args = parser.parse_args()
    if args.certify_first_layer:
        margin = prime_three_certificate()
        if margin <= Fraction(16130543, 10**12):
            raise ArithmeticError("prime-3 certificate failed")
        print("floor(10^12 * certified unnormalized margin) =", (10**12 * margin) // 1)
        return
    if args.exponent is not None and args.exponent < 1:
        parser.error("give a positive common exponent")
    if any(not isprime(p) for p in args.primes) or args.primes != sorted(set(args.primes)):
        parser.error("give strictly increasing prime cutoffs")

    with mp.workdps(45):
        total = mp.mpf(3) / 4 * (1 / mp.log(2) - 1)**2 + mp.mpf(1) / 4
        previous = mp.mpf(0)
        print("prime  period  rows  captured  increment  residual")
        for prime in args.primes:
            fit = stage_fit(prime, exponent=args.exponent)
            print(prime, fit.period, len(fit.conductors), mp.nstr(fit.captured, 15),
                  mp.nstr(fit.captured - previous, 15), mp.nstr(total - fit.captured, 15))
            previous = fit.captured


if __name__ == "__main__":
    main()
```

For arbitrary periodic packets, the [character tower calculation](ValuationCharacterTower.md) gives the complete signed ambient layer Gram and the period-ten and period-thirty examples.

## Symbolic period-six projection

Evaluate this Wolfram Language listing to obtain the period-six Gram, signed moment, signed projection coefficient, and captured energy. The output also checks the three one-prime wavelet inner products and the ambient parity energy. The CRT calculation gives each later prime energy for the period-six row and checks its full symbolic Parseval identity. In the symbolic answer, `rho` denotes the quadratic Dirichlet value divided by Riemann zeta at two, and `lambda` denotes the natural logarithm of two.

```wolfram
(* Native Q mixed fit on period six. rho denotes L(2,chi_-3)/Zeta[2]. *)
NativeQPrimeTower`qSixFit[rho_, lambda_] := Module[{w, weights, row, odd, gram, moment},
  weights = Array[w, 6] /. First[Solve[{
    w[1] + w[5] == 2/3, w[1] - w[5] == 5 rho/4,
    w[2] + w[4] == 2/9, w[4] - w[2] == -rho/4,
    w[3] == 1/12, w[6] == 1/36}, Array[w, 6]]];
  row = Table[Mod[n, 6] - Mod[n, 2] - Mod[n, 3], {n, 6}];
  odd = Mod[Range[6], 2];
  gram = Factor[weights . (row^2)];
  moment = Together[weights . (row (odd/lambda - 1))];
  <|"Weights" -> weights, "Row" -> row, "Gram" -> gram,
    "SignedMoment" -> moment, "SignedCoefficient" -> Factor[moment/gram],
    "CapturedEnergy" -> Factor[moment^2/gram]|>
];

NativeQPrimeTower`qWaveletChecks[r_, k_, j_] := FullSimplify[{
  (r^(k+1) - r r^k)/Sqrt[r^(k+1) (1-r)],
  (r^(k+1) - 2 r r^(k+1) + r^2 r^k)/(r^(k+1) (1-r)),
  (r^(j+1) - r r^j - r r^(j+1) + r^2 r^j)/
    Sqrt[r^(k+1) (1-r) r^(j+1) (1-r)]
}, Assumptions -> 0 < r < 1 && j > k >= 0];

(* Complete ambient prime energies of the CRT row J6. eta is the mean of the unit sign. *)
NativeQPrimeTower`qSixAmbient[eta_, prime_, tailMean_] := Module[
  {probs, atTwo, mean, two, three, tail, factor},
  probs = {3/4, 1/5, 1/20};
  atTwo = {2/3 - 4 eta/3, 4 (1-eta)/3, 4 (1+eta)/3};
  mean = Factor[probs . atTwo];
  two = Expand[probs . (atTwo^2) - mean^2];
  three = Expand[(2/9) ((4/5) (1+eta)^2 + (1/5) (1-eta)^2)];
  tail = 2 (1-eta^2);
  factor = Factor[Sum[(1-1/prime^2) (-1/prime^2)^k, {k, 0, Infinity},
    Assumptions -> prime > 1]];
  <|"Mean" -> mean, "Prime2Energy" -> two, "Prime3Energy" -> three,
    "TailAfter3" -> tail, "SignedGeometricFactor" -> factor,
    "EnergyForPrime2Mod3" -> Factor[2 tailMean^2 (1-factor^2)],
    "ParsevalDifference" -> Expand[mean^2+two+three+tail-(3-8 eta/5)]|>
];

NativeQPrimeTower`results = Module[{rhoN, direct, fitN, target, parity},
  rhoN = (N[Zeta[2, 1/3], 75] - N[Zeta[2, 2/3], 75])/(9 N[Zeta[2], 75]);
  direct = Table[N[Zeta[2, a/6], 70]/(36 N[Zeta[2], 70]), {a, 6}];
  fitN = NativeQPrimeTower`qSixFit[rhoN, N[Log[2], 65]];
  target = (3/4) (1/Log[2] - 1)^2 + 1/4;
  parity = {3/4, -Sqrt[3]/4};
  <|"SymbolicMixedFit" -> NativeQPrimeTower`qSixFit[NativeQPrimeTower`rho, NativeQPrimeTower`lambda],
    "PeriodSixWeightAgreement" -> (Max[Abs[direct - fitN["Weights"]]] < 10^-55),
    "NumericalFit" -> N[{fitN["SignedCoefficient"], fitN["CapturedEnergy"]}, 28],
    "AmbientCRTRow" -> NativeQPrimeTower`qSixAmbient[NativeQPrimeTower`eta, NativeQPrimeTower`prime, NativeQPrimeTower`tailMean],
    "ValuationWaveletMeanNormSqCross" -> NativeQPrimeTower`qWaveletChecks[NativeQPrimeTower`r, NativeQPrimeTower`k, NativeQPrimeTower`j],
    "OddIndicatorConstantAndPrimeTwoMode" -> parity,
    "AmbientParityEnergyMinusTarget" ->
      FullSimplify[(parity[[1]]/Log[2]-1)^2+(parity[[2]]/Log[2])^2-target]|>
];

NativeQPrimeTower`results
```
