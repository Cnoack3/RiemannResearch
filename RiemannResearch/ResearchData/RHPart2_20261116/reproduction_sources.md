# Reproduction sources and retained output

The exact executable sources are retained below. Save a code block under its indicated filename beside the JSON data files to rerun it. Standalone scripts are also supplied in the RH part 2 Drive folder. The code blocks are external computations except for the separately verified Lean audit snippet.

## Phase diagnostics

Filename: `phase_diagnostics.py`.

```python
"""Reproducible, non-certified finite zero-phase diagnostics; no asymptotic inference."""
import json
import platform
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
z = np.array(json.loads((HERE / 'phase_ordinates.json').read_text()), dtype=float)
assert len(z) == 300 and np.all(np.diff(z) > 0) and z[-1] > 400
primes = np.array([2, 3, 5, 7])
rng = np.random.default_rng(20261116)

def circular_pair_dist(u):
    d = np.abs(u[:, None, :] - u[None, :, :])
    return np.minimum(d, 1-d)

def nearest(u):
    d = np.max(circular_pair_dist(u), axis=2)
    np.fill_diagonal(d, np.inf)
    return np.min(d, axis=1)

out = []
for lo, hi in [(50, 100), (100, 200), (200, 400)]:
    v = z[(lo < z) & (z <= hi)]
    u = np.mod(np.outer(v, np.log(primes)/(2*np.pi)), 1)
    n = len(v)
    fourier = np.exp(2j*np.pi*u).mean(axis=0)
    prediction = -(hi-lo)*np.log(primes)/(2*np.pi*np.sqrt(primes)*n)
    sorted_u = np.sort(u, axis=0)
    kuiper = np.max(np.arange(1,n+1)[:,None]/n-sorted_u,axis=0) + np.max(sorted_u-np.arange(n)[:,None]/n,axis=0)
    nn = nearest(u)
    iid_medians = [float(np.median(nearest(rng.random(u.shape)))) for _ in range(100)]
    d = circular_pair_dist(u)
    far = {}
    for eta in [.001,.005,.01,.02,.05]:
        counts = np.sum(d > 2*eta,axis=2)
        np.fill_diagonal(counts, len(primes)+1)
        far[str(eta)] = int(counts.min())
    out.append(dict(window=[lo,hi],count=n,first_fourier_real=fourier.real.tolist(),first_fourier_imag=fourier.imag.tolist(),
        classical_prime_bias_prediction=prediction.tolist(),centered_first_fourier_abs=np.abs(fourier-prediction).tolist(),
        kuiper_by_prime=kuiper.tolist(),sup_nearest_quantiles=np.quantile(nn,[0,.5,1]).tolist(),
        iid_median_nearest_100_replicate_quantiles=np.quantile(iid_medians,[.05,.5,.95]).tolist(),
        floating_point_minimum_half_separation=float(nn.min()/2),minimum_far_coordinate_count=far))
result=dict(status='external floating-point diagnostic, not interval-certified or Lean-verified',
    zero_provider='Wolfram ZetaZero, first 300, machine precision',last_ordinate=float(z[-1]),
    primes=primes.tolist(),seed=20261116,python=platform.python_version(),numpy=np.__version__,windows=out)
(HERE / 'phase_diagnostics.json').write_text(json.dumps(result,indent=2)+'\n')
(HERE / 'phase_ordinates.json').write_text(json.dumps(z.tolist())+'\n')
for row in out:
    print(row)
```

## Interval certificate

Filename: `prime_cover_c2_odd_endpoint_repaired.py`.

```python
#!/usr/bin/env python3
"""Repaired interval computation for the odd first-prime endpoint.

2026-11-16 audit: exact Decimal negation/absolute value; outward
square-root neighbors; outward ainf tail product; exact-zero branch only.
This is an external computation, not a Lean proof. The operator reduction
and analytic series/tail bounds remain separate paper obligations.

This verifies the sufficient Schur criterion in Theorem 4.5 of the
all-tracks audit with J=20, N=4, K=2001.  Only Python's decimal and
fractions modules are used.  Elementary constants and trigonometric
values are enclosed from convergent series; all subsequent arithmetic
uses outward rounding.
"""

from __future__ import annotations

from decimal import Decimal, Context, ROUND_CEILING, ROUND_FLOOR, localcontext
import json
from pathlib import Path
from fractions import Fraction
from math import factorial


PREC = 70
CF = Context(prec=PREC, rounding=ROUND_FLOOR)
CC = Context(prec=PREC, rounding=ROUND_CEILING)


def df(x):
    with localcontext(CF):
        return +Decimal(x)


def dc(x):
    with localcontext(CC):
        return +Decimal(x)


class I:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        self.lo = df(lo)
        self.hi = dc(lo if hi is None else hi)
        if self.lo > self.hi:
            raise ValueError((self.lo, self.hi))

    def __add__(self, other):
        other = as_i(other)
        with localcontext(CF):
            lo = self.lo + other.lo
        with localcontext(CC):
            hi = self.hi + other.hi
        return I(lo, hi)

    __radd__ = __add__

    def __neg__(self):
        return I(self.hi.copy_negate(), self.lo.copy_negate())

    def __sub__(self, other):
        return self + (-as_i(other))

    def __rsub__(self, other):
        return as_i(other) - self

    def __mul__(self, other):
        other = as_i(other)
        vals = []
        for a in (self.lo, self.hi):
            for b in (other.lo, other.hi):
                with localcontext(CF):
                    vlo = a * b
                with localcontext(CC):
                    vhi = a * b
                vals.append((vlo, vhi))
        return I(min(v[0] for v in vals), max(v[1] for v in vals))

    __rmul__ = __mul__

    def inv(self):
        if self.lo <= 0 <= self.hi:
            raise ZeroDivisionError(self)
        with localcontext(CF):
            lo1, lo2 = Decimal(1) / self.lo, Decimal(1) / self.hi
        with localcontext(CC):
            hi1, hi2 = Decimal(1) / self.lo, Decimal(1) / self.hi
        return I(min(lo1, lo2), max(hi1, hi2))

    def __truediv__(self, other):
        return self * as_i(other).inv()

    def __rtruediv__(self, other):
        return as_i(other) / self

    def sqr(self):
        if self.lo <= 0 <= self.hi:
            with localcontext(CC):
                hi = max(self.lo * self.lo, self.hi * self.hi)
            return I(0, hi)
        return self * self

    def mid(self):
        return (self.lo + self.hi) / Decimal(2)

    def __repr__(self):
        return f"[{self.lo}, {self.hi}]"


def as_i(x):
    return x if isinstance(x, I) else I(x)


def frac_i(q: Fraction):
    with localcontext(CF):
        lo = Decimal(q.numerator) / Decimal(q.denominator)
    with localcontext(CC):
        hi = Decimal(q.numerator) / Decimal(q.denominator)
    return I(lo, hi)


def atanh_log_rational(z: Fraction, terms: int):
    # log((1+z)/(1-z)) = 2 sum z^(2k+1)/(2k+1), z in (0,1).
    s = Fraction(0)
    z2 = z * z
    p = z
    for k in range(terms):
        s += p / (2 * k + 1)
        p *= z2
    tail = p / ((2 * terms + 1) * (1 - z2))
    return frac_i(2 * s) + I(0, frac_i(2 * tail).hi)


def arctan_alt_fraction(q: int, terms: int):
    # Alternating series for arctan(1/q); the true value lies between
    # two consecutive partial sums.
    z = Fraction(1, q)
    s = Fraction(0)
    p = z
    sign = 1
    for k in range(terms):
        s += sign * p / (2 * k + 1)
        p *= z * z
        sign *= -1
    nxt = sign * p / (2 * terms + 1)
    return min(s, s + nxt), max(s, s + nxt)


def sqrt_i(x: I):
    if x.lo < 0:
        raise ValueError(x)
    with localcontext(CF):
        lo = max(Decimal(0), x.lo.sqrt().next_minus())
    with localcontext(CC):
        hi = x.hi.sqrt().next_plus()
    return I(lo, hi)


def reduce_angle(x: I, two_pi: I):
    # Widths here are far below 1, so midpoint rounding identifies the
    # same multiple of 2*pi at both endpoints.
    q = x.mid() / two_pi.mid()
    n = int(q.to_integral_value())
    r = x - n * two_pi
    if r.lo < -two_pi.hi / 2 or r.hi > two_pi.hi / 2:
        raise AssertionError((x, n, r))
    return r


def sin_i(x: I, pi: I, terms: int = 45):
    r = reduce_angle(x, 2 * pi)
    r2 = r.sqr()
    term = r
    s = I(0)
    for k in range(terms):
        s += term
        term = -term * r2 / ((2 * k + 2) * (2 * k + 3))
    a = max(r.lo.copy_abs(), r.hi.copy_abs())
    with localcontext(CC):
        err = a ** (2 * terms + 1) / Decimal(factorial(2 * terms + 1))
    return s + I(err.copy_negate(), err)


def cos_i(x: I, pi: I, terms: int = 45):
    r = reduce_angle(x, 2 * pi)
    r2 = r.sqr()
    term = I(1)
    s = I(0)
    for k in range(terms):
        s += term
        term = -term * r2 / ((2 * k + 1) * (2 * k + 2))
    a = max(r.lo.copy_abs(), r.hi.copy_abs())
    with localcontext(CC):
        err = a ** (2 * terms) / Decimal(factorial(2 * terms))
    return s + I(err.copy_negate(), err)


LOG2 = atanh_log_rational(Fraction(1, 3), 90)
LOG3 = atanh_log_rational(Fraction(1, 2), 130)
A5_LO, A5_HI = arctan_alt_fraction(5, 75)
A239_LO, A239_HI = arctan_alt_fraction(239, 25)
PI_MACHIN = I(
    frac_i(16 * A5_LO - 4 * A239_HI).lo,
    frac_i(16 * A5_HI - 4 * A239_LO).hi,
)
# The decimal enclosure below is a coarser enclosure of the Machin
# interval, retained to make the certificate output readily auditable.
PI = I(
    "3.14159265358979323846264338327950288419716939937510582097494459230780",
    "3.14159265358979323846264338327950288419716939937510582097494459230783",
)
if not (PI.lo <= PI_MACHIN.lo and PI_MACHIN.hi <= PI.hi):
    raise AssertionError((PI_MACHIN, PI))
SQRT2 = sqrt_i(I(2))
SQRT3 = sqrt_i(I(3))
W = LOG2 / SQRT2
LOGPI_Z = (PI - 1) / (PI + 1)


def log_from_interval_z(z: I, terms=180):
    # Positive atanh series evaluated with intervals plus a monotone tail.
    z2 = z.sqr()
    p = z
    s = I(0)
    for k in range(terms):
        s += p / (2 * k + 1)
        p *= z2
    tail = 2 * p / ((2 * terms + 1) * (1 - z2))
    return 2 * s + I(0, tail.hi)


LOGPI = log_from_interval_z(LOGPI_Z)


def gamma_i():
    n = 1024
    h = I(0)
    for k in range(1, n + 1):
        h += I(1) / k
    base = h - 10 * LOG2 - I(1) / (2 * n) + I(1) / (12 * n**2)
    base -= I(1) / (120 * n**4)
    upper = base + I(1) / (252 * n**6)
    lower = upper - I(1) / (240 * n**8)
    return I(lower.lo, upper.hi)


GAMMA = gamma_i()
KAPPA = GAMMA + 3 * LOG2 + LOGPI + PI / 2
B = LOG3
L = LOG2


def alpha(j):
    return I(4 * j + 1) / 2


def kfreq(m):
    return m * PI / B


def ainf(m, terms=20000):
    t2 = kfreq(m).sqr()
    s = I(0)
    for j in range(terms):
        al = alpha(j)
        s += 2 * t2 / (al * (al.sqr() + t2))
    # 2*t^2 sum alpha^-3, alpha_j >= 2j for j>=terms.
    M = Decimal(terms)
    with localcontext(CC):
        tail_factor = Decimal(1) / (4 * M**3) + Decimal(1) / (8 * M**2)
    return s + I(0, (t2 * I(tail_factor)).hi)


AINF = {m: ainf(m) for m in (1, 3, 5, 7, 9)}


def f_int(c: I, d: I, lo: I, hi: I):
    if c.lo <= 0 <= c.hi:
        if c.lo != 0 or c.hi != 0:
            raise ZeroDivisionError(c)
        return cos_i(d, PI) * (hi - lo)
    return (sin_i(c * hi + d, PI) - sin_i(c * lo + d, PI)) / c


def sigma(m, n):
    if m == n:
        k = kfreq(m)
        return 2 * ((B - L) * cos_i(k * L, PI) - sin_i(k * L, PI) / k) / B
    lo = -B / 2 + L
    hi = B / 2

    def ii(a, c):
        aa, bb = kfreq(a), kfreq(c)
        return (f_int(aa - bb, bb * L, lo, hi) - f_int(aa + bb, -bb * L, lo, hi)) / B

    return ii(m, n) + ii(n, m)


def pow3_neg_alpha(j):
    # 3^{-(2j+1/2)} = 3^{-2j}/sqrt(3).
    return I(1) / (I(3 ** (2 * j)) * SQRT3)


def robin(m, n, J=20):
    km, kn = kfreq(m), kfreq(n)
    phase = -1 if (((m - 1) // 2 + (n - 1) // 2) % 2) else 1
    s = I(0)
    for j in range(J + 1):
        al = alpha(j)
        s += al.sqr() * (1 + pow3_neg_alpha(j)) / (
            (al.sqr() + km.sqr()) * (al.sqr() + kn.sqr())
        )
    return phase * 4 * s / B


def g(m, n):
    z = -W * sigma(m, n) + robin(m, n)
    if m == n:
        z += AINF[m] - KAPPA
    return z


def ldl_pivots(a):
    a = [[I(x.lo, x.hi) for x in row] for row in a]
    piv = []
    for k in range(len(a)):
        d = a[k][k]
        if d.lo <= 0:
            raise AssertionError((k, d))
        piv.append(d)
        for i in range(k + 1, len(a)):
            for j in range(i, len(a)):
                z = a[i][j] - a[i][k] * a[j][k] / d
                a[i][j] = a[j][i] = z
    return piv


def main():
    # Scalar tail gap: monotonicity of a_infinity gives gamma_n >= gamma_9.
    gamma9 = AINF[9] - KAPPA - W
    if gamma9.lo <= Decimal("0.9"):
        raise AssertionError(gamma9)

    modes = (1, 3, 5, 7)
    A = [[g(m, n) for n in modes] for m in modes]
    S = [[I(A[i][j].lo, A[i][j].hi) for j in range(4)] for i in range(4)]
    for n in range(9, 2002, 2):
        x = [g(m, n) for m in modes]
        for i in range(4):
            for j in range(4):
                S[i][j] -= I(10) * x[i] * x[j] / 9

    # For n>2001: |x_{m,n}| <= 63/(50n), m=1,3,5,7.  Therefore
    # (10/9) sum ||x_n||^2 <= tau, even after enlarging the odd sum to
    # all integers n>2001.
    tau = I(10) / 9 * 4 * (I(63) / 50).sqr() / 2001
    T = [[S[i][j] - (tau if i == j else I(0)) for j in range(4)] for i in range(4)]
    print("pi", PI)
    print("log2", LOG2)
    print("log3", LOG3)
    print("gamma", GAMMA)
    print("logpi", LOGPI)
    print("kappa", KAPPA)
    print("ainf1", AINF[1])
    print("gamma9", gamma9)
    print("tau", tau)
    print("A intervals")
    for row in A:
        print("  ", " ".join(f"[{x.lo:.14E},{x.hi:.14E}]" for x in row))
    print("sigma diagonal")
    for m in modes:
        print(m, "cos", cos_i(kfreq(m) * L, PI), "sigma", sigma(m, m))
    print("T intervals")
    for row in T:
        print("  ", " ".join(f"[{x.lo:.14E},{x.hi:.14E}]" for x in row))
    piv = ldl_pivots(T)
    def encoded(x):
        return {"lo": str(x.lo), "hi": str(x.hi)}
    certificate = {
        "status": "external interval witness; operator and analytic tail bridge not Lean-verified",
        "precision": PREC, "J": 20, "K": 2001, "modes": list(modes),
        "gamma9": encoded(gamma9), "tau": encoded(tau),
        "head_matrix": [[encoded(x) for x in row] for row in A],
        "schur_lower_matrix": [[encoded(x) for x in row] for row in T],
        "ldl_pivots": [encoded(x) for x in piv],
        "positive_pivot_assertions": all(p.lo > 0 for p in piv),
    }
    Path(__file__).with_name("odd_endpoint_interval_witness.json").write_text(
        json.dumps(certificate, indent=2) + "\n")
    print("LDL pivots")
    for p in piv:
        print(f"  [{p.lo:.14E},{p.hi:.14E}]")
    if not all(p.lo > 0 for p in piv):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
```

## Interval regression tests

Filename: `test_interval_enclosures.py`.

```python
"""Exact rational regression tests for the repaired interval arithmetic.

These tests check selected enclosure operations, not the paper's operator theorem.
"""
from pathlib import Path
from decimal import Decimal, localcontext
from fractions import Fraction as F
from random import Random

source = (Path(__file__).parent / 'prime_cover_c2_odd_endpoint_repaired.py').read_text()
namespace = {}
# Load only definitions; avoid the expensive global numerical initialization.
exec(source.split('\nLOG2 =')[0], namespace)
I = namespace['I']

def contains(interval, exact):
    return F(interval.lo) <= exact <= F(interval.hi)

x = Decimal('1.123456789012345678901234567890123456789')
with localcontext() as context:
    context.prec = 28
    old_negation = -x
assert F(old_negation) != -F(x)  # Reproduces the old point-interval failure.
assert contains(-I(x), -F(x))

for n in range(1, 101):
    r = namespace['sqrt_i'](I(n))
    assert F(r.lo)**2 <= n <= F(r.hi)**2

rng = Random(20261116)
for j in range(200):
    a = Decimal(str(rng.randint(-10**30,10**30))).scaleb(-20)
    b = Decimal(str(rng.randint(1,10**30))).scaleb(-20)
    u, v = I(a), I(b)
    assert contains(u+v, F(a)+F(b))
    assert contains(u-v, F(a)-F(b))
    assert contains(u*v, F(a)*F(b))
    assert contains(u/v, F(a)/F(b))

print('Passed: negation regression, 100 square-root brackets, 800 exact arithmetic containment checks.')
```

## Wolfram checks

Filename: `wolfram_exact_checks.wl`.

```wolfram
(* Reproduce the exact finite checks used in the RH part 2 review.
   These computations corroborate, but do not replace, Lean verification. *)
a = {{1, 2}, {0, 1}, {1, 0}};
b = {{1, 0}, {1, 1}, {0, 1}};
h = {2, -1, 3};
g = Transpose[b].b;
c = Inverse[g].Transpose[a].h;
d = b.c;
headTail = <|"gram" -> g, "coefficient" -> c, "drift" -> d,
  "normalResidual" -> (Transpose[a].h - Transpose[b].d),
  "driftNormSquared" -> d.d|>;
k = Table[1/Max[i, j], {i, 5}, {j, 5}];
y = Array[v, 5];
brownian = <|"inverse" -> Inverse[k],
  "precisionDifference" -> Expand[y.Inverse[k].y -
    Sum[i (i + 1) (y[[i]] - y[[i + 1]])^2, {i, 4}] - 5 y[[5]]^2]|>;
blocks = {{{2, 0}, {0, 1}}, {{1, 0}, {0, 2}}, {{2, 1}, {1, 2}}};
localFits = {{0, 0}, {0, 1}, {1, 1}};
total = Total[blocks];
inv = Inverse[total];
source = Sum[blocks[[i]].localFits[[i]], {i, 3}];
common = inv.source;
actual = Sum[(localFits[[i]] - common).blocks[[i]].
  (localFits[[i]] - common), {i, 3}];
discarded = 1/2 Sum[(localFits[[i]] - localFits[[j]]).
  blocks[[i]].inv.blocks[[j]].(localFits[[i]] - localFits[[j]]),
  {i, 3}, {j, 3}];
threeBlock = <|"totalGram" -> total, "inverse" -> inv,
  "commonOptimizer" -> common, "actualMismatch" -> actual,
  "discardedPairwise" -> discarded, "signedDefect" -> actual - discarded|>;
<|"headTail" -> headTail, "brownian" -> brownian, "threeBlock" -> threeBlock|>
```

## Axiom audit

Filename: `axiom_guard_snippet.txt`.

```lean
import RiemannResearch.LinearAlgebra.ThreeBlockOptimizerObstruction
import RiemannResearch.LinearAlgebra.HeadTailDriftObstruction
import RiemannResearch.LinearAlgebra.ReciprocalMaxGreen
import RiemannResearch.Analysis.FiniteCoordinateDecoding
/-- info: 'RiemannResearch.LinearAlgebra.HeadTailDrift.attainable_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RiemannResearch.LinearAlgebra.HeadTailDrift.attainable_iff

/-- info: 'RiemannResearch.LinearAlgebra.HeadTailDrift.no_uniform_strict_angle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms RiemannResearch.LinearAlgebra.HeadTailDrift.no_uniform_strict_angle

/-- info: 'RiemannResearch.LinearAlgebra.HeadTailDrift.normal_minimizer_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms RiemannResearch.LinearAlgebra.HeadTailDrift.normal_minimizer_unique

/-- info: 'RiemannResearch.LinearAlgebra.WeightedGreen.applyGreen_applyInverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms RiemannResearch.LinearAlgebra.WeightedGreen.applyGreen_applyInverse

/-- info: 'RiemannResearch.LinearAlgebra.ReciprocalMaxGreen.brownian_energy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms RiemannResearch.LinearAlgebra.ReciprocalMaxGreen.brownian_energy

/-- info: 'RiemannResearch.LinearAlgebra.ReciprocalMaxGreen.brownian_inverse_energy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms RiemannResearch.LinearAlgebra.ReciprocalMaxGreen.brownian_inverse_energy

/-- info: 'RiemannResearch.Analysis.FiniteCoordinateDecoding.unique_of_error_budgets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms RiemannResearch.Analysis.FiniteCoordinateDecoding.unique_of_error_budgets

/-- info: 'RiemannResearch.LinearAlgebra.HeadTailDrift.normal_tail_energy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms RiemannResearch.LinearAlgebra.HeadTailDrift.normal_tail_energy

/-- info: 'RiemannResearch.LinearAlgebra.ThreeBlockOptimizerObstruction.gram_strictly_positive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms RiemannResearch.LinearAlgebra.ThreeBlockOptimizerObstruction.gram_strictly_positive

/-- info: 'RiemannResearch.LinearAlgebra.ThreeBlockOptimizerObstruction.exact_defect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms RiemannResearch.LinearAlgebra.ThreeBlockOptimizerObstruction.exact_defect
```

## Interval output

Filename: `odd_endpoint_repaired_output.txt`.

```text
pi [3.14159265358979323846264338327950288419716939937510582097494459230780, 3.14159265358979323846264338327950288419716939937510582097494459230783]
log2 [0.6931471805599453094172321214581765680755001343602552541206800094933936, 0.6931471805599453094172321214581765680755001343602552541206800094933938]
log3 [1.098612288668109691395245236922525704647490557822749451734694333637494, 1.098612288668109691395245236922525704647490557822749451734694333637496]
gamma [0.5772156649015328606065120900823964548390487851884425669170745818642000, 0.5772156649015328606065120935289823404766640971526454505419198050560801]
logpi [1.144729885849400174143427351353058711647294812915311571513623071472109, 1.144729885849400174143427351353058711647294812915311571513623071472178]
kappa [5.372183419225665582232957497449736312811428700872072811280209977970389, 5.372183419225665582232957500896322198449044012836275694905055201162356]
ainf1 [4.579381594518005437813941851701490497885499862458307058043110358160754, 4.579381597073672579199331959983550429228565935309206030883366370812604]
gamma9 [0.9198373676784107758480000272666018184380440809911528952445339076606937, 0.9198375746874492280645988015600421428640112938781725789301161540358848]
tau [0.003526236881559220389805097451274362818590704647676161919040479760119938, 0.003526236881559220389805097451274362818590704647676161919040479760119944]
A intervals
   [1.04215406656724E-1,1.04215409212391E-1] [-5.98341030274226E-2,-5.98341030274226E-2] [4.06593867028564E-2,4.06593867028564E-2] [-1.60539881145948E-1,-1.60539881145948E-1]
   [-5.98341030274226E-2,-5.98341030274226E-2] [5.93825972289104E-2,5.93826202299147E-2] [-3.10720285405732E-2,-3.10720285405732E-2] [1.80681036769654E-1,1.80681036769654E-1]
   [4.06593867028564E-2,4.06593867028564E-2] [-3.10720285405732E-2,-3.10720285405732E-2] [1.17214663338824E+0,1.17214669727992E+0] [-2.80420375589040E-1,-2.80420375589040E-1]
   [-1.60539881145948E-1,-1.60539881145948E-1] [1.80681036769654E-1,1.80681036769654E-1] [-2.80420375589040E-1,-2.80420375589040E-1] [1.14106722598211E+0,1.14106735120980E+0]
sigma diagonal
1 cos [-0.3998268685523656930393927289147076399141886483499945614464623565435166, -0.3998268685523656930393927289147076399141886483499945614464623565434206] sigma [-0.8786481520474376575739678829618314865315080546104551156508773482712374, -0.8786481520474376575739678829618314865315080546104551156508773482710914]
3 cos [0.9438128741797218937530090583173687770794740297586285590719573587548489, 0.9438128741797218937530090583173687770794740297586285590719573587548987] sigma [0.7667966074796896191125358651990640974346735228860375622526914066334736, 0.7667966074796896191125358651990640974346735228860375622526914066335477]
5 cos [-0.8842814189762354607614044058395210877898311654428151007838345797069428, -0.8842814189762354607614044058395210877898311654428151007838345797052201] sigma [-0.5932694470630604745553405778178859905780973522171298597710204837038989, -0.5932694470630604745553405778178859905780973522171298597710204837023994]
7 cos [0.2592996597553783881971916973063151681983661104567534361559303673790937, 0.2592996597553783881971916973063151681983661104567534361559303673796134] sigma [0.1035645195110334413962455318308115236412703969485698554095995135409782, 0.1035645195110334413962455318308115236412703969485698554095995135414191]
T intervals
   [8.38143661386905E-2,8.38143686943577E-2] [-4.29492488008240E-2,-4.29492488008240E-2] [2.31357683236247E-2,2.31357683236247E-2] [-1.50638231309994E-1,-1.50638231309994E-1]
   [-4.29492488008240E-2,-4.29492488008240E-2] [3.88879686575804E-2,3.88879916585846E-2] [-1.33478204327077E-2,-1.33478204327077E-2] [1.68452915582640E-1,1.68452915582640E-1]
   [2.31357683236247E-2,2.31357683236247E-2] [-1.33478204327077E-2,-1.33478204327077E-2] [1.14991522638739E+0,1.14991529027907E+0] [-2.64215843840200E-1,-2.64215843840200E-1]
   [-1.50638231309994E-1,-1.50638231309994E-1] [1.68452915582640E-1,1.68452915582640E-1] [-2.64215843840200E-1,-2.64215843840200E-1] [1.05289952869807E+0,1.05289965392576E+0]
LDL pivots
  [8.38143661386905E-2,8.38143686943577E-2]
  [1.68793553668386E-2,1.68793790389294E-2]
  [1.14339699333213E+0,1.14339705766748E+0]
  [2.48478474685090E-1,2.48479333400282E-1]
```
