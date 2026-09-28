# Coefficient-mass obstruction audit — 28 September 2026

Continuation of commit 27303d288368384e410b08f84a8693d5ee44b5ab.
This checkpoint completes the previously written obstruction in Lean,
with critical-zero existence retained as an explicit premise.

## Result and exact formal status

**Kernel-checked conditional obstruction.** For every positive arithmetic
exponent a and nonnegative C satisfying the displayed canonical-energy
estimate, and every s with

    s.re = 1/2,   riemannZeta s = 0,

there is one fixed d in {2,3} such that

    for every b<a:
      exp(-b Phi(n)) B_(n,d)^2 -> +infinity.

Here B is the actual projected inverse-column l1 mass. The theorem selects
d before b; separate cofinal sets or separate exponents for different
columns do not evade the conclusion.

The specialization
`exists_coefficient_mass_stretched_barrier_of_critical_zero` obtains a>0
from `canonicalMobiusResidual_eventual_stretched_energy`. Its only
domain-specific input is the displayed critical-line zero. There is no
remaining unproved quantitative estimate in that specialization.

**Open formalization dependency:** existence of such a zero. No checked
provider was located in the repository or inspected Mathlib declarations.
It remains a premise, never an axiom. The obstruction is therefore not
claimed here as a premise-free Lean refutation.

RH is neither assumed nor proved. RH remains **Open**.
The earlier sufficient implications from mass or concentration budgets to
zero residual and RH remain correct. Under the critical-zero premise, their
global strict-margin hypotheses are impossible; this does not contradict RH.
The endpoint b=a and direct signed physical-tail criteria are not refuted.

## Notation

    V_n = span(g_2,...,g_(n+1)),  P_n = orthogonal projection onto V_n,
    h_d = coefficientRiesz d,
    p_(n,d) = P_n h_d,  q_(n,d) = h_d-p_(n,d),
    B_(n,d) = projectedDualCoefficientMass n d,
    T_N = hilbertOne-canonicalMobiusHilbert N,
    Phi(n) = ((6+log n) log(6+log n))^(1/11).

The physical norm is

    ||f||^2 = sum_(j>=1) f(j)^2/[j(j+1)].

The existing unconditional arithmetic provider supplies a>0, C>=0 and
eventually

    ||T_N||^2 <= 8+C N exp(-a Phi(N)).

## Actual critical-line cutoff

Module: `RH/ParetoCriticalMellinCutoff.lean`.

For the actual bounded-step Mellin integral

    M_s(f) = integral_(1 to infinity) f(floor x) x^(-s-1) dx,

the theorem `paretoMellin_critical_cutoff` proves, for every R>0,

    |M_s(f)| <= ||f|| sqrt(R) + 2 C exp(-R/2),

assuming Re(s)=1/2 and |f(j)|<=C. R is the logarithmic cutoff; the
physical integral is split at exp(R).

The finite-head kernel energy is exactly R. Hilbert Cauchy--Schwarz gives
the head bound, while the complete infinite tail is bounded by integrating
C x^(-3/2). Bounded-step integrability and the union-of-intervals identity
justify the literal split. No boundary functional is assumed continuous
on the whole Hilbert space.

## A fixed nonzero Mellin witness

Module: `RH/ProjectedDualMellinWitness.lean`.

The exact finite physical sequences are h_2=(4,-6,0,...) and
h_3=(2,6,-12,0,...). The checked formulas are

    s M_s(h_2) = 4-10x+6y,
    s M_s(h_3) = 2+4x-18y+12x^2,
    x=2^(-s), y=3^(-s).

Three times the first numerator plus the second is
2(6x-7)(x-1). For Re(s)>0, |x|<1, so both Mellin values cannot vanish.
The declaration `coefficientRiesz_two_or_three_mellin_ne_zero` establishes
this without a zeta-zero assumption.

At a zeta zero with Re(s)>0 and s!=1, bounded Mellin linearity and the
residue zeta identity give M_s(f)=0 for every f in V_n. Consequently

    M_s(q_(n,d)) = M_s(h_d).

The same module proves the actual physical bounds

    |p_(n,d)(j)| <= B_(n,d),
    |q_(n,d)(j)| <= 12+B_(n,d)  for d=2 or d=3.

Select the nonzero Mellin witness once. With L=|M_s(h_d)|>0, the critical
cutoff therefore yields, simultaneously for every n and R>0,

    L <= ||q_(n,d)|| sqrt(R) + 2(12+B_(n,d)) exp(-R/2).

## Finite approximation and unchanged arithmetic exponent

The previously checked `RH/ProjectedDualProjectionError.lean` gives

    ||q_(n,2)||^4 <= 270 B_(n,2)^2 ||T_N||^2/(N+1),
    ||q_(n,3)||^4 <= 530 B_(n,3)^2 ||T_N||^2/(N+1),

with the exact finite conductor conditions. These use the short syntheses

    h_2 = 4*1 - 5*D_2 1 + 2*D_3 1,
    h_3 = 2*1 + 2*D_2 1 - 6*D_3 1 + 3*D_4 1.

The new `Analysis/StretchedCutoffRescaling.lean` proves

    Phi(n) <= Phi(n/8)+log 16  for n>=8.

Its general helper `logProductPower_sub_le_sub` derives a Lipschitz
comparison from the existing decreasing profile/argument ratio and the
profile's upper bound by its argument. Also Phi(n)=o(log n), so the
constant term 8/(n/8+1) is absorbed by exp(-a Phi(n)). Thus

    ||T_(n/8)||^2/(n/8+1) <= D exp(-a Phi(n))

eventually, with D=64 exp(6)+C exp(a log 16). The exponent a is preserved,
not weakened. For n>=24, N=n/8 meets both conductor conditions.

`projectedDualError_two_three_eventual_stretched_fourth` consequently gives

    ||q_(n,d)||^4 <= D' B_(n,d)^2 exp(-a Phi(n)),  d=2,3,

eventually, for D'=530D.

## Scalar contradiction and cofinality

Module: `Analysis/CriticalCutoffGrowth.lean`.

The general theorem `mass_barrier_of_critical_cutoff` combines an eventual
fourth-power error envelope with the nonzero literal cutoff inequality.

If exp(-b Phi(n)) B_(n,d)^2 were bounded cofinally by K, extract a cofinal
sequence of those indices. Put c=|b|+1 and R=c Phi(n). Along that sequence,

    [||q|| sqrt(R)]^4 <= D' K c^2 Phi(n)^2 exp(-(a-b) Phi(n)) -> 0.

The square of the tail term is bounded by

    8*12^2 exp(-c Phi(n)) + 8 K exp(-(c-b) Phi(n)) -> 0.

Both a-b and c-b are positive. This contradicts L>0. The proof works for
every real K and b<a, including negative b, without assuming an eventual
bound or intersecting different columns' cofinal sets.

## Final declarations and Bound(*)

Module: `RH/ProjectedDualMassObstruction.lean`.

- `coefficient_mass_stretched_barrier_of_critical_zero`: divergence with
  the arithmetic energy estimate explicit.
- `exists_coefficient_mass_stretched_barrier_of_critical_zero`: the
  checked arithmetic provider discharges that estimate and supplies a>0.
- `not_cofinal_stretched_coefficient_mass_of_critical_zero`: refutes the
  global mass budget, even allowing a different b_d<a for every d>1.
- `not_cofinal_stretched_l2_concentration_of_critical_zero`: refutes the
  global effective-support/l2 budget under the same explicit zero premise.

For the last theorem, leakage outside I is retained:

    sum_(i outside I) c_i^2 <= rho L,
    kappa = |I| + |I-complement| rho.

The existing finite inequalities imply B^2<=2 kappa L at the same indices.
Hence a cofinal bound on exp(-b Phi(n)) kappa L would supply the prohibited
mass bound. This is the precise obstruction to the strict-margin Bound(*).

The endpoint b=a is outside this contradiction. In particular, the theorem
does not refute the existing endpoint liminf-zero sufficient criteria.

## Other established results and remaining research route

`RH/ProjectedDualSchurAsymptotics.lean` still proves unconditionally

    B_(n,d)^2=o(S_n),  S_n=sum_(j<n) A_j^2,
    A_j^2 >= (j+2)/2,  S_n >= n(n+3)/4.

The lower bound on the absolute Schur majorant does not turn that relative
little-o statement into an upper bound on the actual mass.

The direct signed physical-tail condition remains an Open sufficient
provider:

    n exp(-b Phi(n)) projectedDualTailEnergy n d
      is cofinally bounded for each fixed d>1, with b<a.

Its existing checked implication yields zero residual and RH. Absolute
column mass loses cancellations retained by this signed-tail criterion.
This checkpoint proves neither that provider nor another sufficient
condition for RH.

The obstruction's principal declarations report only `propext`,
`Classical.choice`, and `Quot.sound`. No sorry, admit, unsafe declaration,
or project-local axiom is added. The explicit critical-zero premise is
visible in theorem types; it is not reported by `#print axioms`.
