# Fourier bridge and signed energy: formalization scope

**Continuation update:** The actual periodization, its Fourier-to-Mellin
identification, and all positive-integer boundary samples are now proved in
`DyadicTentFourierReconstruction.lean` and `DyadicTentFourierSamples.lean`.
Arbitrary finite signed packets also have an exact Fourier `HasSum`.
The five-module, 60-theorem continuation is recorded in
`FourierTentContinuationStatus20260910.md`. The sections below record the
preceding 78-theorem checkpoint; its periodization stage is superseded by
this update. The infinite signed arithmetic bridge and uniform full energy
targets remain Open.

September 10, 2026. Source: the supplied terminal-tent handoff and
FourierBridgeUniformSignedEnergy20260910.md from this conversation.

This development formalizes substantial parts of the ordinary proof. It does
not yet give a Lean proof of the complete unconditional Fourier bridge or of
the final uniform boundary-energy theorem. An ordinary mathematical argument,
a checked conditional deduction, and a checked unconditional provider are
different statuses throughout this ledger.

The module set contains 78 public theorems across 15 new modules.
The final checkpoint and user-facing verification handoff record publication
and exact compiler evidence.

## Unconditional providers

The actual root tent has a complex Mellin integral
\[
\int_a^{a+2}\tau_a(x)x^{s-1}\,dx
=\frac{a^{s+1}-2(a+1)^{s+1}+(a+2)^{s+1}}{s(s+1)}
\]
for \(a>0\), \(s\ne0,-1\). Both affine pieces, interval integrability,
zero-frequency specialization, and the nonzero-frequency formula are proved.
The inverse-square bound is established for the actual integral, not assigned
as a property of a newly chosen coefficient sequence.

The concrete dyadic Mellin coefficients are defined using that integral.
Their zero mode is identified with the actual binary residue boundary, and
their nonzero modes satisfy an explicit inverse-square bound. Every fixed
coefficient row is absolutely summable over all integer frequencies, including
zero. The missing periodization identity is stated separately: these integral
coefficients are not simply declared to reconstruct the actual boundary steps.

The arithmetic identity uses the actual Möbius function:
\[
\alpha_\epsilon(n)=\sum_{d\mid n}\mu(d)d^{-\epsilon}
=\prod_{p\mid n}(1-p^{-\epsilon}),\qquad n\ne0.
\]
Positivity, the upper bound one, and the bound
\(\alpha_\epsilon(n)\le\epsilon\log n\) for \(n\ge2\) are proved.
The empty product and the signed atom at one are retained explicitly.

The actual real normalization satisfies
\[
\frac1\epsilon\le\zeta(1+\epsilon)\le1+\frac1\epsilon,\qquad
1-\epsilon\log3\le N_\epsilon\le1+\epsilon,
\]
in the project's real Dirichlet-series convention. In particular,
\[
|N_\epsilon|\le\frac32,\qquad
|N_\epsilon-1|\le(1+\log3)\epsilon
\quad(0<\epsilon\le1/2).
\]
These bounds use real integral comparison and exponentials, without a
quantitative Mertens hypothesis or a complex Laurent-expansion assumption.

Consequently, for the genuine signed coefficients
\(b_\epsilon(n)=N_\epsilon\alpha_\epsilon(n)-\mathbf1_{n=1}\),
the full weighted series is summable and obeys
\[
\sum_{n\ge1}\frac{b_\epsilon(n)^2}{n^2}
\le
\left((1+\log3)^2+36\right)
\left(\sum_{n\ge1}n^{-3/2}\right)\epsilon^2.
\]
This coefficient energy is distinct from the final boundary energy.

The negative-depth atomic shells vanish exactly at integer dilations.
Tent support, height, and uniqueness of a positive integer-indexed tent at
one point are also proved. The continuous compensator is not removed by
the atomic-vanishing theorem.

## Checked deductions with explicit analytic hypotheses

The scalar limit theorem uses a summable majorant uniform in the finite
cutoff, pointwise kernel limits, exact finite approximation identities, and
an independently known physical-coordinate limit. Tannery's theorem then
proves the limiting scalar HasSum identity. The cutoff majorant and the
physical approximation identities remain explicit premises.

The infinite cancellation theorem combines separately convergent main and
comparison Fourier series with the zero-frequency identity. It retains the
comparison and mean until their exact cancellation. Its actual-family
specialization uses the existing arithmetic remainder.

The full norm equals the entire signed Fourier boundary sum once the scalar
HasSum bridge is supplied. The finite-coordinate frequency limit and subsequent
outer boundary sum are justified in that order; no Hilbert-valued Fourier
limit or frequency diagonalization is assumed.

The complete Banach-space Abel assembly proves
\[
\|V(1)-(1-q)\sum_{j\ge0}q^jV(3^{j+1})\|
\le C\left(2+\frac{\epsilon\log3}{1-q}\right)\le4C
\]
from the integer-conductor bound
\(\|V(A)\|\le C(1+\epsilon\log A)\).
Absolute norm summability of the actual infinite orbit is included.
The application to the project's four norm/series obligations requires both
this conductor bound and the exact identification of its Banach vector with
the actual arithmetic remainder. A raw boundary \(\ell^2\) vector must first
be transported through the canonical boundary identification when this
Hilbert-space application is used.

The weak-convergence deduction is stated against every continuous linear
functional. It follows from eventual uniform norm boundedness, convergence
of the actual mean and boundary coordinates, and quotient membership.
It does not assume that coordinatewise convergence alone is norm convergence.

## Exact unproved providers

The concrete definitions in RH/DyadicFourierAnalyticTargets.lean fix:

- ClassicalQuantitativeMertensBound: the actual Möbius summatory bound
  \( |M(x)|\le Cx\exp(-c\sqrt{\log(2x)})\).
- DyadicUniformSignedArithmeticDiscrepancyBound: the uniform bound for the
  actual signed cumulative coefficients with the compensator
  \(\kappa_\epsilon(x-1)\), including the atom at one.
- DyadicSignedFourierBridge: HasSum of the concrete Mellin-coefficient and
  zeta-ratio terms equals each actual remainder coordinate.
- DyadicUniformSignedFourierEnergyBound: the complete signed Fourier energy,
  with summability included, is uniformly bounded.
- DyadicNormalizationRemainderUniformEnergyBound: the corresponding actual
  remainder norm is uniformly bounded.

These are proposition definitions, not axioms and not theorems asserting
their truth. The equivalence of the last two bounds is proved conditional
on the concrete Fourier bridge. No checked provider in this development
discharges the Fourier bridge or either final uniform energy proposition.

To complete the ordinary argument in Lean, the remaining work is:

1. Prove or import and audit the quantitative Möbius/Mertens theorem, then
   prove its uniform weighted partial-sum and hyperbola consequence.
2. Construct the full real log-periodic extension, identify its integer
   samples with the actual boundary steps, and prove Fourier reconstruction.
3. Establish the signed residue kernels, their continuation and uniform
   cutoff bounds, then instantiate the checked scalar limit theorem.
4. Complete the compensated shell norm construction, its large-depth estimates,
   the pole/constant corrections, and its actual Fourier identification.
5. Supply the arithmetic coordinate limits to instantiate weak convergence.
   Convexification and the unrestricted non-\(\ell^2\) counterexample also
   remain ordinary arguments in this conversation.

The external mathematical reference for the classical estimate is
[Lee and Leong, version 4](https://arxiv.org/abs/2208.06141v4).
Citing it does not make it a Lean provider.

The full complementary physical-energy and legal two-seed recovery
obligations toward RH remain separate. This development does not prove RH.

## Module map

| Module | Public theorems | Responsibility |
| --- | ---: | --- |
| Analysis/ComplexTentIntegral | 8 | Actual complex Mellin integral and decay |
| Analysis/IntegerTentSupport | 6 | Integer support and exact atomic cancellation |
| Analysis/AbelFourierCancellation | 3 | Infinite signed cancellation and finite-coordinate limit |
| Analysis/ScalarFourierLimit | 3 | Dominated scalar extraction |
| Analysis/LogarithmicAbelGrowth | 7 | Complete Banach Abel convergence and bounds |
| Analysis/WeakConvergenceDenseTests | 3 | Dense-test and continuous-dual convergence |
| RH/DampedMobiusCoefficients | 15 | Exact divisor/product identity and elementary bounds |
| RH/DampedMobiusCoefficientEnergy | 3 | Full weighted coefficient energy |
| RH/DyadicNormalizationElementaryBounds | 4 | Actual normalization and unconditional coefficient-energy provider |
| RH/DyadicTentMellinCoefficients | 6 | Concrete coefficients and binary boundary identification |
| RH/DyadicTentFourierSummability | 3 | Absolute coefficient-row summability |
| RH/DyadicFourierBoundaryEnergy | 5 | Actual complete energy transfer |
| RH/DyadicFourierAnalyticTargets | 5 | Concrete unproved targets and conditional implications |
| RH/DyadicLogarithmicAbelCriterion | 5 | Actual damping and norm-obligation application |
| RH/DyadicBoundaryWeakConvergence | 2 | Actual quotient weak-convergence criterion |
