# Dyadic regularization: verification continuation

September 10, 2026.

Source: `DyadicRegularizedNormFormalization20260910(1).md`, supplied by the user,
and the preserved ordinary argument `norm_obligation_proved.md`, (N1)--(N31).
The starting published source is commit
`1526ebaa80a3bc2af1284cccaf3042ee0860b913`.

## Scope

This continuation strengthens the formalization of the actual weighted Hilbert
space and its dyadic quotient. It does not prove the unconditional norm bound
(N2), the required Mellin limits, or RH. The analytic assumptions in the
conditional declarations are ordinary theorem parameters, not axioms; their
presence must be checked in theorem types as well as in axiom reports.

## Recovery and the remaining full energy

`RH/DyadicTailRecovery.lean` constructs the finite triadic space using every
positive integer dilation at least X, its projected image, and its norm closure.
Every raw lift belongs to the project's actual legal seed space and vanishes
at all coordinates below X.

For a convergent actual arithmetic series, the regularized family belongs to
the projected legal closure. Scalar inner-product limits against its orthogonal
complement then put the projected target in that closure. The finite-lift
recovery theorem yields, for every positive delta, an actual finite signed
legal lift whose projection is within delta of the target.

The projected integer steps generate the full tail quotient densely, as proved
by recovering each coordinate from two consecutive step pairings. Thus the
concrete scalar limits for all d at least X imply the density conclusion (N4).
The scalar limits themselves remain an analytic provider. The proof uses
closed-subspace duality and does not need a separate Mazur-lemma construction;
it does not claim a convex-combination algorithm for the original rectangles.

For every quotient target u and every raw lift f, the exact identity is

\[
\|u-f\|^2=\|u-Q_Xf\|^2+\|f-Q_Xf\|^2.
\]

The complementary term remains fully present. Small projected error alone
therefore supplies no full-space approximation conclusion.

## A complete operator critical-norm provider

`RH/DyadicCriticalResolvent.lean` constructs the convergent physical series
Hf=sum_j (T_2^*/2)^j f for every vector f. With D=I-T_2T_2^*/2, it proves

\[
QDHf=Qf,\qquad
\|Qf\|^2=\tfrac12\|DHf\|^2,\qquad
\langle Qf,Qg\rangle=\tfrac12\langle DHf,DHg\rangle.
\]

All operators are the actual weighted Hilbert operators, and convergence is
proved internally. These theorems have no additional analytic hypotheses.
They supply a complete operator realization of the critical norm. Identifying
it with the specific boundary martingale formula (N5), or directly proving the
required arithmetic estimates in this representation, remains to be done.

## A finite critical-norm provider

`RH/DyadicFiniteCriticalNorm.lean` constructs the actual norm-convergent series
L(u)=sum_j (T_2/2)^j u. If T_2^*u=0, then

\[
Qu=\tfrac12 L(u),\qquad \|Qu\|^2=\tfrac12\|u\|^2.
\]

Let D=I-T_2T_2^*/2 and H_N f=sum_{j<N}2^(-j)(T_2^*)^j f.
The exact finite reconstruction retains the terminal term:

\[
QDH_Nf=Qf-2^{-N}Q(T_2^*)^Nf.
\]

The physical coordinate formula shows that support below 2^N makes this
terminal term zero. Hence actual finite-supported vectors satisfy

\[
\|Qf\|^2=\tfrac12\|DH_Nf\|^2,
\qquad
\langle Qf,Qg\rangle=\tfrac12\langle DH_Nf,DH_Mg\rangle.
\]

This supplies exact finite norm and Gram data in the original weighted Hilbert
space. It does not yet provide the full boundary isometry, its completion, or
the uniform step-orbit and Mobius estimates.

## A proved obstruction for triadic lifts

`RH/DyadicTriadicComplementObstruction.lean` specializes the established Mellin
obstruction to the actual residue-3 vector. It proves a fixed positive delta
such that every finite triadic lift f satisfies

\[
\delta-\|1-Q_1f\|^2\le\|f-Q_1f\|^2.
\]

Thus projected recovery forces the complementary energy to remain bounded
away from zero. There is no zeta-zero or RH assumption. This does not refute
quotient recovery; it proves that the second seed's signed cancellation is
essential for a full-space completion.

For two actual channels u,v, the complete error splits into projected error,
the two complementary squared norms, and twice their signed inner product.
The proof retains that mixed term exactly. No cancellation bound is supplied.

## Exact step energies

`RH/DyadicStepMeanIdentity.lean` proves that every projected integer step has
mean one, multiplication of its integer index by two preserves the vector,
and its centered Gram matrix is obtained by subtracting one from every entry.
For arbitrary finite signed coefficients, the complete approximation error is

\[
\left\|\sum_i c_iV_{m_i}-1\right\|^2
=\left(\sum_i c_i-1\right)^2+
\sum_{i,j}c_ic_j\bigl(\langle V_{m_i},V_{m_j}\rangle-1\bigr).
\]

No mixed term is dropped and no coefficient positivity is assumed. The finite
Abel cutoff has mean 1-r^N and retains the exact scalar error r^(2N).
Whenever the actual infinite vector series is summable, its normalized Abel
average has mean one and norm squared equal to one plus its squared distance
from the constant. These identities do not prove the missing upper Gram bound.

## Explicit norm assembly

`RH/DyadicRegularizedGramAssembly.lean` connects the concrete Gram estimates,
arithmetic series convergence, and actual remainder bound to both the base and
all-tail norm bounds, with the same explicit constant

\[
C=\left(\|Q1\|+\|(\log2)^{-1}QR_2\|+\sqrt{D+2A}+R\right)^2.
\]

The theorem retains all X,d,epsilon quantifiers and both convergence conclusions.
Its inputs remain: the actual arithmetic series convergence; diagonal growth;
a nonnegative off-diagonal majorant with linear prefix sums; and the actual
O(sqrt(epsilon)) remainder estimate. It assumes no arbitrary transfer identity
or projection.

## Still required

The critical fold/martingale identification and all needed estimates; quantitative
uniform Mobius cancellation and parameter differentiation; the concrete seed
potential and orbit growth; logarithmic step Gram and continued-fraction prefix
estimates; the infinite arithmetic identification; the normalization remainder;
and the actual Mellin or separating-inner-product limits remain necessary for
the unconditional argument. Quotient recovery alone does not construct a full
legal approximation to the constant using the two seeds.

## Highest-leverage next proof targets

1. Turn the finite critical norm/Gram formula into the uniform logarithmic
   bounds for the concrete triadic step orbit. Finite-support nilpotence and
   the operator norm identity now have checked providers.
2. Supply uniform arithmetic cancellation, the infinite arithmetic
   identification, and the actual remainder estimate. These are the central
   remaining analytic providers for unconditional (N2).
3. Construct the second seed channel and control the complete complementary
   energy, including its signed interaction with the triadic lift. Trying to
   drive the triadic complementary energy alone to zero contradicts the
   positive-gap theorem.

The existing declaration `riemannHypothesis_of_twoSeed_closure` converts
membership of `hilbertOne` in the full actual `{2,3}` legal closure into RH.
This continuation does not establish that membership.

## Verification

The combined source check for all six new modules and 28 existing source
dependencies passed in job `job_Ncdsg69dhIPqfGKSso1h6z-02ZIBx6hI`:
`verified: true`, exit code 0, compilation time 18.587 seconds.

Checked-source SHA-256:
`8737bb4b50b041daa5d0af81ebfe58c1b3a2245dbf5e10d4198a77b92a42b4df`.

Fifteen audited endpoints, including the complete norm/Gram identities,
conditional recovery and norm assembly, and the unconditional complementary
gap, depend only on `propext`, `Classical.choice`, and `Quot.sound`.
There are no added `sorry`, `admit`, project axioms, or unsafe declarations.
The source check emitted only style/deprecation warnings from existing
dependencies. Those warnings do not discharge or add mathematical hypotheses.

The repository checkpoint validates the separated new modules and affected
dependents before publication. The published commit is reported with this
document. This remains a partial formalization of the ordinary argument:
neither unconditional (N2) nor RH is established.
