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

## Newly checked continuation: diagonal growth and actual dyadic repair

This verification pass starts from published commit
`b35307048c266efb8c75f352a4690a7c5355d5c1`.
The concrete diagonal-growth assumption is now discharged. The complete
vanishing-damping norm bound, the required weak/Mellin limits, and RH remain
unproved.

### Exact physical refinement and logarithmic diagonal growth

`RH/DyadicStepBoundary.lean` and `RH/DyadicStepLogBound.lean`
construct the actual two-coordinate boundary
\[
d_l=-l e_{2l}+(l+1)e_{2l+1},\qquad l\ge1.
\]
They prove \(T_2^*d_l=0\), \(\|d_l\|^2=1/2\),
\(\|Qd_l\|^2=1/4\), and orthogonality of \(Qd_l\) to every
projected step \(V_m=QT_m1\) with \(m\le2l\).

The complete recurrence retains its signed cancellation:
\[
\|V_{2l+1}\|^2
=\frac14+\frac{\|V_l\|^2+\|V_{l+1}\|^2}{2}
-\frac{\|V_l-V_{l+1}\|^2}{4}.
\]
Together with \(V_{2l}=V_l\), this proves
\[
0<m\le2^N\quad\Longrightarrow\quad
\|V_m\|^2\le1+\frac N4.
\]
In particular,
\[
\|V_{3^{j+1}}\|^2
\le1+\frac{j+1}{2}\le\frac32(j+1).
\]

Checked endpoints:
`dyadicProjectedStep_odd_norm_sq_signed`,
`dyadicProjectedStep_norm_sq_le_depth`,
`dyadicProjectedStep_triadic_diagonal`.
These have no additional analytic hypotheses. This is a dyadic-depth
(ceiling-logarithmic) bound; no sharper floor-log formula is claimed verified.

The same concrete growth proves
`dyadicStepAbelOrbit_series_summable`
for every positive damping. Thus the existing mean-one and norm/variance
theorems for this step average now have an unconditional summability provider.
This is not convergence of the product-index Möbius arithmetic series.

Both norm-assembly endpoints in
`RH/DyadicRegularizedGramAssembly.lean`
now use the proved diagonal internally with \(D=3/2\). Their theorem types
no longer require a diagonal-growth hypothesis or a supplied constant \(D\).
The off-diagonal majorant, its linear prefix bound, the actual Möbius-series
convergence, and the normalization remainder remain explicit assumptions.

### Quantitative critical-norm truncation

`RH/DyadicCriticalApproximation.lean` proves, for every physical vector,
\[
Qf-QDH_Nf=Q(T_2^*/2)^Nf,\qquad
\|Qf-QDH_Nf\|^2\le2^{-N}\|f\|^2.
\]
It proves norm convergence of \(QDH_Nf\) to \(Qf\), and the exact energy
identity
\[
\|Qf\|^2
=\tfrac12\|DH_Nf\|^2
+2\langle QDH_Nf,Q(T_2^*/2)^Nf\rangle
+\|Q(T_2^*/2)^Nf\|^2.
\]
For an integer step with \(m\le2^N\), using \(N+K\) levels gives squared
error at most \(2^{-K}\). The signed terminal interaction is retained before
the error is bounded.

Checked endpoints:
`dyadicCriticalPacket_norm_sq_eq`,
`dyadicCriticalPacket_error_norm_sq_le`,
`dyadicCriticalPacket_tendsto`,
`dyadicProjectedStep_packet_error_norm_sq_le_of_le_two_pow`.

### A concrete second-seed correction family

`RH/DyadicCenteredSeedRepair.lean` constructs, for all positive integer
dilations, the actual finite dyadic legal vectors
\[
G_m=T_mR_2-R_2=(T_2-I)R_m,\qquad QG_m=0.
\]
For \(m\ge2\), the physical coordinate \(G_m(1)=-1\), so the norm is nonzero.
For every vector \(f\), the actual minimizing scalar is
\[
t_*=-\frac{\langle f,G_m\rangle}{\|G_m\|^2}.
\]
Lean proves the complete-square identity, minimality, and the exact gain
\[
\|1-(f+t_*G_m)\|^2
=\|1-f\|^2-\frac{\langle f,G_m\rangle^2}{\|G_m\|^2}.
\]
It also proves that precisely the same gain occurs in the complementary
energy, while the projected vector stays unchanged. For finite triadic \(f\),
the corrected vector is an actual finite legal two-seed lift.

For arbitrary finite signed coefficients, the checked identity is
\[
\begin{aligned}
\left\|1-\left(f+\sum_i c_iG_{m_i}\right)\right\|^2
={}&\|1-Qf\|^2+\|f-Qf\|^2\\
&+2\sum_i c_i\langle f,G_{m_i}\rangle
+\sum_{i,j}c_ic_j\langle G_{m_i},G_{m_j}\rangle.
\end{aligned}
\]
No coefficient positivity is assumed and no cross term is omitted.
The finite dyadic channel is also decomposed exactly into a scalar multiple
of \(R_2\) plus centered corrections; its projection depends only on the sum
of its coefficients.

Checked endpoints:
`dyadicCenteredSeed_optimal_complementary_energy`,
`finite_dyadic_lift_centered_decomposition`,
`finite_dyadic_lift_projection`,
`finite_centered_dyadic_repair_mem_twoSeed`,
`finite_centered_dyadic_repair_error_sq`.

The remaining repair target is now concrete: along actual finite triadic lifts
whose projected error tends to zero, find finite signed centered dyadic
corrections for which the complete complementary quadratic expression above
also tends to zero. Individual scalar gains do not prove that exhaustion.
Containment of all of \(\ker Q\) in the centered dyadic closure has not been
proved and must not be silently assumed.

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
the uniform Abel/mixed-Gram and Mobius estimates.

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
from the constant. These identities do not prove the missing off-diagonal Gram/prefix bound.
The diagonal growth and step-series summability are now supplied above.

## Explicit norm assembly

`RH/DyadicRegularizedGramAssembly.lean` connects the concrete Gram estimates,
arithmetic series convergence, and actual remainder bound to both the base and
all-tail norm bounds, with the same explicit constant

\[
C=\left(\|Q1\|+\|(\log2)^{-1}QR_2\|+\sqrt{3/2+2A}+R\right)^2.
\]

The theorem retains all X,d,epsilon quantifiers and both convergence conclusions.
Its remaining inputs are: the actual arithmetic series convergence;
a nonnegative off-diagonal majorant with linear prefix sums; and the actual
O(sqrt(epsilon)) remainder estimate. It assumes no arbitrary transfer identity
or projection.

## Still required

The critical fold/martingale identification and all needed estimates; quantitative
uniform Mobius cancellation and parameter differentiation; the concrete seed
potential and orbit growth; off-diagonal step Gram and continued-fraction prefix
estimates; the infinite arithmetic identification; the normalization remainder;
and the actual Mellin or separating-inner-product limits remain necessary for
the unconditional argument. Quotient recovery alone does not construct a full
legal approximation to the constant using the two seeds.

## Highest-leverage next proof targets

1. Prove the actual off-diagonal Gram majorant and its linear prefix bound.
   The logarithmic diagonal estimate is now proved with D = 3/2; the exact
   odd-step recurrence retains the adjacent-step difference energy.
2. Supply uniform arithmetic cancellation, the infinite arithmetic
   identification, and the actual remainder estimate. These are the central
   remaining analytic providers for unconditional (N2).
3. Use the constructed centered dyadic correction family to exhaust the
   complete complementary quadratic energy, including every signed mixed
   term. Trying to
   drive the triadic complementary energy alone to zero contradicts the
   positive-gap theorem.

The existing declaration `riemannHypothesis_of_twoSeed_closure` converts
membership of `hilbertOne` in the full actual `{2,3}` legal closure into RH.
This continuation does not establish that membership.

## Earlier verification

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

## Current verification evidence

The final combined source check for the step boundary, logarithmic diagonal,
centered repair, and strengthened assembly passed in
`job_fz5g6EneRkvk0yBiMb1Wb3sSBt_Kat9z`:
`verified: true`, exit code 0, compilation time 6.920 seconds,
with no diagnostic warnings or errors.

Checked-source SHA-256:
`def7a780ae7713d765372423c5df8c0fd3efde76391c9aa6b8a84ce72fc031b0`.

The critical-approximation source check passed separately in
`job_xfWXrn2br_HD9p8nj1gDWoEUYReptO1I`:
`verified: true`, exit code 0, compilation time 2.918 seconds.

Checked-source SHA-256:
`12ace3e9151be19692c1a67631feb916a0f8c4c78c55c67551bc01c0ee445231`.

Audited endpoints use only `propext`, `Classical.choice`, and `Quot.sound`.
The actual strengthened assembly type was printed and inspected: its
off-diagonal/prefix, arithmetic convergence, and remainder hypotheses remain.
There are no added placeholder proofs or project-local axioms.

These source checks are distinct from the final repository checkpoint,
which validates the separated modules and affected dependents before
publication. Its published commit is reported with the delivered document.
Neither unconditional (N2) nor RH has been established.
