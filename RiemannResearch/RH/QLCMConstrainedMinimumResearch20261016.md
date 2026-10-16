# LCM squarefree criterion: constrained Q minimum and capacity continuation

Date: 16 October 2026.

Source: the attached `Q_LCM_Periods_RH_Criterion_and_Research_Agenda_2026-10-16(1).md`,
especially Sections 7–8 and research priorities 1–2. This record identifies
the exact formalized portion; it does not claim that the entire LCM manuscript
or its external RH-to-squarefree-density implication has been formalized here.

## The formalized optimizer

Let Q(n)=1/(zeta(2)n²), g_d(n)=(n mod d)/d, and fix a head H. Put

\[
F_H^0=-\sum_{d=1}^{H}\mu(d)g_d,
\qquad S_H=\sum_{d=1}^{H}\frac{\mu(d)}d.
\]

The conductor-one atom vanishes and the nonsquarefree Möbius coefficients
vanish. `mobiusSeed_mem_squarefreeSpan` proves actual algebraic squarefree
legality. `mobiusSeed_head` proves, unconditionally,

\[
F_H^0(n)=1-nS_H\qquad(1\le n\le H).
\]

Choose a finite nonempty family of distinct legal conductors d_i>H. For the
squarefree application each d_i is squarefree. Define

\[
K_{ij}=\langle g_{d_i},g_{d_j}\rangle_Q,
\quad w_i=1/d_i,\quad f=1-F_H^0,\quad
\beta_i=\langle g_{d_i},f\rangle_Q.
\]

All norms and inner products use the complete infinite Q law. Distinct
conductors greater than one supply actual linear independence and hence the
Gram inverse. Let

\[
x_0=K^{-1}\beta,\qquad C=w^{\mathsf T}K^{-1}w>0,
\qquad m=S_H-w^{\mathsf T}x_0.
\]

The implemented coefficient vector is exactly

\[
x^*=x_0+\frac mC K^{-1}w.
\]

It satisfies w^T x*=S_H. The candidate F*=F_H^0+sum_i x_i* g_{d_i}
is algebraically squarefree legal and equals one at every positive site at
most H. No separate finite interpolation or legality provider is assumed.

The general scalar-constraint module proves feasibility, attained minimality,
and uniqueness of the free coefficient vector. Its full completion is

\[
\|f-\sum_i x_i g_{d_i}\|_Q^2
=\|f-\sum_i x_i^*g_{d_i}\|_Q^2
+\|\sum_i(x_i-x_i^*)g_{d_i}\|_Q^2
\quad(w^{\mathsf T}x=S_H).
\]

The actual constrained value is

\[
\mathcal E=\|f\|_Q^2-\beta^{\mathsf T}K^{-1}\beta+\frac{m^2}{C}.
\]

For d_i enumerating all free divisors of the stage radical, this is the
minimum in Section 8 of the source. A smaller family gives its own restricted
affine minimum and an upper bound for the full-stage minimum. Conductors may
vary and their number may grow with the head.

## Exact capacity identity and a necessary mismatch rate

For A=sum_i x_i g_{d_i}, put s=sum_i x_i/d_i. Since d_i>H,
A(n)=ns on the head. The exact energy identity is

\[
\|A\|_Q^2=\frac H{\zeta(2)}s^2+
\frac1{\zeta(2)}\sum_{n>H}\frac{|A(n)|^2}{n^2}.
\]

Apply this to the actual normal vector U=sum_i (K^{-1}w)_i g_{d_i}.
Its squared norm and head slope both equal C. Therefore

\[
\boxed{C=\frac H{\zeta(2)}C^2+\operatorname{Tail}_Q(U)}
\]

and, for H>0,

\[
\boxed{\frac1C=\frac H{\zeta(2)}+
\frac{\operatorname{Tail}_Q(U)}{C^2}},
\qquad 0<C\le\frac{\zeta(2)}H.
\]

Here Tail_Q is the complete nonnegative energy beyond H, including every
physical site. Lean's l2 coordinate n represents physical site n+1, and
`tailEnergy H` sums l2 coordinates n+H, so the endpoint convention is exact.

If the normalization penalty satisfies m²/C≤B, then

\[
H m^2\le\zeta(2)B.
\]

The same inequality follows from a bound on the entire constrained minimum,
because its unconstrained residual contribution is nonnegative. Thus uniform
boundedness requires m=O(H^{-1/2}). This necessary rate alone is insufficient:
C may be much smaller than zeta(2)/H, and the other residual term must also
be bounded.

This C is the large-conductor normalization capacity. It is different from
the centered target capacity in `QSquarefreeCapacity`, whose divergence is
equivalent to constant closure. There is no contradiction between the two
capacity statements. Seeking divergence of this full-Q normalization C as
H grows would conflict with the proved upper bound.

## Connection to RH and unresolved providers

`riemannHypothesis_of_bounded_minimumError` uses the explicit Möbius seed and
the actual optimizer above, with finite nonempty distinct squarefree families
above each head H. If their complete optimized errors are uniformly bounded,
it derives actual Mathlib `RiemannHypothesis` through the existing squarefree
bounded-exact-head theorem.

This is a **conditional research reduction**. Its open substantive provider
is the uniform bound on `minimumError`. No such bound is proved here; no RH
conclusion follows unconditionally. No RH-to-density premise or new axiom is
introduced. The LCM/radical arithmetic and the refined repeated-period
harmonic comparison from Sections 2–4 remain outside this continuation.

## Lean declarations and verification scope

- `Analysis/FiniteGramScalarConstraint.lean`: `scalar_source_completion`,
  `scalarCoefficients_source`, `scalarCoefficients_energy`,
  `scalarCoefficients_completion`, `scalarCoefficients_isLeast`,
  `scalarCoefficients_unique`.
- `RH/QLargeConductorCapacity.lean`: `linear_head_energy`, `synthesis_energy`,
  `capacity_head_tail`, `capacity_le_zetaTwo_div_head`,
  `inverse_capacity_head_tail`, `distinct_residue_capacity_bound`,
  `head_scaled_mismatch_le`, `scalar_optimizer_head_zero`,
  `constrained_mismatch_bound`.
- `RH/QSquarefreeConstrainedMinimum.lean`: `mobiusSeed_mem_squarefreeSpan`,
  `mobiusSeed_head`, `optimizer_mem_squarefreeSpan`, `optimizer_head`,
  `minimumError_formula`, `minimumError_completion`,
  `riemannHypothesis_of_bounded_minimumError`.

The assembled development snippet passed server check
`job_RtBzezMZmO3hwLJAwDzrXLqJS6qhuYY_` (exit code 0). Axiom inspection of the
actual minimum formula and RH consumer reports only `propext`,
`Classical.choice`, and `Quot.sound`. The capacity identity and general
completion also passed checks with those foundations. A successful snippet
is not a project publication certificate. Final publication is gated
by the server checkpoint's source audit and affected-module validation; its
job result and commit are reported in the accompanying session.

## Research agenda

1. Prove an arithmetic estimate for the signed mismatch m together with a
   lower bound for C on a chosen cofinal family. The proved capacity ceiling
   cannot provide this lower bound. Retain both terms in the exact minimum.
2. Remove the mandatory head rank-one form (H/zeta(2))ww^T before exploring
   tail capacities, preserving the simultaneous corresponding changes to
   beta and the seed energy. Any tail-matrix inverse requires its own actual
   independence proof. Tail capacity and full-Q capacity must remain distinct.
3. Instantiate the finite family by the free squarefree divisors of
   rad(lcm(1,...,M)); prove the conductor-set equality and stage quantifiers.
   Permit M to grow independently of H.
4. Formalize the scalar repeated-period harmonic inequality and transfer it
   to complete Q errors and finite physical optima. This is measurement
   control, and does not supply uniform boundedness of the actual minimum.
5. Use finite computations to reject coefficient ansatzes while retaining
   exact Q Gram cross terms, source signs, and conditioning information.
   Finite success does not establish a cofinal bound.
