# Actual all-conductor unit-signal dilation bridge

Date: 2026-10-18.
Scope: the actual complete inverse-square Q-Hilbert space and unrestricted
conductors. This continuation reuses QFloorDilation.lean; it does not construct
a second floor-dilation operator.

## Conclusion and remaining hypothesis

The actual polynomial detector is now a theorem with no additional arithmetic
hypothesis:

    2*(zetaTwo*e + ell)^2 <= (zetaTwo*e)^2.

Here e is the squared error of the actual limiting normalized optimizer against
the positive-even indicator, and ell is its physical value at 1. The detector
does not assert e=0. The scalar lower bound

    ell >= -zetaTwo*e/4

remains Open. In fact, the new checked results show that this lower bound is
equivalent to e=0, and that e=0 is equivalent to the constant belonging to the
closed all-conductor legal span. Thus this lower bound is a substantive closure
obligation, not a consequence of unconditional optimizer convergence.

## Objects and indexing

Write kappa=zeta(2), Q(n)=1/(kappa*n^2) for n>=1, and zero-extend all physical
sequences at 0. For N>=3 let

    V_N = span{g_2,...,g_N},       P_N = orthogonal projection onto V_N,
    r_N = 1-P_N 1,               delta_N = ||r_N||_Q^2,
    Y = 1_{positive even},        O = 1_{odd} = 2*g_2,
    t_N = 1-4*delta_N > 0,
    U_N = (P_N Y)/t_N,
    e_N = ||U_N-Y||_Q^2 = delta_N/t_N,
    ell_N = U_N(1) = -r_N(1)/t_N.

The existing Lean stage allConductorStage n is V_(n+3).
Consequently index 2*n+3 represents conductor cutoff 2*(n+3), not cutoff 2*n.
All new finite statements respect this shift.

The existing QFullResidueProjection coefficients c^(N) are the actual
inverse-Gram coefficients of P_N 1. They are not the coefficients of U_N.
With A_N=sum_(d=2)^N c_d^(N)/d, the new checked formulas give

    r_N(1) = 1-A_N,
    ell_N = (A_N-1)/t_N.

## What follows from the existing operator

QFloorDilation.lean already supplies:

- the continuous linear map (T_m f)(n)=f(floor(n/m));
- the exact atom identity T_m g_d=g_(m*d)-g_m/d;
- preservation of the unrestricted legal span and its closure;
- the complete squared-norm estimate ||T_m f||_Q^2 <= (2/m)||f||_Q^2.

The new bridge identifies allConductorSpace with that existing legal closure.
It also proves T_2 V_N is contained in V_(2N) from the existing atom identity.
The finite and infinite projection arguments therefore use actual legal
vectors, not an assumed invariant abstract model.

At m=2 the old norm estimate only gives ||T_2 f||^2<=||f||^2. Together with
projection orthogonality, that yields a weaker detector with coefficient 1
instead of 2. It does not supply the strict scalar separation needed here.

## The additional unconditional arithmetic calculation

QFloorDyadicEnergy.lean sharpens the existing operator's estimate by grouping
the entire inverse-square series into even/odd pairs. It first proves

    ||T_2 f||_Q^2 =
      sum_(k>=0) [Q(2*k)+Q(2*k+1)]*f(k)^2.

For k>=1, Q(2*k)=Q(k)/4 and Q(2*k+1)<=Q(k)/4. The k=0 contribution is zero
because f(0)=0. Therefore

    ||T_2 f||_Q^2 <= (1/2)*||f||_Q^2.

This uses elementary arithmetic of the weights only. It uses no cancellation,
RH assumption, sign condition on the residual, or finite truncation of the
Q norm. The operator itself is the pre-existing floorDilation.

## Exact head identity and the finite two-scale estimate

Let S and R be orthogonally complemented subspaces with T_2 S contained in R,
and let r_S=1-P_S 1, r_R=1-P_R 1. Since

    T_2 1 = 1-1_{n=1},

orthogonality gives the exact signed identity

    <r_R,T_2 r_S>_Q = delta_R-r_R(1)/kappa.

Cauchy--Schwarz and the dyadic energy bound then give

    [delta_R-r_R(1)/kappa]^2 <= delta_R*delta_S/2.

The formalization also retains the complete slack identity. With
h=delta_R-r_R(1)/kappa, a=||T_2 r_S||^2, and b=<r_R,T_2 r_S>:

    delta_R*delta_S/2-h^2
      = delta_R*(delta_S/2-a) + (delta_R*a-b^2).

The first term is the weighted dilation loss; the second is the
Cauchy--Schwarz loss. Both are nonnegative. No boundary term or signed
first-coordinate contribution has been discarded.

For S=V_N and R=V_(2N), put x=delta_(2N), y=delta_N,
z=t_(2N)*ell_(2N)/kappa. The actual finite inequality is

    (x+z)^2 <= x*y/2.

The existing scalar algebra is now connected to this actual provider. In
particular, the conditional finite bound

    ell_(2N) >= -kappa*e_(2N)/4 - epsilon

implies

    delta_(2N) <= (8/9)*delta_N
                  + (8/3)*t_(2N)*epsilon/kappa.

This implication is proved. Its displayed lower-bound hypothesis is not.

## The actual limiting polynomial detector

Take S=R=the closed all-conductor legal span. Its established invariance gives

    2*(kappa*delta-r(1))^2 <= kappa^2*delta^2.

The existing strict positivity t=1-4*delta>0 and the new physical first-coordinate
identity identify e=delta/t and ell=-r(1)/t. Dividing by t^2 gives the detector.
It is proved directly in the closed space; no rate of optimizer convergence
is required.

The checked consequences include

    ell <= 0,
    ell=0 iff e=0,
    e=0 iff 1 belongs to the closed all-conductor span,
    e=0 iff ell >= -kappa*e/4.

The remaining question is the scalar lower bound. The negative upper sign
ell<=0 alone does not settle it.

## A concrete inverse-Gram formulation of the open estimate

The finite scalar lower bound is exactly equivalent to

    A_N >= 1-kappa*delta_N/4-t_N*epsilon_N.

This equivalence is checked for the actual inverse-Gram coefficients and
complete Q projection errors. It gives a concrete signed coefficient
functional to estimate. A statement about a generic coefficient vector, a
truncated Gram matrix, or a squarefree-only optimizer would not discharge it.

## Cofinal subsequences and the rate obstruction

The new subsequence theorem assumes only:

1. an index sequence j -> n_j tending to infinity;
2. an additive allowance epsilon_j tending to zero;
3. eventually,
   ell_(n_j+3) >= -kappa*e_(n_j+3)/4-epsilon_j.

Under these explicit hypotheses, the limiting error is zero. Coordinate
convergence follows from the already established Hilbert convergence and
continuous evaluation, realized using qPoint 0. The theorem does not assume
a sign at every finite stage, consecutive dyadic contractions, or any
quantitative convergence rate. No provider of hypothesis 3 is established.

Burnol's Theorem 1.3 and the cutoff-preserving Q/Pareto comparison give the
external logarithmic lower-rate obstruction discussed in
UnitSignalLimit20261013.md. An eventual exact quarter allowance at every
dyadic cutoff would imply delta_(2^j*N0)<=(8/9)^j*delta_N0 and contradict that
lower bound. This is a restriction on proposed hypotheses, not a failure of
the finite implication.

This obstruction alone does not rule out sufficiently sparse nonchained
estimates or vanishing absolute slack. Such allowances still need proof.
The Burnol analytic lower bound is not newly kernel-proved here;
BurnolParetoTransfer.lean formalizes a transfer with that analytic input
explicit. No numerical experiment is used as a provider in this continuation.

## Squarefree limitation

The invariance used here belongs to the unrestricted span. For example,
T_2 g_2=g_4-g_2/2 introduces conductor 4. The current argument does not supply
invariance of a squarefree stage or its closed span. The squarefree dictionary
and all-conductor dictionary have not been interchanged.

## Verified declaration map

- QFloorDyadicEnergy.lean:
  floorDilation_two_norm_sq_exact,
  floorDilation_two_norm_sq_le_half.
- ZetaTwoUnitSignalDilation.lean:
  two_space_head_identity, two_space_slack_identity,
  allConductor_finite_two_scale, allConductor_normalized_two_scale,
  allConductor_finite_quarter_allowance,
  allConductor_optimizer_first_inverseGram,
  allConductor_quarter_allowance_iff_inverseGram,
  allConductorLimit_polynomial_detector,
  allConductorLimit_error_zero_iff_constant_mem,
  allConductorLimit_error_zero_iff_quarter_lower_bound,
  allConductorLimit_error_zero_of_subsequence_allowance.

Verification status is determined by the final server checkpoint and its
integrated-source validation, not by the presence of this document. Development server job job_KFfSvr5dXC0ISZL6lshGvYffrUhrroDE completed with
exit code 0. Six selected axiom reports contain only propext, Classical.choice,
and Quot.sound. The earlier dyadic energy check job_ppX4ntJ-puzz5QlIt2O1QLV12f8jUSKk
also completed with exit code 0.
Conditional theorem hypotheses remain hypotheses after a successful check.

## Next research obligation

Estimate A_N-1+kappa*delta_N/4 from below on a cofinal sequence, with an
absolute error tending to zero after division by t_N. Since t_N converges to
a strictly positive limit, this normalization does not conceal a vanishing
denominator. Retain the signed inverse-Gram functional and complete Q energy.

Any proposed proof should be checked against the equivalence above: an
unconditional provider would settle the constant-closure obligation. Optimizer
convergence, legality, and operator boundedness have now been discharged and
should not be mistaken for that remaining provider.

## Provenance

- User-provided unit-signal/dilation argument and this continuation request,
  especially the polynomial detector and scalar allowance strategy.
- Existing repository modules QFloorDilation.lean, ZetaTwoUnitSignal.lean,
  UnitSignalProjection.lean, UnitSignalTwoScale.lean, and
  QFullResidueProjection.lean are reused.
- J.-F. Burnol, A lower bound in an approximation problem involving the zeros
  of the Riemann zeta function, Theorem 1.3:
  https://arxiv.org/pdf/math/0103058 .
  This supports the external rate obstruction, not a new Lean analytic provider.

No proof of RH or claim of mathematical novelty is made.
