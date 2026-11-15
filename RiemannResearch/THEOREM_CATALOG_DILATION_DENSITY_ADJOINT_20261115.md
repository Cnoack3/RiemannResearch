# Dilation, density, and two-adjoint RH criteria

Date: 2026-11-15.
Source: Christian Noack's dilation/B discussion and request to formalize the interactions and RH equivalences, 14–15 November 2026.
Base revision: 485da6cdff8a886556631afa26fe2e387d6e3462.

## Normalization and scope

The Hilbert space is the actual complete Pareto-weighted real space:
P(n)=1/[n(n+1)] for n>=1, with the physical value at zero anchored to zero.
Q(n)=1/[zeta(2)n^2]. All P/Q identities use toPareto and its inverse, preserving physical sequences.

- U_m f(n)=sqrt(m) f(floor(n/m)).
- The existing hilbertDilationContinuous m is D_m=sqrt(m) U_m.
- B=dQ/dP=(1+1/n)/zeta(2). This is QDensityMetric.B, **not** the historical shifted-reciprocal operator with the same short name.
- ParetoDensityDilation.densityP realizes this physical multiplier in P.
- V is Pareto.CoefficientStabilization.closedSpace, the closure of the span of every g_k, k>=2.
- r_N=1-Pi_(span(g_2,...,g_(N+1)))1, and r=1-Pi_V1. Every norm is the complete Hilbert norm.

This work proves integer-dilation identities, estimates, and density criteria.
It does not implement the enlarged continuous translation model, Stone's theorem,
or a strongly continuous unitary group. U_m is not surjective on the original space for m>1.

## Operator interactions — unconditional

Module: RiemannResearch/RH/ParetoDensityDilation.lean.
Namespace: RiemannResearch.RH.ParetoDensityDilation.

| Declaration | Content |
| --- | --- |
| normalizedP_sequence | Exact normalized floor-dilation formula. |
| normalizedP_norm | U_m is an isometry in P. |
| normalizedP_comp, normalizedP_one | U_m U_n=U_(mn) and U_1=I. |
| normalizedP_head_zero | U_m f vanishes at every physical n<m. |
| normalizedP_not_surjective | U_m is not surjective when m>1. |
| normalizedP_adjoint_left_inverse | U_m* U_m=I. |
| normalizedP_adjoint_norm_le | U_m* contracts the P norm. |
| normalized_toPareto | P and Q dilations preserve the same physical sequences under transport. |
| densityP_toPareto | The two realizations of B agree under transport. |
| density_commutator_sequence | Full floor-sensitive coordinate formula for [B,U_m]. |
| density_adjoint_intertwining | J B_Q U_(m,Q)*=U_(m,P)* J B_Q, where J=toPareto. |
| adjoint_density_formula | U_(m,Q)*=B_Q^(-1) J^(-1) U_(m,P)* J B_Q. |
| density_normalized_error_norm_le | norm((B-cI)U_m f) <= norm(f)/[zeta(2)m], c=1/zeta(2). |
| compressed_density_error_norm_le | norm(U_m* B U_m f-c f) <= norm(f)/[zeta(2)m]. |
| compressed_density_opNorm_le | norm(U_m* B U_m-cI) <= 1/[zeta(2)m]. |
| density_orthogonal_transport_iff, density_orthogonal_transport | For every Q submodule S, J B_Q(S^(perp Q))=(JS)^(perp P). |

For n>=m the coordinate commutator is
\[
 [B,U_m]f(n)=\frac{\sqrt m}{\zeta(2)}
 \left(\frac1n-\frac1{\lfloor n/m\rfloor}\right)f(\lfloor n/m\rfloor).
\]
For n<m it is zero. Lean's all-natural-index statement uses totalized division and f(0)=0.

## Leakage on the legal closure — unconditional

Module: RiemannResearch/RH/DilationDensityLeakage.lean.
Namespace: RiemannResearch.RH.Pareto.DilationDensityLeakage.

- normalized_mem_closedSpace: U_m V is contained in V.
- leakage: the actual bounded operator C=Pi_(V^perp) B.
- leakage_normalized_eq: C U_m v=Pi_(V^perp)(B-cI)U_m v for v in V.
- leakage_normalized_norm_le:
  \[
  \|C U_m v\|\le\frac{\|v\|}{\zeta(2)m}\quad(v\in V).
  \]

This controls dilated vectors. It does not prove C=0 on V or supply adjoint invariance of V.

## Exact density criteria — unconditional

Module: RiemannResearch/RH/DilationAdjointCriterion.lean.
Namespace: RiemannResearch.RH.Pareto.DilationAdjointCriterion.

The proof uses the existing hilbertDilationAdjoint_two_three_fixed_iff:
the common fixed space of D_2* and D_3* is the span of the constant target.
The actual residual lies in V^perp, and g_2 in V has positive mean,
so a constant residual must be zero.

| Declaration | Equivalence |
| --- | --- |
| residual_zero_iff_two_adjoint_fixed | r=0 iff D_2*r=r and D_3*r=r. |
| totality_iff_two_projection_adjoint_mem | V=H iff both D_2*Pi_V1 and D_3*Pi_V1 belong to V. |
| totality_iff_two_adjoint_invariant | V=H iff D_2*V and D_3*V are contained in V. |
| normalized_adjoint_apply | U_m*=(1/sqrt(m))D_m*. |
| totality_iff_two_normalized_adjoint_invariant | V=H iff U_2*V and U_3*V are contained in V. |
| finiteResidual_tendsto | The actual finite projection residuals converge to r. |
| defectNormSum_tendsto | Their two-adjoint defect sums converge to the defect sum of r. |
| totality_iff_residual_defects_tendsto_zero | V=H iff norm(D_2*r_N-r_N)+norm(D_3*r_N-r_N) tends to zero. |

For the normalized adjoint, the residual eigenvalue is 1/sqrt(m), not 1:
D_m*r_N-r_N=sqrt(m)[U_m*r_N-r_N/sqrt(m)].

## RH implication and the explicit converse boundary

No extra analytic provider is required for:
- riemannHypothesis_of_two_adjoint_invariant;
- riemannHypothesis_of_two_normalized_adjoint_invariant;
- riemannHypothesis_of_two_projection_adjoint_mem;
- riemannHypothesis_of_residual_defects_tendsto_zero.

Both conclude Mathlib's actual RiemannHypothesis through the existing Mellin bridge.

The following equivalences retain the explicit argument
hBD : Pareto.BaezDuarte.BaezDuarteMobiusApproximation:
- riemannHypothesis_iff_totality;
- riemannHypothesis_iff_two_projection_adjoint_mem;
- riemannHypothesis_iff_two_adjoint_invariant;
- riemannHypothesis_iff_two_normalized_adjoint_invariant;
- riemannHypothesis_iff_residual_defects_tendsto_zero.

Thus, **under that explicit published analytic provider**, the formalized criterion is
\[
 \mathrm{RH}
 \iff U_2^*V\subseteq V\ \text{and}\ U_3^*V\subseteq V
 \iff \|D_2^*r_N-r_N\|+\|D_3^*r_N-r_N\|\longrightarrow0.
\]
The RH-to-density implication is not newly proved here.
The provider remains a theorem parameter, not an added axiom or an assumed proof of RH.
Its definition asks for a specific natural-error Möbius approximation under RH;
MertensBaezDuarteConverse transfers it to squarefree closure, which is included in V.

Published background:
- Bagchi, Theorem 1: https://arxiv.org/abs/math/0607733.
- Xue, Corollary 1.5 (all-integer adjoint invariance): https://arxiv.org/abs/1911.04029.

The two-adjoint reduction uses the repository's separately proved rigidity theorem.

## Remaining proof obligations

1. Prove the Baez-Duarte analytic provider in Lean to remove its argument from the RH iff theorems.
2. Prove actual two-adjoint invariance, the two fitted-target memberships, or the actual residual-defect zero limit to obtain an unconditional RH proof.
3. Do not replace the complete residual defect by finite coordinate tests without a valid tail estimate.
4. The O(1/m) leakage and compression bounds alone do not establish these arithmetic obligations.

## Verification

The final focused audit succeeded with Bazel and BuildBuddy:
- Job: job_yuiL4xJt2RhyIW97FkFqlGmjVP3HsDBP.
- Request SHA-256: 226750a4152310d801ae6d060aeea0f5d4a2fdc46da9b136df48b403298c6177.
- Build: https://app.buildbuddy.io/invocation/2cdfa56b-b3c2-4664-ae26-12f6b0e78fe8.
- Twelve guarded axiom checks enforce exactly propext, Classical.choice, and Quot.sound.
- No sorry/admit, custom axiom, or assumed RH proof was introduced.

The workspace checkpoint separately gates publication on the source audit,
complete Bazel build, integration validation, and successful commit/push.
Its result is the authoritative record for the final commit and full-build receipt.

The modules are exported by RiemannResearch.lean. No pre-existing theorem or provider is weakened.
