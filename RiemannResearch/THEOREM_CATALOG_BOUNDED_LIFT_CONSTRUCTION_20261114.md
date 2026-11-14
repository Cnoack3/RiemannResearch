# Bounded legal D-lifts: explicit construction and weak compactness

Date: 2026-11-14

## Conclusion

The requested existence with BOTH uniform full-Q norm boundedness and D-image
convergence to D1 has not been established unconditionally. This continuation
constructs explicit smoothed approximants, verifies their quantitative source
and image estimates, and proves that any successful finite bounded lift can
be replaced by a fixed explicit sequence in the unit ball.

No unconditional RH theorem is claimed.

## Notation

All physical indices n are positive. Put Q(n)=1/(zeta(2)n^2),
P(n)=1/(n(n+1)), g_k(n)={n/k}, and
S=span{g_k:k>=2}, V=closure_Q S.
Here Df(n)=f(n)/n. B remains exclusively multiplication by dQ/dP.

## Explicit arithmetic construction

For N>=1, set

v_N = -sum_{d=1}^N mu(d) g_d
      + (N+1)(sum_{d=1}^N mu(d)/d) g_{N+1}.

The conductor-one term is zero. The existing declaration
QMobiusExactHead.exactHead is this exact finite legal vector.
Its exact head identity is v_N(n)=1 for 1<=n<=N.

The new module RH/QMobiusSmoothedLift.lean proves:

| Declaration in QMobiusSmoothedLift | Exact conclusion |
| --- | --- |
| exactHead_D_error_sq_le | ||D(v_N-1)||_Q^2 <= 16/(zeta(2)N), for N>0 |
| exactHead_source_sq_le | ||v_N||_Q^2 <= 8N/zeta(2), for N>0 |
| exactHead_D_tendsto | Dv_N -> D1 in the full Q norm |
| exactHead_scaled_D_error_tendsto | N ||D(v_N-1)||_Q^2 -> 0 |
| exactHead_source_sublinear | ||v_N||_Q^2/N -> 0 |
| exactHead_weak_subsequence_of_bounded_cofinal | Any cofinal choice with a common source-norm bound has a weak subsequence converging to 1; 1 is in V |
| exactHead_norm_tendsto_atTop_of_not_RH | If RH is false, ||v_N||_Q -> infinity |

The last two rate limits reuse the repository's checked PNT estimates. They
have no remaining Mertens-bound hypothesis. The bounds concern the complete
infinite Q norm, not a truncated coordinate sum.

The primary identity behind the bounds is the existing exact cost
J_alpha(v)=||D(v-1)||_Q^2+alpha||v||_Q^2.
The existing estimate at alpha=N^-2 retains both nonnegative terms.
Neither a growing upper bound nor the stronger o(N) source-energy bound
gives a uniform bound or a bounded cofinal subsequence.

## What weak-star compactness actually proves

Assume H(j)->infinity and ||v_{H(j)}||_Q<=C for all j.
In the complete separable space V, the radius-C ball is weakly compact.
Equivalently one can use the Riesz representation map into the continuous
dual and Banach--Alaoglu. Extract a subsequence converging weakly to f in V
with ||f||<=C.

For every z in H,
<z,Dv_{H(phi(j))}>_Q -> <z,Df>_Q
by weak convergence and continuity of the functional v |-> <z,Dv>_Q.
The unconditional strong convergence of the D-images gives the same scalar
limit <z,D1>_Q. Hence Df=D1, and injectivity gives f=1.

This argument requires a single bound before extracting a subsequence.
Compactness of the D-images, finite-head agreement, or a distinct bounded
family does not furnish that source bound. Compactness of D itself is not
needed in this implication.

## A canonical sequence with the norm bound already proved

Let W_N=span(g_2,...,g_{N+1}) and

u_N = Pi^Q_{W_N} 1
    = sum_i (G_N^{-1} b_N)_i g_{i+2},

where G_N and b_N use the complete Q inner products. The existing finite Gram
invertibility makes the formula explicit; it is QFullResidueProjection.candidate.

The new module RH/QFiniteBoundedLift.lean proves, in namespace
QFullResidueProjection:

| Declaration | Exact conclusion |
| --- | --- |
| candidate_norm_le_one | ||u_N||_Q <= 1 for every N |
| bounded_finite_D_lift_iff_unit_strong_lift | A finite legal uniformly bounded D-lift of D1 exists iff a finite legal unit-ball sequence converging strongly to 1 exists |
| candidate_D_tendsto_iff_mem | Du_N -> D1 iff 1 is in V |

In the forward implication of the middle theorem, the unit-ball witness is
exactly u_N; no further choice of coefficients or subsequences is needed.
This normalizes the existential radius. It does NOT normalize each term of
the Mobius family and thereby preserve its target.

Unconditionally u_N -> Pi^Q_V 1, so Du_N -> D Pi^Q_V 1. The outstanding
statement is D Pi^Q_V 1 = D1, equivalently Pi^Q_V 1=1.

Thus the two unconditional constructions supply complementary properties:

| Family | Uniform full-Q norm bound | D-images converge to D1 |
| --- | --- | --- |
| Explicit Mobius v_N | Open; current bound is o(N) for squared norm | Proved |
| Inverse-Gram projections u_N | Proved, radius 1 | Open |

## RH boundary and next arithmetic target

The existing theorem
QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
proves 1 in V -> RH. The new existence equivalences do not discharge that
premise or assert a converse RH -> 1 in V.

An exact remaining scalar target is the complete projection remainder:
||1-u_N||_Q^2 = 1 - b_N^T G_N^{-1} b_N.
The known limit is ||1-Pi_V^Q 1||_Q^2, not automatically zero.
Proving this limit zero supplies the unit-ball sequence without a separate
norm estimate. Alternatively, a bounded cofinal full-Q energy estimate for
the explicit Mobius heads would close the weak-compactness argument.

## Literature context

L. Baez-Duarte, New versions of the Nyman-Beurling criterion for the Riemann
hypothesis, IJMMS 31:7 (2002), 387-406,
https://doi.org/10.1155/S0161171202013248, Section 4, Proposition 4.13.
This is context for the failure of strong L2 convergence of certain natural
Mobius approximants. The paper distinguishes nonconvergence from claims
about subsequences. Its continuous-space statement is not silently imported
as a theorem about this discrete Q family. In particular, failure of strong
convergence alone would not rule out boundedness and weak convergence.

## Verification

The coherent candidate containing all ten new declarations passed the queued
Bazel/BuildBuddy snippet job job_ncEYFB4e_S4LTa1_flLqXNDj_BtwepUW:
verified=true, exit code 0, server verification time 54.535 seconds.

The saved modules were then imported together in focused acceptance job
job_owFsd_yXTwjaYrNcjERlgc_iZmGj_uog. This succeeded with backend=bazel,
verified=true and exit code 0; the complete job took 39.034 seconds.
This checked both saved files and their transitive imports. The final
full-project checkpoint is separate and its terminal publication result
must be reported with the published commit.

No proof placeholders, new axioms, or unsafe declarations are introduced.
