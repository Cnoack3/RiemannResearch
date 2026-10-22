# Stretched energy transfer to inverse-Gram corrections and residual tails

Continuation of commit a9ba272c87ab0654768e94598027f15b634b20af.
Source: the user's requested transfer audit, 28 September 2026, and existing
project projection, exact-head, and Cauchy--Schwarz identities. No mathematical
novelty is claimed.

## Normalization and the two different residuals

Repository stage M uses g_2,...,g_(M+1). Write P_M for its full Pareto
orthogonal projection, F_M=P_M 1, r_M=1-F_M, and E_M=||r_M||^2.
Let u_m be the fixed finite-support coefficient dual:
<g_d,u_m>=1_(d=m) and <1,u_m>=-mu(m). Its repository index is m-2.
The actual inverse-Gram correction is delta_(M,m)=c_(M,m)+mu(m).

The auxiliary boundary-corrected vector is
A_N=-sum_(d<=N) mu(d) g_d+(N+1)m_N g_(N+1).
It belongs to stage N and equals one at physical coordinates 1,...,N.

This A_N is NOT the natural residual called A_N in the historical
InverseGramCorrectionAttempt20260923.md. That older notation means
1+sum_(d<=N) mu(d)g_d. The new energy theorem cannot be substituted for
its norm without accounting for the boundary term.

Put Phi(N)=((6+log N)log(6+log N))^(1/11). The checked arithmetic provider
gives a>0, C>=0 and, eventually,
B_N=8+C N exp(-a Phi(N)) >= ||1-A_N||^2.
For any Hilbert vector v, let
T_N(v)=sum_(j>N) |v(j)|^2/[j(j+1)].
This is the complete physical tail, represented by hilbertTailShift.

## What transfers unconditionally

For N<=M and 2<=m<=N, exact head cancellation and self-adjoint projection give

delta_(M,m)=<1-A_N,P_M u_m>,

hence

|delta_(M,m)|^2 <= B_N T_N(P_M u_m).

The cutoff N can be chosen independently of the larger projection stage M.
The corresponding optimal-error estimate is

E_M^2 <= B_N T_N(r_M).

For every modulus d>=2, uniformly including d>N, one also obtains

|<1-A_N,g_d>|^2 <= 8/(N+1)+C exp(-a Phi(N)).

Here the factor N is removed because T_N(g_d)<=1/(N+1). This is an
unconditional uniform estimate for the boundary-corrected source.
It is not by itself an estimate after applying the inverse Gram matrix.

These bounds improve the previous linear energy multiplier to the checked
stretched multiplier. They retain an actual tail quantity; they do not
give an explicit decreasing numerical bound for delta or E_M alone.

The full norm of a fixed inverse-Gram dual is already bounded:

(G_M^(-1))_(m,m)=||P_M u_m||^2 <= ||u_m||^2.

The unresolved issue is the physical tail at the moving cutoff, not
unbounded total norm of that fixed dual. The norm of the whole inverse
matrix, or an absolute row sum, is a different quantity.

## Stronger necessary tails and a weaker sufficient hypothesis

Let z belong to the orthogonal complement of the closed legal span.
Orthogonality and the exact head give

|<z,1>|^2 <= B_N T_N(z).

Since T_N(z)->0, for every 0<b<a a nonzero constant pairing forces

N exp(-b Phi(N)) T_N(z) -> infinity.

In particular, with r=1-P_V1 and D=||r||^2, D>0 forces that divergence
for the actual limiting residual. This is a genuine unconditional
quantitative strengthening of the earlier N T_N(r)->infinity obstruction.

At any strictly smaller exponent b<a, boundedness along a cofinal
subsequence of N exp(-b Phi(N)) T_N(r) would suffice for D=0 and RH.
It allows cofinal tail size O(exp(b Phi(N))/N), which is weaker than
the earlier O(1/N) requirement. The arithmetic provider for this tail
upper bound is **Open**.

At the original exponent a, the smallest nonnegative-product hypothesis
directly sufficient in this argument is

liminf_(N->infinity) N exp(-a Phi(N)) T_N(r)=0.

For a fixed correction, the analogous direct condition is cofinally
arbitrarily small B_N T_N(P_Nu_m); existence of the correction limit
then identifies that limit as zero. No provider for it was found.

## Why the other checked routes do not close the gap

ResidueSchurLimits expresses coefficient convergence rates through the
actual remaining Schur gains, whose saturation remains open.
CanonicalMobiusScreeningBridge keeps an exact signed source and the
adjacent first-head error ratio. It supplies no estimate forcing source
accumulation or physical-tail decay. Coordinatewise decay before
matrix inversion is not a uniform bound on its pairing with a varying
inverse-Gram row.

The factor N remains in B_N. Hilbert membership only gives T_N(v)->0;
it supplies no rate capable of controlling this growing multiplier.
Neither this transfer nor a bounded fixed dual norm proves RH.

## Formalization

- RH/CanonicalMobiusStretchedCorrection.lean: exact two-cutoff pairing,
  correction and finite optimal-error tail bounds, stretched assembly,
  and fixed inverse-diagonal bound.
- RH/ParetoStretchedAnnihilatorTail.lean: stretched heavy-tail obstruction,
  cofinal bounded-tail implications, and the explicit residual-tail
  hypothesis sufficient for RH.

The Báez-Duarte normalization and its external analytic dependency are
unchanged. All new unconditional conclusions are assembled from checked
project arithmetic and Hilbert-space results.

## Verification

The combined proof passed serialized Lean job
job_Tq53P1rjTgVS8r4HBX-Sj6_fv0gai8mt with exit_code=0 and verified=true.
Axiom inspection of the uniform source, finite projection, inverse-Gram
correction, annihilator barrier, and sharp conditional RH assembly reports
only propext, Classical.choice, and Quot.sound.
The conditional theorem types explicitly retain their tail hypotheses.
The saved modules are additionally checked by the publication checkpoint.
