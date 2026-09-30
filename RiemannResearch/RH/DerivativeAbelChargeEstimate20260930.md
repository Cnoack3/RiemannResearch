# Exact signed Abel-charge continuation — 30 September 2026

Base: `4557e290be0a29eedeb87977edf7fafee0968254`.
The complete conductor-one CRT cancellation from that commit is accepted and
not reproved here.

**Outcome:** the actual Abel endpoint is proved to vanish unconditionally.
A direct finite two-gap lower estimate for the entire charge is proved, with
both square remainders retained in the exact identity. The zero-threshold
signed arithmetic provider remains open. This continuation does not prove RH.

## Exact normalized primitives

Stage n uses conductors 2,...,n+1. Let r_n = 1 - F_n, E_n = ||r_n||^2,
e_(n,d) = c_(n,d) + mu(d), and L_d = mobiusDifferenceCLM d.
For K <= n, P_n(K) = sum_(d=2)^(K+1) e_(n,d).

Write u_d for the existing Möbius Riesz vector and
\[
\mathcal R_N=\sum_{d=1}^N d^{-1}u_d,\qquad
B_N=\mathcal R_N-\frac1N\sum_{k=0}^{N-1}\mathcal R_k.
\]
At N=0 the Lean definitions give zero.

The new finite identity is
\[
\boxed{\langle B_N,f\rangle
=\frac1N\sum_{d=1}^N L_d(f).}
\]
The already established Balazard/PNT ingredients give ||R_N|| <= 7
and R_N weakly converging to zero. Cesaro subtraction then proves
\[
\boxed{\|B_N\|\le14,\qquad B_N\rightharpoonup0.}
\]
Therefore any strongly convergent moving vector f_j and any divergent cutoff
N_j satisfy <B_(N_j),f_j> -> 0, with no relative growth assumption.

Conductor one is NOT silently removed. The exact application is
\[
\boxed{
\frac{P_n(K)}{K+2}
=\frac{K+1}{K+2}\langle B_{K+1},r_n\rangle
-\frac{r_n(1)}{K+2}.}
\]
The complete scalar square, including its signed cross term and first-site
square, is `correctionPrimitive_normalized_square`. Its centered estimate is
\[
\left(\frac{P_n(K)+r_n(1)}{K+2}\right)^2
\le196\left(\frac{K+1}{K+2}\right)^2E_n.
\]
Strong convergence of r_n and the moving-kernel result prove
\[
\boxed{\frac{P_n(n)}{n+2}\longrightarrow0}
\]
without any RH-strength assumption or growing inverse-Gram norm estimate.
This is qualitative endpoint control; no effective projection-convergence
rate is asserted.

## Divisor form and the exact remaining harmonic sum

The finite signed divisor primitive is
\[
\mathcal P_n(K)=
\sum_{j=0}^{K-1}\sum_{d\mid j+2}
\mu\!\left(\frac{j+2}{d}\right)\Delta r_n(d).
\]
`correctionDivisorPrimitive_eq` uses the existing
`correctionPrimitive_eq_divisor_sum` to identify this with P_n(K) for K <= n.

Define
\[
S_n=\sum_{k=0}^{n-1}
\frac{\mathcal P_n(k+1)}{(k+2)(k+3)}.
\]
Every finite stage retains the endpoint:
\[
\boxed{A_n=\frac{\mathcal P_n(n)}{n+2}+S_n.}
\]
Only after proving the endpoint tends to zero do we obtain
\[
\boxed{
S_n\longrightarrow-r(1)
=-\left[(2-\sqrt2)D+
\frac{\sqrt2}{2}\left\|r-\frac{\sqrt2}{2}D_2r\right\|^2\right],
\qquad D=\|r\|^2.}
\]
No termwise positivity of the primitives or of the divisor summands is known.

The most economical remaining divisor-arithmetic provider is
\[
\boxed{
\forall\varepsilon>0\;\forall N\;
\exists n\ge N:\quad
\sum_{k=0}^{n-1}\frac1{(k+2)(k+3)}
\sum_{j=0}^{k}\sum_{d\mid j+2}
\mu\!\left(\frac{j+2}{d}\right)\Delta r_n(d)>-\varepsilon.}
\]
`signedDivisorPrimitiveSum_cofinal_iff_residual_zero` proves that this is
equivalent to residual zero. Consequently it closes the existing
`reciprocalCorrectionAbel_cofinal_iff_residual_zero` and implies RH.
**Open:** a provider of this signed inequality. The displayed equivalence
is a conditional research reduction, not a proof of its premise.

## Direct finite lower control of the complete charge

For b >= 0 set n = 2b+1 and t = 2n+1. Define
\[
W_n=\left\|r_n-\frac{\sqrt2}{2}D_2r_n\right\|^2,\qquad
Q_n=(2-\sqrt2)E_n+\frac{\sqrt2}{2}W_n,
\]
\[
J_b=\left\|(F_t-F_n)-\frac{\sqrt2}{2}D_2(F_n-F_b)\right\|^2.
\]
Q_n denotes the full dyadic residual square, not the projection capacity.

The complete finite equality is
\[
\boxed{
A_n=M_{n+1}-(2-\sqrt2)E_n-\frac{\sqrt2}{2}W_n
+\frac{\sqrt2}{2}(E_b-E_t-J_b),\qquad
M_N=\sum_{d=1}^N\frac{\mu(d)}d.}
\]
Both dyadic squares and both energy endpoints remain.
After assembling this signed balance, the already proved two-gap
Cauchy-Schwarz estimate yields
\[
(A_n+Q_n-M_{n+1})^2
\le2(E_b-E_n)(E_n-E_t),
\]
\[
\boxed{
A_n\ge M_{n+1}-Q_n-\sqrt{2(E_b-E_n)(E_n-E_t)}.}
\]
This is a direct charge bound, with no auxiliary test-cutoff/raw-Möbius error.
The product of adjacent energy drops is sharper than replacing it by their
sum. Its error tends to zero, while Q_n may have a nonzero limit.

## Sharp strict-fraction comparison boundary

The full finite square converges to r(1), and unconditionally
\[
A_n+Q_n\longrightarrow0.
\]
For ANY fixed theta < 1, the following remains an exact conditional reduction:
\[
\boxed{
[\forall\varepsilon>0\;\forall N\;
\exists n\ge N:\ A_n+\theta Q_n>-\varepsilon]
\quad\Longleftrightarrow\quad r=0.}
\]
In particular, even an arbitrarily small fixed improvement from theta=1
would close the sign problem. The target keeps the Abel endpoint,
the signed primitive sum, and the whole residual square together.
The limiting square is never discarded.

The coefficient-one statement is unconditional. No strict-fraction
arithmetic comparison is supplied here.

## CRT, Weil, large-sieve, and Li/Hadamard boundary

The complete CRT cancellation does not control the sign of the surviving
charge: its exact decomposition retains A_n/2. It supplies no justification
for removing A_n or Q_n.

The actual Weil comparison retains the reflected-difference square, which
can contribute negatively. The imported large-sieve bounds are upper square
energy bounds and provide no signed comparison to this charge without an
additional bridge. The actual Li criterion requires positivity of all
actual coefficients; that positivity has no provider here. None of these
is installed as an extra sign assumption or invoked to delete a square.

## Sources and verification

The reciprocal-kernel ingredient follows the repository's formalization of
Michel Balazard, *An arithmetical function related to Baez-Duarte's criterion
for the Riemann hypothesis*, Propositions 6–7:
https://arxiv.org/abs/1812.04309.
This reference supports the imported reciprocal-charge ingredient; the
primitive-kernel and scalar-charge assemblies were developed in this
continuation. No claim of mathematical novelty is made.

New modules: `RH/MobiusPrimitiveCharge.lean` and
`RH/DerivativeAbelChargeBounds.lean`.
Their important conclusions assume only the already established actual
projection, PNT, and Hilbert-space providers. The sign conditions remain
explicit hypotheses in the two conditional equivalences.

The coherent targeted Lean candidate completed with exit code 0, no warnings,
and `verified: true`. Five important endpoint axiom audits report only
`propext`, `Classical.choice`, and `Quot.sound`; no project-local or admitted
proof axiom occurs. A clean axiom list does not discharge the sign hypotheses
in the conditional theorem types.

Publication uses the change-aware checkpoint, which validates the new
modules and their local reverse dependents before committing and pushing.
The task's final checkpoint result is the authoritative publication/build
status; the isolated candidate check alone is not a full project build.

Reproduce the endpoint audit:

```lean
import RiemannResearch.RH.DerivativeAbelChargeBounds
open RiemannResearch.RH.Pareto
open CoefficientStabilization.DerivativeCompatibility
#print axioms primitiveChargeRiesz_inner_moving_tendsto_zero
#print axioms correctionPrimitive_endpoint_tendsto_zero
#print axioms reciprocalCorrectionAbel_doubleStage_lower
#print axioms signedDivisorPrimitiveSum_cofinal_iff_residual_zero
#print axioms reciprocalCorrectionAbel_strict_fraction_cofinal_iff_residual_zero
```
