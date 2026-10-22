# RH continuation: signed charges, exact screening, and physical primitives

Date: 2026-09-24. Starting repository commit: `ad6399ae8d486cdd669648d6f26af54aca77e20d`.
Source handoff: `LateralArithmeticSynthesis20260924.md`.

## Outcome

Unconditional RH was not proved. The continuation improves an unconditional
innovation bound, identifies exactly how full and tail-screened innovations
are related, and enlarges the PNT primitive test class. It does not provide
the signed arithmetic source accumulation or the actual residual regularity
that would imply RH.

The distinction between a verified implication and a verified provider of
its hypotheses is maintained throughout.

## 1. Stronger dyadic certificate

Let
\[
v_M=(M+2)\rho_{M+2}-(M+1)\rho_{M+1},\qquad
z_M=v_M-P_Mv_M,
\]
where P_M projects onto the actual finite legal space. Write R_K for the
reciprocal charge vector and define
\[
A_{L,M}=\sum_{j=0}^L2^{-j}R_{2^j(M+1)}.
\]
Each charge annihilates the finite legal space, and biorthogonality gives
\[
\langle A_{L,M},z_M\rangle=1,\qquad
1\leq\|A_{L,M}\|^2\|z_M\|^2.
\]
The signed tridiagonal correlations give the exact fixed-L limit
\[
\lim_{M\to\infty}\|A_{L,M}\|^2
=\frac{12+3\,4^{-L}}{\pi^2}.
\]
Consequently, for every c<pi^2/12, eventually ||z_M||^2>c. This improves
the previous uniform 1/42 bound in the limiting sense. The order is first
M, with L fixed, then L. No interchange or uniform cutoff rate is assumed.

Lean module: `RH/ReciprocalChargeGeometricInnovation.lean`.
Principal declarations: `geometricDyadicCharge_norm_sq_tendsto`,
`geometricDyadicCharge_full_innovation_product_lower`,
`consecutiveResidue_full_innovation_eventually_gt`.

## 2. The full and tail denominators are linked exactly

Set e=finiteHeadIndicator 1, so ||e||^2=1/2, and define
\[
E_M=\|e-P_Me\|^2=(K_M+2)^{-1},\qquad
s_M=\langle\operatorname{tail}v_M,Q_M\rangle.
\]
Let d_M be the actual screened tail vector, retaining its entire infinite
tail, and write D_M=||d_M||^2 and B_M=||z_M||^2. The exact identities are
\[
\boxed{B_M=D_M+E_Ms_M^2},\qquad
\boxed{D_M=B_M\frac{E_{M+1}}{E_M}}.
\]
For the vector argument, lift d_M back into the subspace with zero first
coordinate. If r_M=e-P_Me, then
\[
z_M=\operatorname{lift}(d_M)-s_Mr_M,
\qquad\langle\operatorname{lift}(d_M),r_M\rangle=0.
\]
The Lean proof represents this lift by an explicit finite combination and
uses projection uniqueness, avoiding any assumed inverse for the tail map.

The dyadic bound therefore gives, for every c<pi^2/12,
\[
D_M>c\frac{E_{M+1}}{E_M}\quad\hbox{eventually}.
\]
If density fails, E_M converges to a positive defect and that ratio tends
to one. In this case D_M>c eventually for every c<pi^2/12. The signed source
still needs independent arithmetic control; this consequence of nondensity
is not a contradiction.

Lean module: `RH/CanonicalMobiusScreeningBridge.lean`.
Principal declarations: `firstHead_full_innovation_energy`,
`consecutiveResidue_full_tail_screening_energy`,
`windowStepScreened_energy_eq_full_mul_error_ratio`,
`windowStepScreened_eventually_gt_error_ratio`,
`windowStepScreened_eventually_gt_of_not_density`.

## 3. Centering the physical primitive

For f in the physical Hilbert space write
\[
H_f(N)=\sum_{n=1}^N f_n,\qquad t_n=\operatorname{tailAverage}(f,n).
\]
Exact reconstruction gives
\[
f_n=(n+1)t_{n-1}-nt_n\quad(n\geq1),
\]
\[
\boxed{H_f(N)-LN=2\sum_{j=0}^{N-1}(t_j-L)-N(t_N-L)}.
\]
Both the sum and endpoint term matter. Weighted-tail information is not a
substitute for a bound on this physical primitive.

The proved PNT pairing with the constant vector permits arbitrary centering:
\[
\sum_{K\geq0}|H_f(K)-LK|
\frac{3+\tau(K+1)}{(K+1)(K+2)}<\infty
\quad\Longrightarrow\quad
\langle 1-\operatorname{rawMobius}_N,f\rangle\longrightarrow0.
\]
In particular, the bound
\[
|H_f(K)-LK|\leq C\frac{K+1}{\log(2(K+1))^p},\qquad p>2,
\]
is sufficient. For the actual limiting orthogonal residual r, the pairing
equals its fixed energy. Thus this bound for r implies r=0 and RH.
**The bound for r remains Open.** Neither its mean L nor its rate is proved.

Lean module: `RH/NaturalMobiusCenteredPrimitiveTests.lean`.
Principal declarations: `physicalPrimitive_centered_eq_tailAverage`,
`rawMobiusResidual_inner_tendsto_of_summable_centered_primitive`,
`riemannHypothesis_of_residual_centered_primitive_log_bound`.

## 4. Why these improvements still do not prove source divergence

The following exact scalar model satisfies all the displayed scalar
screening/capacity identities while having a positive limiting defect:
\[
E_M=\frac{M+2}{4(M+1)},\quad K_M=\frac{2M}{M+2},\quad B_M=1,
\]
\[
s_M^2=\frac{4(M+1)}{(M+2)^3},\qquad
D_M=\frac{(M+1)(M+3)}{(M+2)^2}.
\]
Direct algebra gives
\[
E_M=(K_M+2)^{-1},\quad B_M=D_M+E_Ms_M^2,
\quad D_M=B_ME_{M+1}/E_M,
\]
\[
K_{M+1}-K_M=\frac{s_M^2}{D_M}
=\frac4{(M+2)(M+3)}.
\]
Here K_M tends to 2 and E_M tends to 1/4 despite B_M=1. This is a scalar
compatibility example, **not the actual arithmetic sequence**. It shows why
these identities and innovation lower bounds alone cannot force divergence.

On the primitive side, square-summable differences of t_n permit
t_n=(n+1)^(1/4). The corresponding exact physical coordinates
\[
f_n=(n+1)n^{1/4}-n(n+1)^{1/4}
\]
belong to the weighted Hilbert space, but
\[
\lim_{N\to\infty}N^{-5/4}H_f(N)=3/5.
\]
No linear centering yields the required logarithmic envelope. This example
does not assert arithmetic orthogonality; it rules out the proposed generic
inference from Hilbert membership and tail Parseval alone.

The threshold p>2 is sharp for the unsigned divisor majorant. Dyadic blocks
a in [2^i,2^(i+1)), b in [2^j,2^(j+1)) in the exact double series
\[
\sum_n\frac{\tau(n)}{n\log(2n)^p}
=\sum_{a,b\geq1}\frac1{ab\log(2ab)^p}
\]
give divergence for 0<=p<=2; negative p is immediate. A weaker envelope
therefore requires additional cancellation, not the same positive majorant.

There is also a precise hypothetical zero obstruction. In the bilinear
Mellin convention, for 1/2<Re(s)<1 put
\[
z_s(n)=\frac{n(n+1)}s\bigl(n^{-s}-(n+1)^{-s}\bigr).
\]
This belongs to the weighted Hilbert space and its pairing with rho_m is
zeta(s)(1/m-m^(-s))/s. Thus a zero s in this half-strip supplies a legal
annihilator. Its physical primitive satisfies the exact formula
\[
H_s(N)=\frac1s\left(2\sum_{n=1}^N n^{1-s}-N(N+1)^{1-s}\right),
\]
and, for every L, N^(s-2)(H_s(N)-LN) tends to 1/(2-s). It therefore violates
the centered logarithmic bound. For the sesquilinear Hilbert convention use
the conjugate parameter in the representing vector. These formulas are
direct mathematical derivations, not Lean-verified zeta theorems in this
continuation. They do not assert that such a zero exists, or that the actual
residual has this asymptotic form.

## 5. Further mathematical extension: all integer dilations

This section is a derived argument, **not a Lean-verified theorem in this
continuation**. It identifies a feasible next unconditional extension.

For c_h(n)=1_{h|n} mu(n/h)/(n/h), the mixed-cutoff limit should be formalized
from the repository's scaled quotient-kernel theorem as
\[
\lim_{N\to\infty}\langle R_{aN},R_{bN}\rangle
=\sum_{n\geq1}c_a(n)c_b(n).
\]
With a'=a/gcd(a,b), b'=b/gcd(a,b), the right side equals
\[
\frac1{a'b'}\sum_{d\geq1}\frac{\mu(a'd)\mu(b'd)}{d^2}.
\]
The common-cutoff construction reverses a/g and b/g; the symmetric product
makes the covariance unchanged.

For the unit-signal certificate sum_(h<=D) R_(hN)/h, the resulting limiting
energy is exactly
\[
F_D=1+\sum_{n>D}\frac1{n^2}
\left(\sum_{h\mid n,\ h\leq D}\mu(n/h)\right)^2.
\]
The divisor identity handles n<=D. The summable majorant tau(n)^2/n^2
handles the rest, so F_D tends to 1. For example tau(n)^2<=d_4(n) and
sum d_4(n)/n^2=zeta(2)^4 prove summability. This would improve the full
innovation lower limit to 1. It still does not supply the missing source
accumulation, as the exact scalar example above demonstrates.

## 6. Literature and the precise stopping point

Manzur, Noor and Quintero, *A Hardy space approximation supporting zero-free
half-planes for the zeta-function*, arXiv:2606.16097, Theorem 3.1 proves the
raw approximation in Hardy half-planes with boundary alpha>1. The paper
does not prove the critical-boundary convergence or the physical residual
estimate used here: https://arxiv.org/html/2606.16097v1.

Calderaro, Manzur, Noor and Santos, *Orthogonality questions in the Hardy
space related to zeta-zeros*, supplies background on regularity exclusions
and weighted closure conditions: https://arxiv.org/html/2203.05030v3.
These are background sources, not imported assumptions discharging RH.

The exact remaining capacity obligation is still
\[
\sum_{M\geq1}\frac{s_M^2}{D_M}=+\infty,
\]
equivalently K_M tends to infinity and E_M tends to zero. The alternative
is an actual provider for the centered primitive criterion in Section 3.
Neither was established. PNT, denominator control, and dual charge norm
cancellation have not been converted into either provider.

## Verification and publication

The initial dyadic and centered-primitive candidate passed with exit code 0
and verified=true in `job_clLmCWUYNwEOFuDrYDQPzICzdluprFYR`.
The final coherent candidate, including all three modules and their
principal axiom checks, passed with exit code 0 and verified=true in
`job_f0uyO8G5y_m-oCmcM6HXRuhb7dbPNpVx`.
Printed dependencies contained only propext, Classical.choice and Quot.sound.
No sorry, admit, project-local axiom or unsafe declaration was introduced.
The final RH implication explicitly retains its centered primitive bound.
The repository checkpoint validates the affected modules before publishing;
the publication commit is recorded in this file's repository history.
