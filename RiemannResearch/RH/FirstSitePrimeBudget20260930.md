# First-site capacity: exact prime budget and the remaining provider

Date: 2026-09-30.
Base: Cnoack3/RiemannResearch e9f76732570540900138d9e6b01c43ee4188c3d6.
Module: RH/ParetoFirstSitePrimeBudget.lean.

Follow-up: [RH consequences and the angular channel](FirstSiteRHAngularContinuation20260930.md).
The fixed-fraction conditions below remain valid conditional implications,
but the later classical Burnol/PNT comparison rules out their arithmetic
hypotheses. The exact total-budget target remains valid; the later angular
reduction retains the complete signed square and every nonprime gain.

The first-site provider remains open. This continuation proves exact
unconditional budget identities and quantitative conditional growth criteria.
It does not redo the offsite transfer or claim RH.

## The actual fixed-rank problem

Write \(C_n=\mathrm{tailCapacity}(n)\). Stage \(n\) uses
\(g_2,\ldots,g_{n+1}\). The existing inverseSource witness attains the
optimal finite-trial ratio exactly. Hence the remaining task is
\(C_n\to+\infty\), not further coefficient search.

The existing exact identities are
\[
\Delta_n=\frac{\mathrm{vacancy}(n)}2=\frac1{C_n+2},\qquad
C_{n+1}-C_n=\frac{\eta_n^2}{\sigma_n},\qquad \sigma_n>0.
\]
The determinant ratio is
\[
\frac{\det(\mathrm{tailGram}_n)}{\det(\mathrm{fullGram}_n)}
 =\frac2{C_n+2}.
\]
These formulas identify the target but do not supply capacity divergence.

## A positive source that already diverges

For budget index \(j\), set \(p=j+3\), \(P=(j+2)!\),
\[
 \delta_j=\mathrm{coprimePrimeDefect}(P,p)>0,\qquad
 \kappa_j=
 \langle\mathrm{tailInnovation}(j+1),
 \mathrm{infiniteCoprimeCertificate}(P)-\mathrm{tailMinimum}(j+1)\rangle.
\]
At prime \(p\), the existing exact factorial/CRT identity gives
\[
 \eta_{j+1}=\delta_j+\kappa_j.
\]
Both the innovation and the certificate retain the complete physical tail.
The old-block screening retains every signed Gram correlation.

Define, with all sums over \(0\le j<N\),
\[
\begin{aligned}
 U_N&=\sum_{p\ {\rm prime}}\frac{\delta_j^2}{\sigma_{j+1}},&
 V_N&=\sum_{p\ {\rm prime}}\frac{\kappa_j^2}{\sigma_{j+1}},\\
 X_N&=\sum_{p\ {\rm prime}}\frac{\delta_j\kappa_j}{\sigma_{j+1}},&
 J_N&=\sum_{p\ {\rm nonprime}}\frac{\eta_{j+1}^2}{\sigma_{j+1}},\\
 G_N&=\sum_{p\ {\rm prime}}\frac{\eta_{j+1}^2}{\sigma_{j+1}},&
 A_N&=V_N+2X_N+J_N.
\end{aligned}
\]
Here \(A_N\) is this note's combined signed budget, not an Abel charge or
an earlier projection notation.

The existing source theorem proves \(U_N\to+\infty\), using
\(\delta_j^2/\sigma_{j+1}\ge 1/(8p)\) at prime stages and divergence
of the reciprocal-prime sum. This divergence concerns \(U_N\), not \(C_n\).

## New exact full accounting

The new module proves
\[
 \boxed{C_{N+1}=C_1+G_N+J_N
                 =C_1+U_N+V_N+2X_N+J_N
                 =C_1+U_N+A_N.}
\]
The initial modulus-two capacity, every nonprime increment, both prime
squares and the signed mixed term are present.

Declarations:
- capacity_eq_prime_composite_budget
- factorialPrimeGain_eq_signed_energy
- capacity_eq_prime_signed_budget

Monotonicity yields only
\[
 A_N\ge -U_N.
\]
The new primeSignedBudget_ratio_tendsto_of_capacity_bounded shows that
if \(C_n\) is bounded, necessarily
\[
 \frac{A_N}{U_N}\longrightarrow -1.
\]
The same conclusion is proved for a nonzero actual closed point residual.
This is a necessary condition for bounded capacity; it is not a converse.
A slowly diverging capacity could also have this normalized limit.

## A less restrictive sufficient provider than error summability

For any fixed \(\theta<1\) and finite real \(K\), it is enough to prove
\[
 \forall N_0\ \exists N\ge N_0:\qquad
 A_N\ge-\theta U_N-K.
\]
Indeed the exact identity then gives, at those stages,
\[
 C_{N+1}\ge C_1+(1-\theta)U_N-K.
\]
Since \(U_N\to+\infty\) and \(C_n\) is monotone, this forces
\(C_n\to+\infty\), hence \(\Delta_n\to0\).

This is formalized as tailCapacity_tendsto_of_prime_signed_fraction and
riemannHypothesis_of_prime_signed_fraction. The displayed signed inequality
is an explicit OPEN arithmetic hypothesis. No provider is supplied.
It requires no pointwise noncancellation at every prime, no summability
of \(\kappa_j^2/\sigma_{j+1}\), and no uniform inverse-Gram bound.
It is sufficient, not asserted to be necessary.

The weakest exact remaining estimate, without a prescribed rate, is
\[
 \boxed{\forall B\in\mathbb R\ \exists N:
 B<U_N+V_N+2X_N+J_N.}
\]
tailCapacity_tendsto_iff_prime_budget_unbounded proves its equivalence to
\(C_n\to+\infty\). This equivalence is a reduction, not a proof of the estimate.

## Tunable square completion

For every \(t>0\), define the complete nonnegative remainder
\[
 R_N(t)=\sum_{p\ {\rm prime}}
 \frac{(t\eta_{j+1}+\kappa_j)^2}{t\sigma_{j+1}}.
\]
The new exact identity is
\[
 \boxed{U_N+R_N(t)=(1+t)G_N+(1+t^{-1})V_N.}
\]
Only the subsequent inequality drops \(R_N(t)\) and uses
\(G_N\le C_{N+1}\):
\[
 U_N\le(1+t)C_{N+1}+(1+t^{-1})V_N.
\]
The declarations primeSourceBudget_young_completion and
primeSourceBudget_le_capacity_error preserve this order of equality
before estimation.

Consequently, for \(0\le\theta<1\), a cofinal bound
\[
 V_N\le\theta U_N+K
\]
also suffices for capacity divergence. The verified choice
\(t=(1+\theta)/(1-\theta)\) proves
tailCapacity_tendsto_of_prime_error_strict_fraction.
This bound allows nonsummable error energy. It remains an OPEN arithmetic
hypothesis, and the broader signed criterion above allows more cancellation.

## Why the examined structures do not yet close the provider

- Schur positivity permits a convergent sum of positive increments.
- The determinant ratio is exactly the same scalar capacity target.
- CRT/factorial source divergence is already established, but
  \(\eta=\delta+\kappa\) retains an uncontrolled signed correction.
- Dilation corrections give actual correlation squares. The existing
  canonical projection is orthogonal to its nontrivial dilations even in
  the nonzero-residual alternative, so a uniform positive dilation gain
  cannot be inferred from the dilation identities alone.
- The growing factorial certificates are reset at each stage. Their
  support escape and large norm do not themselves imply large primal
  capacity; all certificate-to-minimum gaps must remain in the accounting.

The next arithmetic task is therefore a signed aggregate comparison of
\(2X_N+V_N+J_N\) with the known divergent \(U_N\), preferably the cofinal
strict-fraction bound above, or the exact unbounded-budget condition.

## Verification and assumptions

Serialized isolated Lean verification of the complete candidate succeeded
with exit code 0. Axiom checks on the exact identities, scalar equivalence,
conditional growth criteria and bounded-capacity cancellation limit reported
only propext, Classical.choice and Quot.sound. The conditional theorem types
retain their arithmetic hypotheses; standard axiom output does not discharge
those hypotheses.

Publication uses the workspace checkpoint to audit and validate the changed
module and its reverse dependents. No whole-project rebuild is claimed here.
