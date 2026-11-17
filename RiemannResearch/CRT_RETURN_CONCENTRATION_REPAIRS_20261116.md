# Verified replacements for the concentration and return-sampling steps

Source: Christian Noack, *Chinese-Remainder and Profinite Structure in the
Nyman–Beurling–Báez-Duarte Hilbert Space*, `sdf_modified.pdf`, July 21, 2026,
Lemma 14.6, Hypothesis 14.9, and Remark 14.10.
[Source PDF](https://drive.google.com/file/d/1RWvDfQdERH8uDRS9PwGhK2eOKJxyfvO6/view).
This continues commit `e16638c565a286502efaad5e72dcdc448f6332b8`.

The two invalid steps have valid replacements below. The original premises
do not imply the originally claimed conclusions. The corrected estimates
retain the missing scale factors, reference-measure bias, and finite-interval
boundary terms. They do not establish the still-open uniform arithmetic
bounds needed for RH.

## Replacement for Lemma 14.6

Let `s` be the finite return sample, `d(i)` its atom label, and `u_d` one shared
atom vector. Set

\[
e_i=c_i-u_{d(i)},\quad S=\sum_{i\in s}|e_i|,\quad
N=|s|,\quad V_d=\sum_{i:d(i)=d}e_i^2.
\]

The exact identity is

\[
 S^2+\frac12\sum_{i,j\in s}(|e_i|-|e_j|)^2
 =N\sum_d V_d.
\]

Consequently, any fiber budgets `V_d <= B_d` give

\[
 S^2\le N\sum_d B_d.
\]

In particular, the original premise `V_d <= E^2 H` gives only

\[
 S^2\le N\,D\,E^2 H,
 \qquad D=\#\{d(i):i\in s\}.
\]

The desired `S^2 <= C H E^2` does follow if `N <= C H` and the *total*
budget is at most `E^2`. A usable allocated version is

\[
 V_d\le b_d E^2,\qquad \sum_d b_d\le1.
\]

The previous per-fiber `E^2 H` premise cannot substitute for this total
budget. This is a corrected premise, not a proof that the actual optimizer
satisfies it.

There is also an exact accounting rule for shell-local centering:

\[
 V_d=\sum_{i:d(i)=d}(c_i-\bar c_d)^2+
 N_d(\bar c_d-u_d)^2.
\]

Shell-dependent means may be used to estimate the first term, but the mean
shift must be charged to the same `u_d` across all shells. Choosing a different
legal atom coefficient independently on every shell is not justified.

Formal declarations in `Analysis/FiniteAtomConcentration.lean`:

- `l1_sq_add_pairwise_eq_card_mul_loss`
- `loss_le_fiber_budgets`
- `l1_sq_le_fiber_budgets`
- `l1_sq_le_uniform_fiber_bound`
- `l1_sq_le_normalized_fiber_budgets`
- `loss_le_of_dispersion_and_bias_budget`

## Replacement for Hypothesis 14.9

For `Q > 0`, define

\[
 U_Q=\{0\le r<Q:(r,Q)=1\},\qquad
 \mu_U(f)=\frac1{|U_Q|}\sum_{r\in U_Q}f(r).
\]

Every reduced return coordinate is a unit. The reference distribution must
respect this support. For an additive character, its unit reference is its
sum over units divided by `|U_Q|`; with the usual notation this is
`c_Q(a)/phi(Q)`, not zero in general. The Lean statements use arbitrary real
observables, hence apply separately to real and imaginary parts of characters.
No multiplicative formula for Ramanujan sums is needed by these proofs.

For even `Q`, the parity observable has `mu_U((-1)^r) = -1`. Its deviation
from this reference is exactly zero on every return sample. The prior
parity obstruction to Haar comparison remains valid; unit centering
removes that deterministic obstruction exactly.

There is an unconditional finite-interval replacement. Let

\[
 I=\{a,a+1,\ldots,a+H-1\},\quad H=kQ+r,
 \quad N=\#\{n\in I:(n,Q)=1\}>0,
\]

and write

\[
 g(n)=1_{(n,Q)=1}\bigl(f(n\bmod Q)-\mu_U(f)\bigr).
\]

Then the complete signed identity is

\[
 \sum_{n\in I}g(n)=\sum_{i=0}^{r-1}g(a+kQ+i).
\]

If `|f| <= M` on units and `M >= 0`, it follows that

\[
 \left|\frac1N\sum_{n\in I,(n,Q)=1}f(n\bmod Q)-\mu_U(f)\right|
 \le\frac{2Mr}{N}.
\]

Taking `k=floor(H/Q)` and `r=H mod Q` yields the ordinary incomplete-period
bound. For complete periods the error vanishes. This estimate is explicit
and unconditional, but it does **not** give a modulus-uniform power saving
for short shells when `Q` grows. Any stronger unit-centered discrepancy
hypothesis remains open and must be stated for the required observables.

Formal declarations in `NumberTheory/UnitCenteredReturnSampling.lean`:

- `unitMean_parity`, `parity_centered_return_sum`
- `coprime_mod_iff`, `return_centered_sum`
- `unit_return_interval_exact`, `return_average_error_exact`
- `return_average_error_le`

The general block decomposition is in
`Analysis/FinitePeriodicCancellation.lean`.

## Corrected mean-square transfer for Remark 14.10

Centering the sampling measure on units does not permit erasing its bias
relative to the original center `b`. The exact identity is

\[
 \operatorname{Avg}_S(f-b)^2
 =\operatorname{Var}_U(f)+(\mu_U(f)-b)^2+
 \bigl[\operatorname{Avg}_S(f-b)^2-\mu_U((f-b)^2)\bigr].
\]

The square-bracketed term is signed and retained. An absolute bound on this
term gives a valid mean-square transfer; a character discrepancy estimate
alone needs its full observable-expansion cost before it supplies that bound.

For actual interval returns, the preceding finite-period argument supplies
an unconditional version. If `|f-b| <= L` on units, then

\[
 \operatorname{Avg}_{I\cap U}(f-b)^2
 \le \operatorname{Var}_U(f)+(\mu_U(f)-b)^2+
 \frac{2rL^2}{N}.
\]

This is `return_second_moment_le`. The unrestricted-to-unit nonnegative
moment comparison also has a checked, explicit density cost:

\[
 \mu_U(f^2)\le\frac{Q}{|U_Q|}\mu_{\mathrm{Haar}}(f^2).
\]

These statements replace the unsupported transfer from Haar translates to
returns. They do not assert that the right side is small in the actual
short-shell regime.

Other declarations: `unit_second_moment`, `sample_second_moment_exact`,
`sample_second_moment_le`, `unit_second_moment_le_haar`.

## Actual occurrence optimizer and RH consumer

`RH/ExactHeadOccurrenceBudgets.lean` applies the repaired concentration
accounting to the actual `occurrenceCoefficients P x`, not an abstract
replacement sequence:

\[
 A(P,x)\le5\sum_d B_d
\]

whenever each complete fiber loss for a single shared atom vector `u` is
bounded by its `B_d`. This is `reuseEnergy_le_fiber_budgets`.

`riemannHypothesis_of_cofinal_fiber_budgets` is a **conditional research
reduction**: at common arbitrarily large stages, the actual fiber budgets
must hold and `occurrenceEnergy + 5 sum_d B_d` must have one uniform real
bound. It proves the implication, not its analytic hypotheses.

Still open: such budgets for the actual optimizer, a sharper route retaining
signed Green cancellation, and the analytic occurrence-error provider.
The repaired finite identities and interval estimates do not close RH.

## Verification

The sources include guarded axiom audits for the decisive new results.
These audit ordinary transitive foundations; domain-specific assumptions
remain visible in theorem types. Publication requires the full managed
`//:RiemannResearch` Bazel/BuildBuddy checkpoint. Its terminal verification
record and final commit are reported with the publication.
