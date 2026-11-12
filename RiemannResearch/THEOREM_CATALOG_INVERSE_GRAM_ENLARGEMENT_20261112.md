# Inverse-Gram enlargement and periodic tail certificates — 12 November 2026

Baseline: eb09bd278f88edafc68a60b1603b7fd4efba6aad.
Published source commit: 584e5593316880a078e745838288c6065bace0ec.
Full-project Bazel/BuildBuddy checkpoint passed before publication:
job_W--Qw94L1msS8UktHmP-11KQC58l4pN5, target //:RiemannResearch,
195.512 server build seconds. Guarded audit of all 18 new theorems passed:
job_thm7bb2PiL65cPhpFat_fbRlLlIxJNgy; allowed axioms were only
propext, Classical.choice, and Quot.sound.
The arithmetic cofinal O(alpha) and all-exponent near-linear providers remain OPEN.

## Signed direction descent and nested full families

Module: RH/QReciprocalSchurDescent.lean.
Let J_alpha(v;x)=||D(v-x)||_Q^2+alpha||v||_Q^2. Define
s_alpha(w)=||Dw||_Q^2+alpha||w||_Q^2,
r_alpha(x,v,w)=<D(x-v),Dw>_Q-alpha<v,w>_Q.

Exact identity:
J_alpha(v+t w;x)=J_alpha(v;x)-2t r_alpha+t^2 s_alpha.
For s_alpha != 0, t=r_alpha/s_alpha gives the exact finite gain
J_alpha(v+(r_alpha/s_alpha)w;x)=J_alpha(v;x)-r_alpha^2/s_alpha.
Every larger finite-span minimizer containing v and w has cost at most this
candidate's cost. This is an unconditional finite improvement inequality.
It does not assert that the residual pairing is nonzero or uniformly large.
The module does not construct a block matrix inverse or assert a Schur-complement
asymptotic estimate.

For H<=K and alpha,beta>0, with v_H=fullMinimizer H alpha and
v_K=fullMinimizer K beta, the exact nested-parameter identity is

fullValue H alpha = fullValue K beta
 + ||D(v_H-v_K)||_Q^2 + beta||v_H-v_K||_Q^2
 + (alpha-beta)||v_H||_Q^2.

At fixed alpha, conductor enlargement decreases the cost by exactly the first
two nonnegative terms. This does not imply a rate for H-dependent alpha.
Regularization slopes satisfy
(alpha-beta)||v_alpha||^2 <= V(alpha)-V(beta)
 <= (alpha-beta)||v_beta||^2.
For 0<beta<=alpha, beta V(alpha)<=alpha V(beta), so normalized cost increases
as regularization decreases when the conductor space is held fixed.

Public definitions: directionEnergy, residualPairing.
Public theorems:
- cost_change_regularization
- cost_add_smul
- directionEnergy_pos
- optimized_direction_identity
- minimizer_direction_bound
- nested_parameters_identity
- fullSpan_mono
- fullValue_parameters_identity
- fullValue_nested_gain
- fullValue_mono_conductors
- fullValue_mono_parameters
- fullValue_regularization_slope
- fullValue_normalized_mono
- fullValue_direction_bound

## Infinite signed periodic tails

Module: Analysis/PeriodicWeightedTail.lean.
For nonnegative decreasing weights w, convergence of the indicated weighted
series, and uniformly bounded signed prefixes |sum_(i<k) f(i)|<=B, prove
|sum_i f(i)w(i)|<=B w(0).
For a periodic f of mean a, exact finite-prefix discrepancy B gives
|sum_i f(i)w(i)-a sum_i w(i)|<=B w(0).
The general periodic theorem needs only finite within-period prefix checks.
A nonnegative periodic f admits B=r*a, where r is its period.
All summability hypotheses are explicit; the theorems do not silently assume
convergence. Applications to Q source and D-error tails must supply their
respective squared periodic sequences and weights.

Public theorems:
- infinite_abel_bound
- infinite_weighted_mean_bound
- periodic_weighted_mean_bound
- nonnegative_periodic_weighted_mean_bound

## Scope of the continuation

Eighteen theorems and two definitions, plus two root imports.
These identities and tail estimates preserve signed cancellation but supply
no new unconditional asymptotic exponent. Numerical finite-stage certificates
must be recorded separately from these abstract kernel-checked identities.
A full-project checkpoint remains the publication gate.
