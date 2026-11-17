# Canonical occurrence blocks: integration and explicit optimizer

Date: 16 November 2026 (America/Los_Angeles).
Base: 9aa96643cf4257b8957e9ecfc0303f78e063a766.
Namespace: RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection.

This continuation integrates the actual occurrence normal equations, the
complete progression-weight geometry, finite weighted variance, and the
cofinal signed Green criterion. It adds 43 named theorems and three explicit
definitions in three exported modules. Ten new guarded axiom audits are
added to the existing occurrence audit.

The mathematical derivations are assembled from existing repository results.
No literature novelty is claimed, and no new asymptotic arithmetic provider
is assumed to have been proved.

## Exact optimizer, with no partition oracle

For P>0, write
F = {n : 1 <= n < P, x < gcd(n,P)}.
Let a_0 < ... < a_(m-1) enumerate F in increasing order, and put a_m=P.
The definition occurrenceBoundary constructs these endpoints using
Finset.orderEmbOfFin; it also covers F empty. All endpoint membership,
ordering, coverage, and no-interior-free-position facts are proved.

Let w(r)=progressionWeight P r, including every infinite progression tail,
and T(r)=atom P 1 r-1, the actual coprime-count target.
On I_i=[a_i,a_(i+1)), define

    W_i  = sum_(r in I_i) w(r),
    mu_i = sum_(r in I_i) w(r) T(r) / W_i.

The actual normal-equation fit is mu_i throughout I_i.
Before a_0 its value is zero. Its active coefficients satisfy exactly

    c*(a_0) = mu_0,
    c*(a_i) = mu_i - mu_(i-1),  i>0.

Every active coefficient is nonnegative, and the actual fitted function is
monotone. These properties are conclusions of the unconstrained normal
equations, not extra optimization constraints. Coefficients outside F are
unused and are not asserted to be unique or nonnegative.

## Exact complete error and two-sided block bounds

The full finite occurrence objective is exactly

    occurrenceEnergy(P,x)
      = sum_(1 <= r < a_0) w(r) T(r)^2
        + sum_i sum_(r in I_i) w(r) (T(r)-mu_i)^2.

The constrained initial interval is retained. The terminal residue r=P is
outside this finite objective and is still handled by the existing
MobiusHeadGreen.actual_energy_split in the RH closure argument.

For each free block I, with W=sum_I w and E_I its actual error,

    2 W E_I = sum_(r,s in I) w(r) w(s) (T(r)-T(s))^2,

and for any real constant z,

    sum_(r in I) w(r) (T(r)-z)^2 = E_I + W (mu-z)^2.

Consequently,

    E_I <= W [T(b-1)-T(a)]^2 / 4,  I=[a,b).

For distinct r,s in the block there is also the certified lower bound

    w(r)w(s)(T(r)-T(s))^2 / (w(r)+w(s)) <= E_I.

A block with constant target contributes exactly zero. All weights remain
complete; the formalization does not truncate their infinite progressions.

occurrenceGapBudget is the initial target energy plus the sum of these
quarter-oscillation bounds. It is an explicit finite arithmetic statistic,
and occurrenceEnergy_le_gapBudget needs only P>0.

## Integration with the actual atom optimizer

For any shared atom vector u, the existing exact decomposition gives

    atomEnergy = occurrenceEnergy + reuseEnergy.

The new assembled bound is

    atomEnergy(P,x)
      <= occurrenceGapBudget(P,x)
         + ||fit(c*) - synthesis(u)||_complete^2.

The signed Green trial is retained in full; it is not replaced by the much
larger unweighted coefficient dispersion. The previous exact identity for
its nonnegative excess over the optimal reuse energy remains unchanged.

riemannHypothesis_of_cofinal_gap_green_budget is a **conditional research
reduction**. It requires one real B, stage-dependent legal atom vectors u,
and arbitrarily large common x with

    occurrenceGapBudget(greenPeriod x,x) + GreenTrialEnergy(u_x) <= B.

The implication is proved. This uniform cofinal arithmetic bound remains
**Open**. The finite block calculation does not supply a squarefree
smooth-gap estimate or a uniform signed Green cancellation estimate.

## Declaration map

| Module | Main declarations and role |
|---|---|
| RH/ExactHeadOccurrenceCertificates.lean | fit_jump; occurrence_trial_identity; occurrenceEnergy_le_trial; trial_normal_fit; occurrence_fit_eq_of_normal; occurrenceCoefficients_eq_of_normal. A finite normal certificate determines the actual fitted values and every active coefficient. |
| RH/ExactHeadOccurrenceBlocks.lean | occurrence_fit_eq_block_mean; occurrence_block_energy_eq_variance; occurrence_block_trial_identity; occurrence_block_pairwise_identity; occurrence_block_energy_le_oscillation; occurrence_block_pair_lower; occurrence_initial_energy. Sixteen theorems establish exact local accounting and bounds. |
| RH/ExactHeadOccurrencePartition.lean | occurrenceBoundary and its coverage/order theorems; occurrence_partition_sum; occurrenceEnergy_eq_block_variances; occurrenceGapBudget; occurrenceEnergy_le_gapBudget; atomEnergy_le_gapBudget_add_green; occurrenceCoefficients_boundary; occurrenceCoefficients_nonneg; occurrence_fit_mono; riemannHypothesis_of_cofinal_gap_green_budget. Twenty-one theorems assemble the canonical finite solution and its RH consumer. |

## Verification and remaining work

All three modules are exported by RiemannResearch.lean and use the existing
RH/BUILD.bazel package. The ten new #guard_msgs axiom checks require exactly
propext, Classical.choice, and Quot.sound. They check transitive foundations;
substantive premises remain visible in theorem types.

Focused integrated audit: job `job_mqilA0Qpip7ZxoTJvcc76383N8TPjxcf`
completed successfully using Bazel/BuildBuddy, with 61.19 server-reported
verification seconds (61.26 seconds including the worker interval).
[Focused build](https://app.buildbuddy.io/invocation/28ceff8f-3a69-4fcf-b680-5fe86cdcf6b8).
The workspace-opening request took 26.1 seconds in a batch with independent
GitHub reads; that is not a kernel-verification measurement. Polling delay
is separate from the server build time.

The managed full-project Bazel/BuildBuddy checkpoint is the publication
gate. Focused file checks certify only their listed targets and imports,
not the entire project. The terminal checkpoint record identifies the exact
published commit and full //:RiemannResearch validation.

Current research agenda (updated 17 November 2026):

1. Prove a uniform cofinal bound for the explicit initial-plus-block
   statistic, or a sharper exact-variance bound that uses the pairwise formula.
2. Construct one shared atom vector whose complete signed Green trial is
   bounded at the same cofinal stages.
3. **Completed for every fixed P>0:** complete rational energy and coefficient
   enclosures with effective convergence, plus finite reuse certificates.
   See [the certification continuation](THEOREM_CATALOG_OCCURRENCE_CERTIFICATION_20261117.md).
4. Prove any required squarefree smooth-gap or translated-sieve providers
   with their correct arithmetic normalization.

RH, the cofinal Green bound, and the uniform compression estimate remain open.
