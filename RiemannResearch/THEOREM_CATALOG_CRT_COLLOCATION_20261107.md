# Full-conductor CRT collocation: theorem catalog supplement

7 November 2026. See
[research memorandum](RH/CRTCollocationZeroGrowthResearch20261107.md).
All norms are complete physical Q norms. These are full-conductor spaces,
including prime powers, and not squarefree-only spaces.

## Established finite and Hilbert-space results

`Analysis/FiniteAccretiveCollocation.lean`:

- `difference_energy`, `eq_zero_of_difference_inner`: exact contraction
  identity and its injectivity consequence.
- `existsUnique_test_match`: finite collocation existence and uniqueness.
- `matched_energy`, `matched_defect_le`: the complete shift defect is retained.

`RH/QCRTFiniteCollocation.lean`:

- `trialSpace`, `cellSpace`, `conditionalProjection`, `target`: actual spaces
  and operators in the existing Q Hilbert space.
- `difference_residue`, `difference_mem_cell`: physical differences belong
  to the finite divisor-test space.
- `existsUnique_divisor_match`, `canonical`, `canonical_match`: an actual
  unique legal solution; no matrix-invertibility provider is assumed.
- `conditional_injective_on_trial`, `conditional_range`: the exact finite
  image is the gcd-cell space orthogonal to the multiples-of-L indicator.
- `canonical_conditional`, `conditional_gcd_coordinates`: conditional
  projection matching and gcd-cell measurability.
- `canonical_divisor_moment`, `canonical_dilation_moment`: exact prescribed
  moments, including the L^(-2) boundary term.
- `legal_error_identity`, `canonical_error`, `canonical_mean`, `canonical_norm`:
  complete energies and the explicit leakage remainder.
- `canonical_difference_energy`, `canonical_shift_energy`,
  `canonical_shift_defect_le`: exact identities exposing cancellation of
  leakage from the weaker shift defect.

`RH/QCRTLeakageParseval.lean`:

- `sum_divisorWavelet`: finite Hilbert-space Möbius inversion.
- `divisor_wavelet_inner`, `canonical_low_wavelet`: exact Jordan-normalized
  low coordinates, with the persisted formula in the unnormalized basis.
- `canonical_leakage_parseval`: the full infinite sum over conductors not
  dividing L, including excessive prime-power depths.

`RH/QCRTBoundedCriterion.lean`:

- `lcm_trialSpace_mono`, `iSup_lcm_trialSpace`: the increasing LCM tower
  exhausts the actual full legal span.
- `lcm_optimal_tendsto_projection`: unconditional convergence to the actual
  full legal projection, without asserting that it equals one.
- `canonical_moments_tendsto`: all fixed divisor moments converge under
  cutoff growth and divisor exhaustion.

`RH/QCRTZeroObstruction.lean`:

- `tailMellin`: the actual existing Mellin functional composed with I-T_L.
- `qMellin_trial_zero`: residue annihilation at an actual zeta zero.
- `canonical_mellin_balance`: the signed identity
  1/s = Mellin(a_L)-Mellin(F_L-h_L), retaining the entire endpoint.
- `canonical_leakage_projection_zero`: the complete leakage is orthogonal
  to the finite gcd-cell space.
- `canonical_mellin_obstruction`: the quantitative obstruction
  1/|s| <= |Mellin(a_L)| + ||tailMellin|| sqrt(leakage),
  conditional only on the stated zeta-zero and strip hypotheses.

## Conditional research reductions

| Declaration | Conclusion | Domain-specific obligation |
|---|---|---|
| `qOne_mem_of_bounded_divisor_moments` | 1 lies in the actual full legal closure | Open for an arbitrary supplied family: legal membership, uniform norm bound, and correct limiting divisor moments |
| `qOne_mem_of_bounded_canonical` | 1 lies in the actual full legal closure | Open: uniform bound on the actual canonical family; cutoff growth and divisor exhaustion are explicit |
| `riemannHypothesis_of_bounded_canonical` | Mathlib RH | Same open bound |
| `riemannHypothesis_of_bounded_leakage` | Mathlib RH | Open: bounded complete canonical leakage |
| `riemannHypothesis_of_bounded_lcm_leakage` | Mathlib RH | Open: bounded leakage along some cofinal LCM subsequence; the arithmetic exhaustion conditions are discharged |
| `optimal_tendsto_one_of_bounded_canonical` | Existing full inverse-Gram candidates converge to 1 | Same open canonical bound |
| `lcm_optimal_error_tendsto_zero_of_bounded_canonical` | Actual complete LCM optimal errors tend to zero | Same open canonical bound |
| `riemannHypothesis_of_vanishing_mellin_budget` | Mathlib RH | Open: the explicitly stated actual projected-Mellin budget tends to zero throughout the right half strip |

These implications have proofs; the open growth hypotheses do not yet have
checked providers. No converse RH-to-bounded-collocation theorem is claimed.
The standalone generic moment theorem is a sufficient-condition theorem,
not a claim that every legal bounded family has the required moments.

## Explicit Euler-tail and sampler continuation: now checked

Fourteen new modules replace the earlier paper-only estimate with proofs.
Each module below is exported by the root aggregate; all paths are below
`RiemannResearch/`.

| Owning module | Principal checked results |
|---|---|
| `NumberTheory/DivisorEscapeTail.lean` | Complete escape series, exact divisor-sum subtraction, certified finite-prefix enclosures, basic LCM rate M^(1-t)/(t-1) |
| `NumberTheory/DivisorEscapeEulerProduct.lean` | `tail_eq_series_mul_euler_deficit`; convergence of the actual Euler product and its prime escape union bound |
| `NumberTheory/DivisorEscapePrimeTail.lean` | `tail_lcmUpto_le_explicit_log`; eventual constant log(4)+epsilon; depth splitting, `tail_lcmUpto_square_le_explicit`, and matching `tail_lcmUpto_lower_explicit` |
| `NumberTheory/GcdSampleTail.lean` | Complete S_t(L) sampler energy, summability, positivity, and S<=2^(t-2)D |
| `NumberTheory/DivisorCountSqrt.lean` | tau(L)<=2 sqrt(L) |
| `Analysis/CofinalLogGrowth.lean` | Cofinal/extended-liminf growth transfer; eventual logarithmic lower floors from squared-norm power floors |
| `RH/QGcdSampling.lean` | Actual finite Mobius gcd-cell sampler and its real/complex orthogonality identities |
| `RH/QCRTProjectedMellin.lean` | `tailMellin_norm_le_sharp`, `tailMellin_norm_le_separated`; actual defect energy and unconditional fixed-s norm decay |
| `RH/QCRTExactEndpoint.lean` | `canonical_residual_explicit_obstruction`; exact signed residual endpoint, with no assumed endpoint provider |
| `RH/QCRTZeroGrowth.lean` | Actual canonical power floors, both liminf RH criteria, logarithmic norm floor, and critical-power zero exclusion |
| `RH/QGcdCellEstimates.lean` | Exact conditional cell geometry, finite Mobius formula for S, and necessary full-trial stability factor |
| `RH/QCRTInverseInstability.lean` | `eventually_exists_unstable_trial`: every fixed full-trial inverse bound fails as the modulus tends to infinity |
| `RH/QCRTPrimeCutoffGrowth.lean` | Exact prime canonical lift; actual norm growth along primes |
| `RH/QCRTNestedCutoffs.lean` | Nested conditional identities and `canonical_increment_norm_sq`, retaining the full leakage increment and cross term |

For beta=Re(s), 1/2<beta<=1, A_beta=1+2^(beta-1), the formalized improvement is

    ||tailMellin(L,s)|| <= sqrt(Z)(sqrt(D_(2beta)(L))+sqrt(S_(2beta)(L)))
                         <= A_beta sqrt(Z D_(2beta)(L)).

For every t>1 and M>=2, the fully explicit logarithmic bound is

    D_t(L_M) <= zeta(t)(2 log 4+2)[1+2/(1-2^(1-t))]
                    M^(1-t)/log M.

Its minimum with the basic integer-tail bound is also checked. Eventually,
2 log 4+2 can be replaced by log 4+epsilon for any epsilon>0. The formal
zeta(t) here is the positive-integer p-series.

The matching checked lower bound, for every M>=32, is

    D_t(L_M) >= 4 * 32^(-t) M^(1-t)/log M.

`prime_interval_count_lower` proves pi(32M)-pi(M)>=4M/logM using the retained
Mathlib `Chebyshev.pi_ge`; `prime_interval_count_le_tail` connects these actual
escaping primes to D. Thus the scalar Euler-tail order is sharp up to positive
t-dependent constants; a faster order for D is not an available route to RH.

## Stronger conditional criteria and exact open obligations

| Declaration in QCRTZeroGrowth | Checked conclusion | Still-open input |
|---|---|---|
| `riemannHypothesis_of_liminf_norm_log_eq_zero` | Mathlib RH | Extended nonnegative liminf log(1+||F_(L_(M+2))||)/log(M+2)=0 |
| `riemannHypothesis_of_liminf_residual_log_eq_zero` | Mathlib RH | The corresponding liminf for ||1-F_(L_(M+2))|| is zero |
| `canonical_norm_sq_log_power_floor` | A zero at beta>1/2 forces ||F_(L_M)||^2>=c_s M^(2beta-1)log M eventually | No growth input; the theorem is conditional on the specified zero |
| `zeta_ne_zero_of_cofinal_critical_power_bound` | zeta(s) is nonzero | For some fixed C, ||F_(L_M)||<=C M^(beta-1/2) cofinally |

All canonical vectors are the actual unique full-conductor collocation lifts.
No detector, endpoint decay, Euler-tail estimate, or reverse RH-to-density
provider is assumed in these new criteria. The actual growth bound remains
open. An upper bound for squarefree best-fit displacement is not a bound
for these canonical lifts.

The inverse-instability theorem concerns arbitrary right-hand sides. Prime
canonical growth concerns a sequence that is not divisor-exhausting. Neither
disproves the desired bound along the LCM tower.

## Complete sampler prime-budget continuation

Two further owning modules are exported from the root aggregate:

| Owning module | Established results |
|---|---|
| `NumberTheory/GcdSamplePrimeTail.lean` | Direct first-forbidden-prime-power cover; exact complete cover sums and depth/size split; `sampleTail_lcmUpto_le_reciprocal`; `sampleTail_div_tail_tendsto_zero`; arbitrary-threshold and square-cutoff refinements; all-cutoff `sampleTail_lcmUpto_le_explicit_log` and `eventually_sampleTail_lcmUpto_le_log` |
| `RH/QCRTAsymptoticSampler.lean` | `eventually_tailMellin_norm_le_one_add`; complete `eventually_canonical_obstruction`; zero-dependent `eventually_escape_leakage_floor` |

The existing `NumberTheory/DivisorEscapePrimeTail.lean` owns the reusable
finite prime-to-integer comparison, complete prime integral bound, and
`primeTail_two_le_explicit_log`.

For fixed 1<t<=2 the complete sampler satisfies S_t(L_M)=O_t(1/(M log M)).
For 1<t<2, S_t(L_M)/D_t(L_M) tends to zero. For every epsilon>0 the actual
Mellin detector is eventually bounded by (1+epsilon)sqrt(Z D), with Z=zeta(2).
The exact endpoint and full leakage are retained before taking estimates.

| Conditional research reduction | Conclusion | Domain-specific obligation |
|---|---|---|
| `QCRTAsymptoticSampler.riemannHypothesis_of_cofinal_escape_energy` | Mathlib RH | **Open:** for every 1<t<2, c>0 and N, some M>=N has D_t(L_M)||F_(L_M)||_Q^2<c; the formal indexing uses L_(M+2) |

The zero-dependent leakage lower bound holds for every 0<epsilon<1:
D_(2 Re(s))(L_M)V(L_M) >= (1-epsilon)^2/((1+epsilon)^2 Z |s|^2)
eventually at a hypothetical right-half-strip zero. This does not supply
the cofinal smallness condition. See Section 6 of the stability memorandum.

## Sharp sampler order and Mellin rate continuation

The follow-on changes extend the three existing owning modules:

| Owning module | Established results |
|---|---|
| `NumberTheory/GcdSampleTail.lean` | `sampleTerm_two`, `sampleTail_two`, pointwise antitonicity, `sampleTail_antitoneOn`, `tail_two_le_sampleTail`, and the exact positive-cutoff endpoint ratio `sampleTail_div_tail_two` |
| `NumberTheory/GcdSamplePrimeTail.lean` | Positive explicit constants `sampleLogConstant` and `sampleRatioConstant`; `sampleTail_lcmUpto_lower_explicit`; eventual two-sided energy bounds; `eventually_sampleTail_div_tail_le_power`; `exists_eventually_sampleTail_div_tail_bounds`; normalized-energy bounds and nonconvergence to zero |
| `RH/QCRTAsymptoticSampler.lean` | `eventually_tailMellin_norm_le_power` for the actual projected Mellin map |

For each fixed 1<t<=2 and L_M=lcm(1,...,M), the complete sampler has the
sharp order S_t(L_M)=Theta_t(1/(M log M)). Its relative energy has the sharp
order S_t(L_M)/D_t(L_M)=Theta_t(M^(t-2)). At t=2 this ratio is exactly one
for every positive finite cutoff.

For beta=Re(s) in (1/2,1), the new checked bound is

    K_(L_M)(s) <= [1+sqrt(C_R(2 beta)) M^(beta-1)] sqrt(Z D_(2 beta)(L_M)),

where C_R(t)=C_S(t)/(4*32^(-t)) and
C_S(t)=zeta(t)[1/(t-1)+2^(t+1)/(t+1)+4(2 log 4+2)].
The rate is sharp for the separated arithmetic contribution. No lower
bound for the actual signed Mellin operator is asserted. The canonical
norm-growth obligation remains **Open**, and RH is not proved.
See Section 6A of the stability memorandum for precise endpoint limitations.

## Still not claimed

- Any proof of subpolynomial growth for the actual canonical LCM family,
  or a proof of RH.
- A converse from RH to bounded canonical collocation.
- A separate formalization of the infinite-product representation for S;
  the sharper sampler bounds above use a direct prime-power cover instead.
- Interval certification of the Wolfram full-tail numerical tables.
- A separately named P-LCM-minimizer convergence theorem.

See the [main research memorandum](RH/CRTCollocationZeroGrowthResearch20261107.md),
[stability memorandum](RH/CRTCollocationStabilityResearch20261107.md), and
[existing-machinery audit](RH/CanonicalUpdateMachineryAudit20261107.md).
The latter records the exact signed-source and leakage-response gap that
remains after applying existing carry and screened-Gram results.

## Verification provenance

The preceding construction was published at
`0fb2590c08fff6c746258cc5cc5b8fbda8ac2bcf`.

All fourteen new owning modules were imported and verified together in
`job_Y-NHrRTo0q3HUoOgT7QZK3Y0xZr1GUoH`, with server-reported verification
time 18.649 seconds. Fourteen principal declarations were axiom-audited:
every result used only `propext`, `Classical.choice`, and `Quot.sound`.
This includes the new arithmetic estimates, actual RH reductions, finite
sampler formula, instability, prime growth, and nested increment energy.
The later three-lemma lower-bound candidate passed
`job__A9uD8lLirroZC2FOf4Jo7WR8T3MbkbJ` in 6.846 seconds. Its final lower theorem
had the same standard axiom set and was merged into the arithmetic owner
before the final checkpoint.

The final checkpoint validates the root aggregate and affected modules,
audits the repository delta, and publishes the exact commit. Its terminal
result is reported in the accompanying delivery; a successful snippet alone
is not represented as that final publication gate.

## Sampler continuation verification

The actual owning modules were imported and nine principal results audited in
server job `job_2UWZpSU2BXE_1to_4VLKjfV1r84hGqeE`, which succeeded with
server-reported verification time 25.561 seconds. The checked modules included
DivisorEscapePrimeTail, GcdSamplePrimeTail, the affected QCRTZeroGrowth consumer,
and QCRTAsymptoticSampler. Every audited declaration used only
`propext`, `Classical.choice`, and `Quot.sound`. The conditional RH theorem
still has the explicit cofinal-growth hypothesis in its type.

The opening of a fresh workspace timed out; reopening the retained workspace
succeeded. Opening round-trip duration was not recorded. Subsequent queued
checks were polled at their reported 30-second minimum intervals; polling
latency and the server's reported verification duration are distinct.
The retained token is `ws_mwWauOIKeaTQFsXlLf9olVQpDUYrLPst`.
The final checkpoint separately audits, validates, and publishes the complete
unpublished delta; its terminal job and commit are reported in the delivery.

## Sharp-order continuation verification

This continuation starts from published commit
`4b977a100e86fa1462cc2480c606ed5a45251483`.
The three actual owning modules passed server job
`job_rtm41nQ0l6YmdE3wPQ-XOca_V0rqu90f`, with reported verification
time 28.486 seconds. All fifteen newly added theorems were axiom-audited,
as was the existing conditional cofinal escape-energy implication to RH.
Each used only `propext`, `Classical.choice`, and `Quot.sound`.
Two positive-constant definitions accompany the fifteen theorems.
The final checkpoint separately validates and publishes the repository delta.

## Canonical prime-power update continuation

Base: 8f11fcee05b12c462bb0538be8839bb6aa7df5a5. The user approved publication after review.

**Kernel-checked before publication in the owning modules:** server job
job_ujFCPKlblpVJB_6DH7Fzyzfv96rawsgQ built both changed owning modules and
audited all 15 added theorems, using only propext, Classical.choice, Quot.sound.
Reported verification duration: 15.547 seconds. This is targeted module
verification; the publication checkpoint separately validates the full delta and any integration.

QCRTNestedCutoffs adds one definition, updateSource, and 14 theorems:
- canonical_norm_growth_exact; canonical_update_budget_iff;
- canonical_increment_conditional; updateSource_eq; updateSource_norm_sq;
- target_increment_divisor_moment; signed_divisor_update_source;
- canonical_target_source_mean; signed_difference_update_source;
- signed_difference_update_source_old; signed_difference_update_source_new;
- canonical_increment_difference_test; canonical_increment_difference_energy;
- leakage_divisor_moment_sq_le.

LinearAlgebra/ObliqueBlockElimination adds block_elimination, preserving both
cross blocks and the signed source in a nonsymmetric system. It is exported
from the aggregate module.

For N=pL at admission p^k, the source is
b=h_N-h_L-T_N r_L, with ||b||^2=L^-2-N^-2+||T_N r_L||^2.
New difference-test rows have signed source delta/d+<r_L,a_d>.
The exact norm update retains 2<r_L,r_N-r_L>; its budget equivalence does not
prove the budget. The contraction-defect estimate is not a full-Q norm bound.

**Independently checked calculations:** exact rational complete-tail intervals
certify E_12>E_60, a negative leakage correlation at 12 -> 60, and failure of
the literal C=1 multiplicative bound at 2 -> 6. Wolfram agrees at higher
precision. Higher stages through L_16=720720 are floating-point exploration.

**Paper argument, not Lean-checked:** the gcd-cell refinement formula and an
arithmetic family at genuine 2^k LCM admissions show that periodicity,
zero-cell vanishing, and old-cell orthogonality cannot alone force
depth-decaying revealed leakage. This family is not asserted to be canonical
or to satisfy h_L+r in V_L.

**Open:** the actual canonical signed Schur-response estimate, any uniform
C/p^k norm-growth budget, and the cofinal canonical escape-energy hypothesis.
No RH claim is made. See RH/CanonicalPrimePowerUpdatesResearch20261107.md.
