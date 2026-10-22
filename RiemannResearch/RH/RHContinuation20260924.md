# RH continuation and recovered-module integration — 24 September 2026

## Scope and evidence

This is a targeted source audit and continuation plan, not an exhaustive verification of the RH repository. The inspected `main` snapshot is [`e2518b1fae5f7211cf07fc7b5a1303c1234d7460`](https://github.com/Cnoack3/RiemannResearch/commit/e2518b1fae5f7211cf07fc7b5a1303c1234d7460). Source declarations and the associated verification reports were read through GitHub. The source audit was followed by successful full-file checks of the repaired trigamma and midpoint modules on the recovery base. Final integration against main is validated separately by the publication checkpoint; no whole-repository verification is inferred from the targeted checks.

The recovery branch's latest inspected evidence commit is [`ae75566e5a657cd235af687eaf93fdda0762cdad`](https://github.com/Cnoack3/RiemannResearch/commit/ae75566e5a657cd235af687eaf93fdda0762cdad). Its `recovery/trigamma-2026-09-21/README.md` supersedes the older status inside the unchanged recovery ZIP. All four recovered module paths are absent from the inspected main snapshot.

## Published recovery checkpoint

Commit [`090bf0ca128df7ca1c9e892577f50cf93ad1cdd2`](https://github.com/Cnoack3/RiemannResearch/commit/090bf0ca128df7ca1c9e892577f50cf93ad1cdd2) published all four recovered modules. The checkpoint successfully built the four affected modules on the original base, integrated them into the newer main without conflicts, rebuilt the integrated modules, and pushed. This supersedes the earlier “proof candidates” status; it does not assert a full-repository build.

The subsequent extension in `CRTTrigammaMeanValue` uses cancellation of the common reciprocal-series tails to improve the scaled squared error from a denominator `L^2` to `L^3`, and proves an explicit absolute-error bound. Its precise statements assume only positive real residue and conductor. The publication checkpoint records acceptance of the final source.

A 16-theorem axiom audit (job `job_GR3fqQj_tPijyCNZzSoDqN1rbV3CcRwo`) checked the exact alpha source together with the built midpoint/inverse modules. Every listed declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`. The ordinary positivity and Gram hypotheses in their theorem types are still explicit.

## Current unconditional endpoints

In `RH/HardyMobiusEndpoint.lean`, namespace `RiemannResearch.RH.Pareto`, `rawHardyMobiusSum_endpoint` proves convergence of the actual raw Möbius sums to `1/s`, uniformly in the vertical-line squared integral over every real part greater than 1. The corrected family is covered by `correctedHardyMobiusSum_endpoint`. The raw endpoint's arithmetic provider is discharged by `rawMobiusEndpointHeadRate`, using `mobiusReciprocalSum_sq_mul_harmonic_tendsto_zero` from `RH/MobiusQuantitativeRate.lean`.

`RH/ParetoMellinHardyEndpoint.lean`, `paretoMellin_hardy_endpoint_isLUB`, identifies the actual Hardy line-integral supremum with the complete weighted cell energy. This endpoint uses a stronger-decaying weight than the critical Pareto norm. It does not establish approximation at real part 1/2. See `RH/HardyEndpointFormalization20260924.md` for the exact normalization, sources, and recorded verification boundary.

In `RH/NoorRegularizedApproximation.lean`, namespace `RiemannResearch.RH.Pareto.Noor`, `finiteMinimum_tendsto_zero` proves unscaled finite arithmetic regularization convergence for every parameter sequence tending to zero. `exists_finite_minimizing_lifts` supplies actual finite arithmetic minimizers when the parameters are positive. `RH/NoorRegularizedGram.lean` makes their coefficients and energy explicit through `finiteMinimum_eq_inverseGram`, `finiteMinimizer`, and `finiteMinimizer_energy`.

## Precise remaining analytic obligations

The Noor route still needs a cofinal sequence `N`, a positive sequence `t` tending to zero, and the stronger rate

\[
\frac{\operatorname{finiteMinimum}(N_j,t_j)}{t_j}\longrightarrow0.
\]

`riemannHypothesis_of_finiteMinimum_div_parameter_tendsto_zero` keeps that rate as its explicit `hrate` hypothesis. The inverse-Gram formulation is `riemannHypothesis_of_inverseGram_gap` in `RH/NoorRegularizedGram.lean`, in the same namespace. The exact bound `energy_div_le_finiteMinimum_div` explains why unscaled convergence does not supply the divided rate. The complete mixed terms remain in `RH/NoorShiftedDefect.lean` and the associated mixed-Gram development.

The Hardy route still needs one constant bounding the corrected family's actual line integrals on the moving half-planes `Re(s) > 1/2 + α_N`, with `α_N ≥ 0` and `α_N → 0`. This is exactly `hbound` in `RH/ExactHeadMovingHardyRH.lean`, `canonicalMobius_riemannHypothesis_of_movingHardy_bound`. Legality and exact initial coordinates are discharged there; the common bound is not. Compactness or diagonal selection alone supplies neither missing estimate.

For the Pareto/DPP route, the actual residual must vanish, equivalently the relevant saturation or capacity condition must be proved using the established project bridges. `RH/IntegerDPPResidueAccounting.lean` already proves the unconditional exact limit

\[
q_N\longrightarrow
1+\sum_{n\ge0}\operatorname{classEntry}(n+1)
-\sum_{n\ge0}\operatorname{classLoss}(n+1).
\]

The declaration is `qN_tendsto_entry_loss`; both series are summable. `qN_liminf_eq_one_iff_entry_eq_loss` identifies saturation with equality of those totals, but does not prove their equality. In this normalization, `q_N` is a probability; the divergent quantity is tail capacity.

## Role of the four recovered modules

| Module | Recovery evidence | Intended contribution and limit |
| --- | --- | --- |
| `LinearAlgebra/FiniteMatrixInverseComparison.lean` | Published and checked against newer main; the earlier eight-theorem axiom audit is preserved. | General inverse-quadratic antitonicity and relative comparison. The repaired proof imports existing `FiniteConstrainedMatrixInverse.lean` and reuses `gramEquiv_symm_eq_inv_mulVec` for literal inverse identification. |
| `RH/NonnegativeResidueObstruction.lean` | Published and checked against newer main; two endpoint declarations were also axiom-audited. | The normalized nonnegative-coefficient family has tail energy at least `2/27`, with occupation cap `27/31`. This motivates signed cancellation and does not bound unrestricted signed minimizers. |
| `RH/ProgressionMidpointInverse.lean` | Repaired source published after validation against newer main. | Transfer existing relative weight bounds through Gram inversion to occupation estimates. The general theorem transfers every real limiting value for the specified finite dictionaries; applying it to the arithmetic DPP requires identifying its exact Gram and rows. Limit one specializes to saturation equivalence. It does not supply saturation. |
| `RH/CRTTrigammaMeanValue.lean` | Repaired source published after validation against newer main. | Canonical mean points, monotonicity, fixed-residue scaled limits, and cubic scaled-error estimates. A fixed-residue asymptotic is not uniform control of a growing Gram inverse. |

`RH/ParetoProgressionMidpoint.lean` already owns relative weight, quadratic, minimum, and zero-limit comparisons; these should be reused. A further concrete consumer of generic inverse comparison is monotonicity of Noor inverse gain under increasing positive regularization, since `finiteRegularizedGram N t = finiteShiftedGram N + t^2 • finiteUnshiftedGram N`. That bounded extension would still leave the divided-energy rate open.

## Integration and continuation

Repair and verify modules in coherent groups, recording exact source and result after each successful publication. Preserve the archived source and its historical evidence. Keep new status entries tied to actual check results; historical file verification is not verification against the newer main snapshot.

The inspected `tools/agent_workspaces.py` checkpoint implementation validates the local changes, commits them, and, if main has advanced, cherry-picks them into a temporary latest-main clone and revalidates before pushing. An integration conflict leaves the original local commit preserved. No reset, rebase, or deletion of the recovery workspace is required.

No unconditional proof of RH is claimed by this audit or by the four recovered additions. The next mathematical work should target an explicit missing arithmetic estimate above, preserving all signed terms and the complete infinite tail.
