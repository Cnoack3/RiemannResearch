# Full-conductor oscillation verification evidence

The focused Bazel checks below were run on the reviewed Lean sources. The
publication checkpoint checks the aggregate project and downstream consumers.

| Check | Server job | Scope | Result |
|---|---|---|---|
| Earlier oscillation checkpoint | `job_33234U-hLjNTtoKtV0VTunS2xhyc8zdU` | Aggregate project at [`dc881be2`](https://github.com/Cnoack3/RiemannResearch/commit/dc881be2b37746444ee88b6d867ae70a36dd132b) | Passed |
| Full oscillation application | `job_ZrZf8mI3WTRHp5bdPWjvgKLV4JPpPS-j` | `QFullOscillationDual.lean` and transitive imports | [Passed](https://app.buildbuddy.io/invocation/7c508752-e716-4ae4-b5ea-734acb108c52) |
| Axiom audit | `job_HMyiHlxWo4N59H8W1RRueligAsrYqGJU` | 21 selected declarations | [Passed](https://app.buildbuddy.io/invocation/f41e9e86-8a45-4168-b65e-276d6eb56c46) |

The checked `QFullOscillationDual.lean` source has SHA-256
`5778da86ee6162348888456fd4d09b55021ba94cb64562a5280358e13f2ec00b`.
The final file check followed a repair to the multiplication-cancellation
proof. The axiom audit covers dependencies. The uniform kernel-product
premise remains open.

## Executable axiom audit

```lean
import RiemannResearch.RH.QFullOscillationDual
import Lean.Util.CollectAxioms
import Lean.Elab.Command

-- Executable audit: fail on any transitive axiom outside ordinary foundations.
-- This does not discharge the explicit hypotheses of conditional theorems.
run_cmd do
  let names : Array Lean.Name := #[
    ``RiemannResearch.RH.QFullDivisorProjection.sequence_mod_of_mem,
    ``RiemannResearch.RH.QFullDivisorProjection.qOptimizer_tendsto,
    ``RiemannResearch.RH.QFullDivisorProjection.pOptimizer_tendsto,
    ``RiemannResearch.RH.QFullDivisorProjection.displacement_tendsto,
    ``RiemannResearch.RH.QFullDivisorProjection.lcm_displacement_tendsto,
    ``RiemannResearch.RH.QFullDivisorProjection.factors_through_residue,
    ``RiemannResearch.RH.QFullDivisorProjection.continuous_profiniteLift,
    ``RiemannResearch.RH.QFullDivisorProjection.positive_site_error_one,
    ``RiemannResearch.RH.QFullDivisorProjection.no_uniform_approximation_to_one,
    ``RiemannResearch.RH.QFullCRTDisplacement.riemannHypothesis_of_finite_residue_oscillation,
    ``RiemannResearch.RH.QFullCRTDisplacement.displacement_carry_translation,
    ``RiemannResearch.Analysis.ResidueOscillation.bound_of_expanding_head_limit,
    ``RiemannResearch.RH.QMatchedOscillationKernel.inner_pairKernel,
    ``RiemannResearch.RH.QMatchedOscillationKernel.screenedPairKernel_energy,
    ``RiemannResearch.RH.QMatchedOscillationKernel.matched_test_identity,
    ``RiemannResearch.RH.QMatchedOscillationKernel.matched_pair_identity,
    ``RiemannResearch.RH.QMatchedOscillationKernel.matched_pair_bound,
    ``RiemannResearch.RH.QFullOscillationDual.carry_screened_identity,
    ``RiemannResearch.RH.QFullOscillationDual.riemannHypothesis_of_head_kernel_product,
    ``RiemannResearch.RH.QFullOscillationDual.prime_power_escape_example,
    ``RiemannResearch.RH.QFullOscillationDual.endpoint_carry_cancellation_example]
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let _ ← Lean.getConstInfo name
    let axs ← Lean.collectAxioms name
    for ax in axs do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {name}"
```
