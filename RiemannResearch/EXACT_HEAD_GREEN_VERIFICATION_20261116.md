# Exact-head Green verification and axiom audit
Date: 2026-11-16.

## Guarded transitive axiom check

Bazel/BuildBuddy job `job_xAhpgx5jIhHCYWwQTWv1rPXEgARUYX-D` passed,
exit code 0, 51.966 seconds. Eight `#guard_msgs` assertions required the
exact transitive axiom list

    [propext, Classical.choice, Quot.sound]

for the main conditional RH theorem and the supporting normal-coefficient,
legal norm-split, primitive-square, affine-fit, signed-moment, low-conductor
and event-summation results. No `sorryAx` or custom axiom occurs in these
dependency closures.

[Guarded audit build](https://app.buildbuddy.io/invocation/fa131769-376f-4501-b893-15b9ae362694)

Audited snippet SHA-256:
`791a06569bddd5ad60527aa2eb67876023b27602c6381043932118a28b48029b`.

The 14 newly authored source modules were also scanned for `sorry`,
`admit`, `axiom` declarations and `unsafe` declarations; no matches were found.
This source scan covers the new modules, not every pre-existing repository file.

## Published full checkpoints

| Commit | Full target | Build seconds | Evidence |
|---|---|---:|---|
| [c20ca4a](https://github.com/Cnoack3/RiemannResearch/commit/c20ca4aa4e1d728c38a2da59826d330b8834325c) | //:RiemannResearch | 227.504 | [Build](https://app.buildbuddy.io/invocation/e67bbbea-fd1a-481e-88a5-b3aba0f00356) |
| [c8e343a](https://github.com/Cnoack3/RiemannResearch/commit/c8e343a60365e47f39eff95d738cdc3d518e8f83) | //:RiemannResearch | 208.605 | [Build](https://app.buildbuddy.io/invocation/403192db-aaf6-4d9c-b608-42dc0e30e57e) |
| [2042719](https://github.com/Cnoack3/RiemannResearch/commit/2042719725f4edd784a9eecf2767827b1d0dfe94) | //:RiemannResearch | 197.319 | [Build](https://app.buildbuddy.io/invocation/4a8c28bb-378f-4435-8028-37ffd1995348) |
| [bec4737](https://github.com/Cnoack3/RiemannResearch/commit/bec4737b714907f72a0c62f1f097cbc29a90fc08) | //:RiemannResearch | 191.946 | [Build](https://app.buildbuddy.io/invocation/17e6a627-15a6-45f1-b776-68fe78b84b15) |

Final code checkpoint: `job_FiFArmWFyGNXOAtlBlmLG5bPK0kgfnfo`.
It succeeded, committed and pushed `bec4737b714907f72a0c62f1f097cbc29a90fc08`;
the build scope was the full `//:RiemannResearch` target.
This follow-up changes documentation only. The complete code checkpoint and
the guarded transitive axiom audit are separate evidence records.

## Reproducible guarded Lean audit

```lean
import RiemannResearch.RH.MobiusHeadGreenNormal
import RiemannResearch.RH.MobiusAffineMomentBounds
import RiemannResearch.RH.ExactHeadGreenPrimitive
import RiemannResearch.LinearAlgebra.CumulativeGramEvents

/--
info: 'RiemannResearch.RH.Pareto.MobiusHeadGreen.riemannHypothesis_of_primorial_profile_deficit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  RiemannResearch.RH.Pareto.MobiusHeadGreen.riemannHypothesis_of_primorial_profile_deficit

/--
info: 'RiemannResearch.RH.Pareto.MobiusHeadGreen.exists_primorial_normal_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  RiemannResearch.RH.Pareto.MobiusHeadGreen.exists_primorial_normal_coefficients

/--
info: 'RiemannResearch.RH.Pareto.FloorProfileExtension.hilbertExtension_error_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  RiemannResearch.RH.Pareto.FloorProfileExtension.hilbertExtension_error_split

/--
info: 'RiemannResearch.RH.ExactHeadGreenPrimitive.canonical_energy_eq_primitive_square' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  RiemannResearch.RH.ExactHeadGreenPrimitive.canonical_energy_eq_primitive_square

/--
info: 'RiemannResearch.RH.MobiusAffineProfile.exists_unique_affine_fit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  RiemannResearch.RH.MobiusAffineProfile.exists_unique_affine_fit

/--
info: 'RiemannResearch.RH.MobiusAffineProfile.affine_signed_moment_abs_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  RiemannResearch.RH.MobiusAffineProfile.affine_signed_moment_abs_le

/--
info: 'RiemannResearch.RH.Pareto.ExactHeadGreen.actual_low_conductor_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  RiemannResearch.RH.Pareto.ExactHeadGreen.actual_low_conductor_bound

/--
info: 'RiemannResearch.LinearAlgebra.WeightedGreen.cumulative_gram_event_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  RiemannResearch.LinearAlgebra.WeightedGreen.cumulative_gram_event_identity
```
