/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoEquivalence
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic.Ring

/-!
# Orthonormal basis transfer from Pareto to inverse-square Q

Source: Bagchi, Proc. Indian Acad. Sci. Math. Sci. 116 (2006), pp. 137--146,
https://arxiv.org/abs/math/0607733, p. 138, for equivalence of comparable
weighted sequence spaces. The explicit constants and the complete sequence
re-encoding are supplied by QParetoEquivalence and ZetaTwoParetoTransfer.

Every finite synthesis of an arbitrary P-orthonormal family has uniform
two-sided coefficient bounds after re-encoding under Q. This applies to
residue Gram--Schmidt families but does not assert ambient completeness.
-/

noncomputable section
open scoped BigOperators
open RiemannResearch.RH

namespace RiemannResearch.RH.QParetoOrthonormalTransfer

/-- Every finite P-orthonormal synthesis stays uniformly conditioned when
the same physical functions are represented under Q. -/
theorem pareto_orthonormal_transfer_bounds {ι : Type*} (p : ι → Pareto.ThresholdHilbert)
    (hp : Orthonormal ℝ p) (s : Finset ι) (c : ι → ℝ) :
    (∑ i ∈ s, (c i) ^ 2) ≤ ZetaTwoProbability.zetaTwo *
      ‖∑ i ∈ s, c i • QParetoEquivalence.toQ (p i)‖ ^ 2 ∧
    ZetaTwoProbability.zetaTwo *
      ‖∑ i ∈ s, c i • QParetoEquivalence.toQ (p i)‖ ^ 2 ≤
      2 * (∑ i ∈ s, (c i) ^ 2) := by
  classical
  have hn : ‖∑ i ∈ s, c i • p i‖ ^ 2 = ∑ i ∈ s, (c i) ^ 2 := by
    have hh := hp.inner_sum c c s
    simpa only [real_inner_self_eq_norm_sq, RCLike.star_def, starRingEnd_apply,
      star_trivial, ← pow_two] using hh
  have hm : (∑ i ∈ s, c i • QParetoEquivalence.toQ (p i)) =
      QParetoEquivalence.toQ (∑ i ∈ s, c i • p i) := by
    change (∑ i ∈ s, c i • QParetoEquivalence.toQLinear (p i)) =
      QParetoEquivalence.toQLinear (∑ i ∈ s, c i • p i)
    simp
  rw [hm]
  constructor
  · have h := ZetaTwoParetoTransfer.toPareto_norm_sq_le
      (QParetoEquivalence.toQ (∑ i ∈ s, c i • p i))
    simpa only [QParetoEquivalence.toPareto_toQ, hn] using h
  · have h := ZetaTwoParetoTransfer.zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq
      (QParetoEquivalence.toQ (∑ i ∈ s, c i • p i))
    simpa only [QParetoEquivalence.toPareto_toQ, hn] using h

end RiemannResearch.RH.QParetoOrthonormalTransfer
