/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CompensatedTwoCoefficientCriterion

/-!
# Original conductor coordinates of the compact source

Source: the user-provided source-resolvent continuation, 7 October 2026.
The existing coefficient duality supplies the literal source (3,1,0,...).
This does not truncate the remaining Gram interactions or claim inverse transport.
-/
noncomputable section
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- Exact signed compact source pairing, in the original residue coordinates. -/
theorem twoThreeDual_inner_eq_original_coefficients (x : ThresholdHilbert) :
    inner ℝ twoThreeDual x =
      3 * coefficientCLM 2 x + coefficientCLM 3 x := by
  unfold twoThreeDual
  rw [inner_sub_left, real_inner_smul_left,
    mobiusRieszHilbert_inner, mobiusRieszHilbert_inner]
  simp only [coefficientCLM, neg_apply]
  ring

/-- Original atom g_(j+2): source vector is exactly (3,1,0,...).
This is a coordinate identity, without dropping any later conductor. -/
theorem twoThreeDual_inner_residueAtom (j : ℕ) :
    inner ℝ twoThreeDual (residueAtom j) =
      3 * (if j = 0 then 1 else 0) + (if j = 1 then 1 else 0) := by
  rw [twoThreeDual_inner_eq_original_coefficients]
  have h0 := coefficientCLM_biorthogonal 0 j
  have h1 := coefficientCLM_biorthogonal 1 j
  simpa only [Nat.zero_add, Nat.reduceAdd, eq_comm] using
    congrArg₂ (fun a b : ℝ => 3 * a + b) h0 h1

end RiemannResearch.RH.Pareto.CoefficientStabilization
