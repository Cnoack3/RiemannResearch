/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.DilationWaveletAlgebra
import RiemannResearch.RH.ParetoCoordinateEvaluation

/-!
# A persistent coordinate obstruction for far two-seed dilations

Source: independently derived arithmetic audit, 15 September 2026. Start
with the actual seeds 2 and 3, and then allow every dilation index greater
than 6. All these generators vanish at physical coordinate 6. Their closed
span therefore stays at squared distance at least 1/42 from the constant.
This is a restricted arithmetic family; it does not obstruct the full legal
span with every positive dilation. Strict finite improvement for this family
is established in the companion analytic note, not in this module.
-/

namespace RiemannResearch.RH.Pareto.FarDilationBlindSpot
noncomputable section

/-- The original two seeds and all their dilations beyond the common period six. -/
def generators : Set ThresholdHilbert :=
  {f | ∃ (a m : ℕ) (ha : 0 < a) (hm : 0 < m),
    (a = 2 ∨ a = 3) ∧ (m = 1 ∨ 6 < m) ∧ f = digitHilbert a m ha hm}

def finiteSpan : Submodule ℝ ThresholdHilbert := Submodule.span ℝ generators

def closedSpan : Submodule ℝ ThresholdHilbert := finiteSpan.topologicalClosure

theorem generator_legal {f : ThresholdHilbert} (hf : f ∈ generators) :
    f ∈ hilbertLegalSubspace ({2, 3} : Set ℕ) := by
  obtain ⟨a, m, ha, hm, hseed, _, rfl⟩ := hf
  change hilbertSequence (digitHilbert a m ha hm) ∈ legalSeedSpan ({2, 3} : Set ℕ)
  rw [hilbertSequence_digitHilbert, digitSequence_eq_scaled_generator a m hm]
  apply (legalSeedSpan ({2, 3} : Set ℕ)).smul_mem
  apply dilation_generator_mem _ _ hm
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hseed

theorem finiteSpan_le_legal : finiteSpan ≤ hilbertLegalSubspace ({2, 3} : Set ℕ) :=
  Submodule.span_le.mpr fun _ hf => generator_legal hf

theorem generator_six_zero {f : ThresholdHilbert} (hf : f ∈ generators) :
    hilbertSequence f 6 = 0 := by
  obtain ⟨a, m, ha, hm, hseed, hbudget, rfl⟩ := hf
  rw [hilbertSequence_digitHilbert]
  rcases hbudget with rfl | hm6
  · rcases hseed with rfl | rfl <;> norm_num [digitSequence]
  · simp [digitSequence, Nat.div_eq_of_lt hm6]

theorem finiteSpan_le_evaluation_kernel : finiteSpan ≤ (physicalEvaluationCLM 5).ker := by
  apply Submodule.span_le.mpr
  intro f hf
  change physicalEvaluationCLM 5 f = 0
  simpa using generator_six_zero hf

theorem closedSpan_le_evaluation_kernel : closedSpan ≤ (physicalEvaluationCLM 5).ker := by
  exact Submodule.topologicalClosure_minimal finiteSpan finiteSpan_le_evaluation_kernel
    (physicalEvaluationCLM 5).isClosed_ker

/-- Coordinate continuity preserves the blind spot under the full Hilbert closure. -/
theorem closedSpan_six_zero {f : ThresholdHilbert} (hf : f ∈ closedSpan) :
    hilbertSequence f 6 = 0 := by
  have h := closedSpan_le_evaluation_kernel hf
  change physicalEvaluationCLM 5 f = 0 at h
  simpa using h

private theorem point_norm_sq (n : ℕ) : ‖paretoPointHilbert n‖ ^ 2 = paretoWeight n := by
  have h := inner_paretoPoint (paretoPointHilbert n) n
  simpa only [hilbertGibbsPhysical_paretoPoint, ↓reduceIte, mul_one,
    real_inner_self_eq_norm_sq] using h

/-- A single omitted physical coordinate gives a lower bound in the complete norm. -/
private theorem coordinate_error_floor (n : ℕ) (f : ThresholdHilbert)
    (hf : hilbertSequence f (n + 1) = 0) : paretoWeight n ≤ ‖hilbertOne - f‖ ^ 2 := by
  have hi : inner ℝ (hilbertOne - f) (paretoPointHilbert n) = paretoWeight n := by
    rw [inner_sub_left, inner_paretoPoint, inner_paretoPoint,
      hilbertGibbs_one_physical, hilbertGibbsPhysical_eq, hf]
    ring
  have hc := norm_inner_le_norm (𝕜 := ℝ) (hilbertOne - f) (paretoPointHilbert n)
  rw [hi, Real.norm_eq_abs, abs_of_pos (paretoWeight_pos n)] at hc
  have hs : (paretoWeight n) ^ 2 ≤
      (‖hilbertOne - f‖ * ‖paretoPointHilbert n‖) ^ 2 := by
    nlinarith [paretoWeight_pos n, norm_nonneg (hilbertOne - f),
      norm_nonneg (paretoPointHilbert n)]
  rw [mul_pow, point_norm_sq] at hs
  nlinarith [paretoWeight_pos n]

/-- The actual restricted two-seed family has a fixed positive full-error floor. -/
theorem closedSpan_error_floor {f : ThresholdHilbert} (hf : f ∈ closedSpan) :
    (1 : ℝ) / 42 ≤ ‖hilbertOne - f‖ ^ 2 := by
  have h := coordinate_error_floor 5 f (closedSpan_six_zero hf)
  norm_num [paretoWeight] at h ⊢
  exact h

theorem hilbertOne_not_mem : hilbertOne ∉ closedSpan := by
  intro hf
  have h := closedSpan_error_floor hf
  norm_num at h

end
end RiemannResearch.RH.Pareto.FarDilationBlindSpot
