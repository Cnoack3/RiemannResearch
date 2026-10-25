/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.UnitVectorVariance
import RiemannResearch.RH.ThresholdHilbertL1
import RiemannResearch.RH.ThresholdHilbertSpace
import Mathlib.Tactic.Linarith

/-!
# Exact equality cases for the complete Pareto L1/L2 bounds

Source: the user's norm-convergence and equality-case discussion, 25 October
2026. Equality in L1 <= L2 means constant absolute value. Equality of the
absolute mean and L2 norm means a constant signed function. Physical constants
are stated only at positive integers because coordinate zero is an anchor.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis.UnitVectorVariance

theorem hilbert_eq_smul_one_iff (f : ThresholdHilbert) (c : ℝ) :
    f = c • hilbertOne ↔ ∀ n : ℕ, 0 < n → hilbertSequence f n = c := by
  have hs : hilbertSequence (c • hilbertOne) = c • hilbertSequence hilbertOne :=
    hilbertSequenceLinear.map_smul c hilbertOne
  constructor
  · intro hf n hn
    rw [hf, hs, hilbertOne_sequence]
    simp [zeroAnchor, Nat.ne_of_gt hn]
  · intro hf
    apply hilbertSequence_injective
    funext n
    by_cases hn : n = 0
    · subst n
      simp
    · rw [hs, hilbertOne_sequence, hf n (Nat.pos_of_ne_zero hn)]
      simp [zeroAnchor, hn]

theorem abs_inner_one_le_hilbertL1Norm (f : ThresholdHilbert) :
    |inner ℝ f hilbertOne| ≤ hilbertL1Norm f := by
  have hl := inner_one_le_hilbertL1Norm (-f)
  rw [inner_neg_left, hilbertL1Norm_neg] at hl
  exact abs_le.mpr ⟨by linarith, inner_one_le_hilbertL1Norm f⟩

/-- The exact variance of the signed physical function. -/
theorem hilbert_centered_norm_sq (f : ThresholdHilbert) :
    ‖f - (inner ℝ f hilbertOne) • hilbertOne‖ ^ 2 =
      ‖f‖ ^ 2 - (inner ℝ f hilbertOne) ^ 2 := by
  simpa only [real_inner_comm hilbertOne f] using
    centered_norm_sq hilbertOne f hilbertOne_norm_sq

/-- The L1/L2 square gap is the variance of the absolute physical function. -/
theorem hilbertAbs_centered_norm_sq (f : ThresholdHilbert) :
    ‖hilbertAbs f - hilbertL1Norm f • hilbertOne‖ ^ 2 =
      ‖f‖ ^ 2 - hilbertL1Norm f ^ 2 := by
  simpa only [← hilbertL1Norm_eq_inner_abs, hilbertAbs_norm] using
    hilbert_centered_norm_sq (hilbertAbs f)

theorem abs_inner_one_eq_norm_iff_constant (f : ThresholdHilbert) :
    |inner ℝ f hilbertOne| = ‖f‖ ↔
      ∃ c : ℝ, ∀ n : ℕ, 0 < n → hilbertSequence f n = c := by
  have hm : inner ℝ f hilbertOne = inner ℝ hilbertOne f := real_inner_comm _ _
  rw [hm]
  have h := abs_inner_eq_norm_iff_exists_smul hilbertOne f hilbertOne_norm_sq
  simp only [hilbert_eq_smul_one_iff] at h
  exact h

theorem hilbertL1Norm_eq_norm_iff_abs_smul (f : ThresholdHilbert) :
    hilbertL1Norm f = ‖f‖ ↔ ∃ c : ℝ, hilbertAbs f = c • hilbertOne := by
  have hm : inner ℝ hilbertOne (hilbertAbs f) = hilbertL1Norm f := by
    rw [real_inner_comm, ← hilbertL1Norm_eq_inner_abs]
  have h := abs_inner_eq_norm_iff_exists_smul hilbertOne (hilbertAbs f)
    hilbertOne_norm_sq
  simpa only [hm, abs_of_nonneg (hilbertL1Norm_nonneg f), hilbertAbs_norm] using h

/-- Constant magnitude, rather than constant sign, is the precise equality case. -/
theorem hilbertL1Norm_eq_norm_iff_abs_constant (f : ThresholdHilbert) :
    hilbertL1Norm f = ‖f‖ ↔
      ∃ c : ℝ, ∀ n : ℕ, 0 < n → |hilbertSequence f n| = c := by
  rw [hilbertL1Norm_eq_norm_iff_abs_smul]
  simp only [hilbert_eq_smul_one_iff, hilbertAbs_sequence]

theorem hilbertL1Norm_sub_tendsto_zero {u : ℕ → ThresholdHilbert}
    {f : ThresholdHilbert} (hu : Tendsto u atTop (𝓝 f)) :
    Tendsto (fun M => hilbertL1Norm (u M - f)) atTop (𝓝 0) := by
  apply hilbertL1Norm_tendsto_zero_of_norm
  have hc : Tendsto (fun _ : ℕ => f) atTop (𝓝 f) := tendsto_const_nhds
  simpa only [sub_self, norm_zero] using (hu.sub hc).norm

end RiemannResearch.RH.Pareto
