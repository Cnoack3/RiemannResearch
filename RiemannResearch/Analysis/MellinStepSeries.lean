/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CesaroFiniteCalculus
import RiemannResearch.RH.ParetoMellinFunctional

/-! The actual Pareto Mellin integral is the convergent first-difference series. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Analysis.Cesaro
open RH.Pareto

private def cell (k : ℕ) : Set ℝ := Ico ((k : ℝ) + 1) ((k : ℝ) + 2)

private theorem cell_floor (k : ℕ) {x : ℝ} (hx : x ∈ cell k) : ⌊x⌋₊ = k + 1 := by
  apply Nat.floor_eq_on_Ico
  simpa only [cell, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hx

private theorem cell_disjoint : Pairwise (Function.onFun Disjoint cell) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  exact hij (Nat.add_right_cancel ((cell_floor i hxi).symm.trans (cell_floor j hxj)))

private theorem cell_union : (⋃ k, cell k) = Ici (1 : ℝ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    change (k : ℝ) + 1 ≤ x ∧ x < (k : ℝ) + 2 at hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    exact le_trans (by linarith : (1 : ℝ) ≤ (k : ℝ) + 1) hk.1
  · intro hx
    have hx0 : 0 ≤ x := le_trans zero_le_one hx
    have hf : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).2 (by simpa using hx)
    let k := ⌊x⌋₊ - 1
    have hk : k + 1 = ⌊x⌋₊ := Nat.sub_add_cancel hf
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    have hlo := Nat.floor_le hx0
    have hhi := Nat.lt_floor_add_one x
    rw [← hk] at hlo hhi
    simpa only [cell, Set.mem_Ico, Nat.cast_add, Nat.cast_one,
      add_assoc, one_add_one_eq_two] using And.intro hlo hhi

private theorem integral_power_cell (s : ℂ) (hs : s ≠ 0) (k : ℕ) :
    (∫ x in cell k, (x : ℂ) ^ (-s - 1)) = mellinFirst s (k + 1) / s := by
  have hab : (k : ℝ) + 1 ≤ (k : ℝ) + 2 := by linarith
  have hz : (0 : ℝ) ∉ uIcc ((k : ℝ) + 1) ((k : ℝ) + 2) := by
    rw [uIcc_of_le hab]
    intro h
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [h.1]
  have he : -s - 1 ≠ (-1 : ℂ) := by
    intro h
    apply hs
    linear_combination -h
  unfold cell
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    integral_cpow (Or.inr ⟨he, hz⟩)]
  rw [show -s - 1 + 1 = -s by ring]
  simp only [mellinFirst, Nat.cast_add, Nat.cast_one, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [show (k : ℂ) + 1 + 1 = (k : ℂ) + 2 by ring]
  field_simp
  ring

/-- Actual integrability of the step-form Mellin integrand in the continuity half-plane. -/
theorem stepMellin_integrable (f : ThresholdHilbert) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    IntegrableOn (fun x : ℝ => (hilbertSequence f ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1))
      (Ioi 1) := by
  apply (paretoMellin_integrable f s hs).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one hx))
  rw [Complex.cpow_sub (-s) 1 hx0, Complex.cpow_one]
  unfold mellinWeightedStep paretoMellinKernel
  ring

private theorem integral_step_cell (f : ThresholdHilbert) (s : ℂ) (hs : s ≠ 0) (k : ℕ) :
    (∫ x in cell k, (hilbertSequence f ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1)) =
      (hilbertSequence f (k + 1) : ℂ) * (mellinFirst s (k + 1) / s) := by
  calc
    _ = ∫ x in cell k, (hilbertSequence f (k + 1) : ℂ) * (x : ℂ) ^ (-s - 1) := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro x hx
      dsimp only
      rw [cell_floor k hx]
    _ = _ := by rw [integral_const_mul, integral_power_cell s hs]

/-- A bounded physical step has an integrable Mellin integrand throughout Re(s)>0.
Source: user-provided mathematical completion, Section 5. -/
theorem stepMellin_integrable_of_bounded (f : ThresholdHilbert) (B : ℝ)
    (hB : ∀ n, |hilbertSequence f n| ≤ B) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (hilbertSequence f ⌊x⌋₊ : ℂ) *
      (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
  have hmeas : Measurable (fun x : ℝ => (hilbertSequence f ⌊x⌋₊ : ℂ) *
      (x : ℂ) ^ (-s - 1)) :=
    (Complex.continuous_ofReal.measurable.comp
      ((measurable_of_countable (hilbertSequence f)).comp Nat.measurable_floor)).mul
      (Complex.continuous_ofReal.measurable.pow_const (-s - 1))
  have hi := (integrableOn_Ioi_rpow_of_lt
    (by linarith : -s.re - 1 < -1) (by norm_num : (0 : ℝ) < 1)).const_mul B
  apply hi.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
  exact mul_le_mul_of_nonneg_right (hB ⌊x⌋₊) (Real.rpow_nonneg hx0.le _)

/-- Countable cell integration supplies an actual HasSum whenever its full integrand is integrable. -/
theorem hasSum_first_mellin_pairing_of_integrable (f : ThresholdHilbert) (s : ℂ)
    (hs0 : s ≠ 0)
    (hint : IntegrableOn (fun x : ℝ => (hilbertSequence f ⌊x⌋₊ : ℂ) *
      (x : ℂ) ^ (-s - 1)) (Ioi 1)) :
    HasSum (fun k : ℕ => mellinFirst s (k + 1) * (hilbertSequence f (k + 1) : ℂ))
      (s * paretoMellin f s) := by
  have hi : IntegrableOn
      (fun x : ℝ => (hilbertSequence f ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1)) (⋃ k, cell k) := by
    rw [cell_union, integrableOn_Ici_iff_integrableOn_Ioi]
    exact hint
  have h := hasSum_integral_iUnion (fun k => (show MeasurableSet (cell k) from measurableSet_Ico))
    cell_disjoint hi
  simp_rw [integral_step_cell f s hs0] at h
  rw [cell_union, integral_Ici_eq_integral_Ioi, ← paretoMellin_eq_step_integral f s] at h
  have hm := h.mul_left s
  have he : (fun k : ℕ => s * ((hilbertSequence f (k + 1) : ℂ) *
      (mellinFirst s (k + 1) / s))) =
      (fun k : ℕ => mellinFirst s (k + 1) * (hilbertSequence f (k + 1) : ℂ)) := by
    funext k
    field_simp
  rw [he] at hm
  exact hm

/-- The original all-Hilbert statement, with its existing name and signature preserved. -/
theorem hasSum_first_mellin_pairing (f : ThresholdHilbert) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    HasSum (fun k : ℕ => mellinFirst s (k + 1) * (hilbertSequence f (k + 1) : ℂ))
      (s * paretoMellin f s) := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  exact hasSum_first_mellin_pairing_of_integrable f s hs0 (stepMellin_integrable f s hs)

/-- Bounded physical vectors have the actual first-difference series on the full positive half-plane. -/
theorem hasSum_first_mellin_pairing_of_bounded (f : ThresholdHilbert) (B : ℝ)
    (hB : ∀ n, |hilbertSequence f n| ≤ B) (s : ℂ) (hs : 0 < s.re) :
    HasSum (fun k : ℕ => mellinFirst s (k + 1) * (hilbertSequence f (k + 1) : ℂ))
      (s * paretoMellin f s) := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  exact hasSum_first_mellin_pairing_of_integrable f s hs0
    (stepMellin_integrable_of_bounded f B hB s hs)

end RiemannResearch.Analysis.Cesaro
