/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualBGSTBDensity
import RiemannResearch.Analysis.ActualZeroCountUpper
import RiemannResearch.Analysis.ActualZeroDensityWindow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Strong zero density and exact Selberg slope two under the BGSTB thin box

Source for the thin box and the low-height split: BGSTB, Theorem 2 and
Section 6, <https://arxiv.org/abs/2306.04799>. Applying the box at each
zero's own height also gives uniform control up to real part 1.
-/

noncomputable section
open Filter Set Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- The thin-box assumption in BGSTB Theorem 2, at all sufficiently large
real heights. The strict horizontal boundary matters for the inclusive count. -/
def BGSTBThinBox : Prop :=
  ∀ᶠ T : ℝ in atTop, ∀ ρ ∈ cutoff T, T ^ (3 / 8 : ℝ) < ρ.im →
    |ρ.re - 1 / 2| < 1 / (2 * Real.log T)

private theorem count_eq_of_empty_upper_window {H T σ : ℝ} (hHT : H ≤ T)
    (h : ∀ ρ ∈ cutoff T, H < ρ.im → ρ.re < σ) :
    rightInclusiveCount T σ = rightInclusiveCount H σ := by
  rw [rightInclusiveCount_split hHT]
  suffices hz : rightInclusiveWindow H T σ = 0 by rw [hz, add_zero]
  unfold rightInclusiveWindow realSum
  apply Finset.sum_eq_zero
  intro ρ hρ
  have hw : ¬ (H < ρ.im ∧ σ ≤ ρ.re) := fun hw => (h ρ hρ hw.1).not_ge hw.2
  simp [hw]

/-- Under the thin-box condition only finitely many zeros have real part
at least 3/4. Test each zero at its own height. -/
private theorem eventually_count_quarter_fixed (h : BGSTBThinBox) :
    ∃ U : ℝ, ∀ T ≥ U, ∀ σ : ℝ, 3 / 4 ≤ σ →
      rightInclusiveCount T σ = rightInclusiveCount U σ := by
  have he : ∀ᶠ t : ℝ in atTop, ∀ ρ ∈ cutoff t, ρ.im = t → ρ.re < 3 / 4 := by
    filter_upwards [h, Real.tendsto_log_atTop.eventually_ge_atTop 2,
      eventually_gt_atTop (1 : ℝ)] with t ht hL ht₁
    intro ρ hρ him
    have hp : t ^ (3 / 8 : ℝ) < ρ.im := by
      rw [him]
      simpa using Real.rpow_lt_rpow_of_exponent_lt ht₁ (by norm_num : (3 / 8 : ℝ) < 1)
    have hw := (abs_lt.mp (ht ρ hρ hp)).2
    have hw' : 1 / (2 * Real.log t) ≤ (1 / 4 : ℝ) := by
      apply (div_le_iff₀ (by linarith : 0 < 2 * Real.log t)).mpr
      linarith
    linarith
  obtain ⟨U, hU⟩ := eventually_atTop.1 he
  refine ⟨U, fun T hT σ hσ => count_eq_of_empty_upper_window hT ?_⟩
  intro ρ hρ him
  obtain ⟨hz, hpos, _⟩ := mem_cutoff.mp hρ
  exact (hU ρ.im him.le ρ (mem_cutoff.mpr ⟨hz, hpos, le_rfl⟩) rfl).trans_le hσ

/-- Any fixed finite positive-height head is uniformly negligible compared
to the critical density power up to real part 1. -/
private theorem fixed_head_eventually_small (U ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ σ : ℝ,
      rightInclusiveCount U σ ≤ ε * T ^ (2 * (1 - σ)) := by
  classical
  let s := insert 0 ((cutoff U).image Complex.re)
  have hne : s.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  let b := s.max' hne
  have hb : b < 1 := by
    have hm : b ∈ s := s.max'_mem hne
    rcases Finset.mem_insert.mp hm with he | hm
    · rw [he]; norm_num
    · obtain ⟨ρ, hρ, he⟩ := Finset.mem_image.mp hm
      rw [← he]
      exact (mem_cutoff.mp hρ).1.2.2
  have hpow := (tendsto_rpow_atTop (show 0 < 2 * (1 - b) by linarith)).eventually_ge_atTop
    ((Ncount 0 U : ℝ) / ε)
  filter_upwards [hpow, eventually_ge_atTop (1 : ℝ)] with T hT hT₁
  intro σ
  by_cases hs : σ ≤ b
  · calc
      _ ≤ (Ncount 0 U : ℝ) := rightInclusiveCount_le_count _ _
      _ ≤ ε * T ^ (2 * (1 - b)) := by
        simpa only [mul_comm] using (div_le_iff₀ hε).mp hT
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hT₁ (by linarith)) hε.le
  · have hz : rightInclusiveCount U σ = 0 := by
      unfold rightInclusiveCount realSum
      apply Finset.sum_eq_zero
      intro ρ hρ
      have hmem : ρ.re ∈ s := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hρ)
      have hlt : ρ.re < σ := (s.le_max' _ hmem).trans_lt (lt_of_not_ge hs)
      simp [if_neg hlt.not_ge]
    rw [hz]
    exact mul_nonneg hε.le (Real.rpow_nonneg (by linarith) _)

/-- The thin box gives the uniform little-o estimate through real part 1
with no far-density inputs. Below 3/4 the unaccounted head has height T^(3/8);
above 3/4 it is contained in a fixed finite head. -/
theorem bgstbStripDensity_one_of_thinBox (h : BGSTBThinBox) : BGSTBStripDensity 1 := by
  obtain ⟨U, hU⟩ := eventually_count_quarter_fixed h
  obtain ⟨C, hC, hcount⟩ := exists_count_le_height_log
  intro ε hε
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).bound (div_pos hε hC)
  filter_upwards [h, hl, fixed_head_eventually_small U ε hε, eventually_ge_atTop U,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 8)).eventually_ge_atTop 9,
    eventually_gt_atTop (1 : ℝ)] with T hbox hlT hhead hTU h9 hT
  intro σ hσ
  by_cases hhigh : 3 / 4 ≤ σ
  · rw [hU T hTU σ hhigh]
    exact hhead σ
  have hTp : 0 < T := zero_lt_one.trans hT
  have hL := Real.log_pos hT
  have hshort : rightInclusiveCount T σ = rightInclusiveCount (T ^ (3 / 8 : ℝ)) σ := by
    apply count_eq_of_empty_upper_window (Real.rpow_le_self_of_one_le hT.le (by norm_num))
    intro ρ hρ hh
    have hc := (abs_lt.mp (hbox ρ hρ hh)).2
    linarith only [hc, hσ.1]
  change ‖Real.log T‖ ≤ ε / C * ‖T ^ (1 / 8 : ℝ)‖ at hlT
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hL,
    abs_of_pos (Real.rpow_pos_of_pos hTp _)] at hlT
  have hlog : C * Real.log T ≤ ε * T ^ (1 / 8 : ℝ) := by
    calc
      _ ≤ C * (ε / C * T ^ (1 / 8 : ℝ)) := mul_le_mul_of_nonneg_left hlT hC.le
      _ = _ := by field_simp
  have hlshort : Real.log (T ^ (3 / 8 : ℝ)) ≤ Real.log T := by
    rw [Real.log_rpow hTp]; linarith
  have hpos := (Real.rpow_pos_of_pos hTp (3 / 8)).le
  rw [hshort]
  calc
    _ ≤ (Ncount 0 (T ^ (3 / 8 : ℝ)) : ℝ) := rightInclusiveCount_le_count _ _
    _ ≤ C * T ^ (3 / 8 : ℝ) * Real.log (T ^ (3 / 8 : ℝ)) := hcount _ h9
    _ ≤ C * T ^ (3 / 8 : ℝ) * Real.log T := mul_le_mul_of_nonneg_left hlshort (mul_nonneg hC.le hpos)
    _ = (C * Real.log T) * T ^ (3 / 8 : ℝ) := by ring
    _ ≤ (ε * T ^ (1 / 8 : ℝ)) * T ^ (3 / 8 : ℝ) := mul_le_mul_of_nonneg_right hlog hpos
    _ = ε * T ^ (1 / 2 : ℝ) := by rw [mul_assoc, ← Real.rpow_add hTp]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT.le
      (by linarith only [le_of_not_ge hhigh])) hε.le

theorem uniformSelbergDensity_two_of_thinBox (h : BGSTBThinBox) : UniformSelbergDensity 2 :=
  uniformSelbergDensity_two_of_full_bgstb (bgstbStripDensity_one_of_thinBox h)

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.uniformSelbergDensity_two_of_thinBox' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms uniformSelbergDensity_two_of_thinBox

end RiemannResearch.Analysis.ActualZeroOrdinate
