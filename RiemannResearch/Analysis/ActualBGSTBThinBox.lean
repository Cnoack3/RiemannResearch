/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualBGSTBDensity
import RiemannResearch.Analysis.ActualZeroCountUpper
import RiemannResearch.Analysis.ActualZeroDensityWindow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.LeftRight

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


/-- A closed lower edge, imposed at every sufficiently large real height,
is equivalent to the open two-sided box of BGSTB Theorem 2. For a zero
in the open lower height window one can increase T slightly, giving a
strictly smaller horizontal width. Reflection supplies the other edge. -/
theorem bgstbThinBox_iff_eventually_closed_lower :
    BGSTBThinBox ↔ ∀ᶠ T : ℝ in atTop, ∀ ρ ∈ cutoff T, T ^ (3 / 8 : ℝ) < ρ.im →
      1 / 2 - 1 / (2 * Real.log T) ≤ ρ.re := by
  constructor
  · intro h
    filter_upwards [h] with T hT
    intro ρ hρ hγ
    linarith only [(abs_lt.mp (hT ρ hρ hγ)).1]
  · intro h
    obtain ⟨U, hU⟩ := eventually_atTop.1 h
    filter_upwards [eventually_ge_atTop U, eventually_gt_atTop (1 : ℝ)] with T hUT hT
    intro ρ hρ hγ
    have hc : ContinuousAt (fun t : ℝ => t ^ (3 / 8 : ℝ)) T := by fun_prop (disch := positivity)
    have he : ∀ᶠ t : ℝ in 𝓝 T, t ^ (3 / 8 : ℝ) < ρ.im := hc.tendsto.eventually (gt_mem_nhds hγ)
    obtain ⟨t, hTt, htγ⟩ := he.exists_gt
    obtain ⟨hz, hip, hiT⟩ := mem_cutoff.mp hρ
    have hmem : ρ ∈ cutoff t := mem_cutoff.mpr ⟨hz, hip, hiT.trans hTt.le⟩
    have hleft := hU t (hUT.trans hTt.le) ρ hmem htγ
    have hright := hU t (hUT.trans hTt.le) (reflect ρ) (reflect_mem hmem)
      (by simpa only [reflect_im] using htγ)
    rw [reflect_re] at hright
    have hlog := Real.log_lt_log (zero_lt_one.trans hT) hTt
    have hwidth : 1 / (2 * Real.log t) < 1 / (2 * Real.log T) :=
      one_div_lt_one_div_of_lt (mul_pos (by norm_num) (Real.log_pos hT))
        (by linarith only [hlog])
    exact abs_lt.mpr ⟨by linarith, by linarith⟩


/-- An inclusive left cutoff keeps the complement of the strictly right
tail. This identity includes zeros lying at either of the two boundaries. -/
theorem rightInclusiveCount_left_add_rightStrictTail (T d : ℝ) :
    rightInclusiveCount T (1 / 2 - d) + rightStrictTail T d = (Ncount 0 T : ℝ) := by
  let f := fun ρ : ℂ => if 1 / 2 - d ≤ ρ.re then (1 : ℝ) else 0
  change realSum T f + realSum T (fun ρ => if 1 / 2 + d < ρ.re then 1 else 0) = _
  rw [← realSum_reflect T f, ← realSum_add, ← realSum_one T]
  congr 1
  funext ρ
  dsimp only [f]
  rw [reflect_re]
  by_cases h : 1 / 2 + d < ρ.re
  · rw [if_neg (show ¬ (1 / 2 - d ≤ 1 - ρ.re) by linarith), if_pos h, zero_add]
  · rw [if_pos (show 1 / 2 - d ≤ 1 - ρ.re by linarith), if_neg h, add_zero]


/-- Under Theorem 3's density hypothesis, an inclusive cutoff on the
left side retains the total count up to o(N(T)/e). -/
theorem bgstb_left_cutoff_deficit_isLittleO_count_div_exp {b : ℝ} (hb : 1 / 2 < b)
    (h : BGSTBStripDensity b) :
    (fun T : ℝ => (Ncount 0 T : ℝ) - rightInclusiveCount T (1 / 2 - 1 / (2 * Real.log T)))
      =o[atTop] (fun T : ℝ => (Ncount 0 T : ℝ) / Real.exp 1) := by
  apply Asymptotics.IsBigO.trans_isLittleO _ (bgstb_endpoint_isLittleO_count_div_exp hb h)
  apply Asymptotics.IsBigO.of_bound'
  filter_upwards with T
  let d := 1 / (2 * Real.log T)
  have he := rightInclusiveCount_left_add_rightStrictTail T d
  have hn := sub_nonneg.mpr (rightInclusiveCount_le_count T (1 / 2 - d))
  have hp := rightInclusiveCount_nonneg T (1 / 2 + d)
  change ‖(Ncount 0 T : ℝ) - rightInclusiveCount T (1 / 2 - d)‖ ≤
    ‖rightInclusiveCount T (1 / 2 + d)‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hn, abs_of_nonneg hp]
  linarith only [he, rightStrictTail_le_inclusive T d]

/-- Count both boundary lines among the exceptions. Under Theorem 2
every such occurrence belongs to the initial height segment. -/
theorem bgstb_outside_count_le_initial_of_thinBox (h : BGSTBThinBox) :
    ∀ᶠ T : ℝ in atTop,
      realSum T (fun ρ => if 1 / (2 * Real.log T) ≤ |ρ.re - 1 / 2| then 1 else 0) ≤
        (Ncount 0 (T ^ (3 / 8 : ℝ)) : ℝ) := by
  classical
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with T hh hT
  let H := T ^ (3 / 8 : ℝ)
  have hHT : H ≤ T := Real.rpow_le_self_of_one_le hT.le (by norm_num)
  have hf : (cutoff T).filter (fun ρ => ρ.im ≤ H) = cutoff H := by
    ext ρ
    simp only [Finset.mem_filter, mem_cutoff]
    grind
  calc
    _ ≤ realSum T (fun ρ => if ρ.im ≤ H then 1 else 0) := by
      apply realSum_mono
      intro ρ hρ
      by_cases hz : ρ.im ≤ H
      · rw [if_pos hz]
        split <;> norm_num
      · rw [if_neg hz, if_neg (hh ρ hρ (lt_of_not_ge hz)).not_ge]
    _ = _ := by
      rw [realSum, count_eq_sum]
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter, hf, Nat.cast_sum]


/-- Positive half-width makes the two closed exceptional tails disjoint.
Reflection identifies their counts including multiplicity and boundary atoms. -/
theorem closed_displacement_count_eq_twice_right (T : ℝ) {d : ℝ} (hd : 0 < d) :
    realSum T (fun ρ => if d ≤ |ρ.re - 1 / 2| then 1 else 0) =
      2 * rightInclusiveCount T (1 / 2 + d) := by
  let f := fun ρ : ℂ => if 1 / 2 + d ≤ ρ.re then (1 : ℝ) else 0
  change _ = 2 * realSum T f
  calc
    _ = realSum T (fun ρ => f ρ + f (reflect ρ)) := ?_
    _ = _ := by rw [realSum_add, realSum_reflect, two_mul]
  congr 1
  funext ρ
  dsimp only [f]
  rw [reflect_re]
  by_cases hr : 1 / 2 + d ≤ ρ.re
  · have hl : ¬ 1 / 2 + d ≤ 1 - ρ.re := by linarith
    have ha : d ≤ |ρ.re - 1 / 2| := by linarith only [hr, le_abs_self (ρ.re - 1 / 2)]
    rw [if_pos ha, if_pos hr, if_neg hl, add_zero]
  · by_cases hl : 1 / 2 + d ≤ 1 - ρ.re
    · have ha : d ≤ |ρ.re - 1 / 2| := by linarith only [hl, neg_le_abs (ρ.re - 1 / 2)]
      rw [if_pos ha, if_neg hr, if_pos hl, zero_add]
    · have ha : |ρ.re - 1 / 2| < d := abs_lt.mpr ⟨by linarith, by linarith⟩
      rw [if_neg ha.not_ge, if_neg hr, if_neg hl, add_zero]

/-- Under the density assumption of Theorem 3, the total number of
occurrences outside the open box is little-o of T/e, counting both edges. -/
theorem bgstb_outside_isLittleO_height_div_exp {b : ℝ} (hb : 1 / 2 < b)
    (h : BGSTBStripDensity b) :
    (fun T : ℝ => realSum T (fun ρ => if 1 / (2 * Real.log T) ≤ |ρ.re - 1 / 2| then 1 else 0))
      =o[atTop] (fun T : ℝ => T / Real.exp 1) := by
  apply ((bgstb_endpoint_isLittleO_height_div_exp hb h).const_mul_left 2).congr' _ .rfl
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  exact (closed_displacement_count_eq_twice_right T
    (one_div_pos.mpr (mul_pos (by norm_num) (Real.log_pos hT)))).symm

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
