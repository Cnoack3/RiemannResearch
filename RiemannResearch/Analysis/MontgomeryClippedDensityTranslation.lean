import RiemannResearch.Analysis.MontgomeryGapRowDuality

/-! # Translation bounds for smooth clipped ordinate windows

A bounded error in the cumulative height count pairs with the local change
of the model density and the top boundary strip. The lower boundary term
vanishes for cumulative functions with value zero at the origin.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap

/-- Integrate a measurable bounded multiplier against an interval-integrable density. -/
theorem intervalIntegrable_bounded_height_multiplier {a b η : ℝ} (hab : a ≤ b)
    {w E : ℝ → ℝ} (hw : IntervalIntegrable w volume a b) (hE : Measurable E)
    (hbound : ∀ u ∈ Icc a b, |E u| ≤ η) :
    IntervalIntegrable (fun u => w u*E u) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at hw ⊢
  have hi : IntegrableOn (fun u => E u*w u) (Ioc a b) := by
    apply hw.bdd_mul (c:=η) hE.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    simpa only [Real.norm_eq_abs] using hbound u ⟨hu.1.le,hu.2⟩
  simpa only [mul_comm] using hi

private theorem abs_weighted_height_integral {a b η : ℝ} (hab : a ≤ b)
    {w E : ℝ → ℝ} (hw : IntervalIntegrable w volume a b) (hE : Measurable E)
    (hbound : ∀ u ∈ Icc a b, |E u| ≤ η) :
    |∫ u in a..b, w u*E u| ≤ η*(∫ u in a..b, |w u|) := by
  rw [← intervalIntegral.integral_const_mul]
  apply (intervalIntegral.abs_integral_le_integral_abs hab).trans
  apply intervalIntegral.integral_mono_on hab (intervalIntegrable_bounded_height_multiplier hab hw hE hbound).abs
    (hw.abs.const_mul _)
  intro u hu
  rw [abs_mul,mul_comm η]
  exact mul_le_mul_of_nonneg_left (hbound u hu) (abs_nonneg _)

/-- Integrating a backward clipped difference transfers the shift to the
density. The uniform error is multiplied by its L¹ translation increment
and the mass of the upper boundary strip. -/
theorem backward_clipped_error_translation_le {c η : ℝ} (hc : c ∈ Icc (0:ℝ) 1)
    {w E : ℝ → ℝ} (hw : IntervalIntegrable w volume 0 1) (hE : Measurable E) (hz : E 0 = 0)
    (hb : ∀ u ∈ Icc (0:ℝ) 1, |E u| ≤ η) :
    |∫ u in (0:ℝ)..1, w u*(E u-E (max 0 (u-c)))| ≤ η*
      ((∫ u in (0:ℝ)..(1-c), |w u-w (u+c)|)+(∫ u in (1-c)..1, |w u|)) := by
  let v := 1-c
  let d := fun u : ℝ => max 0 (u-c)
  have hv₀ : 0 ≤ v := sub_nonneg.mpr hc.2
  have hv₁ : v ≤ 1 := sub_le_self _ hc.1
  have hwsub (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : IntervalIntegrable w volume a b := by
    apply hw.mono_set
    rw [uIcc_of_le hab,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc ha hb
  have hEsub (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb₁ : b ≤ 1) :
      IntervalIntegrable (fun u => w u*E u) volume a b :=
    intervalIntegrable_bounded_height_multiplier hab (hwsub a b ha hab hb₁) hE
      (fun u hu => hb u ⟨ha.trans hu.1,hu.2.trans hb₁⟩)
  have hd : Continuous d := continuous_const.max (continuous_id.sub continuous_const)
  have hdmem {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) : d u ∈ Icc (0:ℝ) 1 :=
    ⟨le_max_left _ _,max_le zero_le_one ((sub_le_self _ hc.1).trans hu.2)⟩
  have hDi := intervalIntegrable_bounded_height_multiplier zero_le_one hw (hE.comp hd.measurable)
    (fun u hu => hb (d u) (hdmem hu))
  change IntervalIntegrable (fun u => w u * E (d u)) volume 0 1 at hDi
  have hleft : (∫ u in (0:ℝ)..c, w u*E (d u)) = 0 := by
    have he : (∫ u in (0:ℝ)..c, w u*E (d u)) = ∫ _ in (0:ℝ)..c, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hc.1] at hu
      change w u*E (max 0 (u-c))=0
      rw [max_eq_left (sub_nonpos.mpr hu.2),hz,mul_zero]
    simpa using he
  have hright : (∫ u in c..1, w u*E (d u)) = ∫ u in (0:ℝ)..v, w (u+c)*E u := by
    have he : (∫ u in c..1, w u*E (d u)) = ∫ u in c..1, w u*E (u-c) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hc.2] at hu
      change w u*E (max 0 (u-c))=_
      rw [max_eq_right (sub_nonneg.mpr hu.1)]
    rw [he]
    have h := intervalIntegral.integral_comp_add_right (a:=(0:ℝ)) (b:=v)
      (fun u => w u*E (u-c)) c
    simpa only [zero_add,add_sub_cancel_right,v,sub_add_cancel] using h.symm
  have hDi₁ := hDi.mono_set (show uIcc 0 c ⊆ uIcc (0:ℝ) 1 by
    rw [uIcc_of_le hc.1,uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl hc.2)
  have hDi₂ := hDi.mono_set (show uIcc c 1 ⊆ uIcc (0:ℝ) 1 by
    rw [uIcc_of_le hc.2,uIcc_of_le zero_le_one]; exact Icc_subset_Icc hc.1 le_rfl)
  have hshift : (∫ u in (0:ℝ)..1, w u*E (d u)) = ∫ u in (0:ℝ)..v, w (u+c)*E u := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hDi₁ hDi₂,hleft,hright,zero_add]
  have hws : IntervalIntegrable (fun u : ℝ => w (u+c)) volume 0 v := by
    simpa only [sub_self,v] using (hwsub c 1 hc.1 hc.2 le_rfl).comp_add_right c
  have hwi := hwsub 0 v le_rfl hv₀ hv₁
  have hes := intervalIntegrable_bounded_height_multiplier hv₀ hws hE
    (fun u hu => hb u ⟨hu.1,hu.2.trans hv₁⟩)
  have H : (∫ u in (0:ℝ)..1, w u*(E u-E (d u))) =
      (∫ u in (0:ℝ)..v, (w u-w (u+c))*E u)+(∫ u in v..1, w u*E u) := by
    simp only [mul_sub,sub_mul]
    rw [intervalIntegral.integral_sub (hEsub 0 1 le_rfl zero_le_one le_rfl) hDi,
      ←intervalIntegral.integral_add_adjacent_intervals (hEsub 0 v le_rfl hv₀ hv₁) (hEsub v 1 hv₀ hv₁ le_rfl),
      hshift,intervalIntegral.integral_sub (hEsub 0 v le_rfl hv₀ hv₁) hes]
    ring
  change |∫ u in (0:ℝ)..1, w u*(E u-E (d u))| ≤ _
  rw [H]
  apply (abs_add_le _ _).trans
  have hf := abs_weighted_height_integral hv₀ (hwi.sub hws) hE
    (fun u hu => hb u ⟨hu.1,hu.2.trans hv₁⟩)
  have ht := abs_weighted_height_integral hv₁ (hwsub v 1 hv₀ hv₁ le_rfl) hE
    (fun u hu => hb u ⟨hv₀.trans hu.1,hu.2⟩)
  exact (add_le_add hf ht).trans_eq (by dsimp only [v]; ring)

end RiemannResearch.Analysis.MontgomeryPositiveGap

namespace RiemannResearch.Analysis.MontgomeryPositiveGap

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.backward_clipped_error_translation_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms backward_clipped_error_translation_le

end RiemannResearch.Analysis.MontgomeryPositiveGap
