import RiemannResearch.Analysis.MontgomeryMacroscopicGap

/-! # Transposition of clipped ordinate rows

Integrating a real density over the forward height interval at every actual
zero can equivalently be done by integrating the density against the backward
cumulative count. Strictness at the lower count endpoint removes every
equal-ordinate tie in the forward pair formula.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate

private theorem heightTail_intervalIntegrable {w : ℝ → ℝ}
    (hw : IntervalIntegrable w volume 0 1) (v : ℝ) :
    IntervalIntegrable ((Ici v).indicator w) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hw ⊢
  exact hw.indicator measurableSet_Ici

private theorem integral_heightTail {w : ℝ → ℝ} {v : ℝ} (hv : 0 < v) :
    (∫ u in (0:ℝ)..1, (Ici v).indicator w u) = ∫ u in (min 1 v)..1, w u := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  by_cases h : v ≤ 1
  · have hs : Ici v ∩ Ioc 0 1 = Icc v 1 := by
      ext u
      change (v ≤ u ∧ 0 < u ∧ u ≤ 1) ↔ v ≤ u ∧ u ≤ 1
      exact ⟨fun t => ⟨t.1,t.2.2⟩,fun t => ⟨t.1,hv.trans_le t.1,t.2⟩⟩
    rw [hs, min_eq_right h, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le h]
  · have hs : Ici v ∩ Ioc 0 1 = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact h (hu.1.trans hu.2.2)
    simp [hs,min_eq_left (le_of_not_ge h)]

private theorem scaledCount_indicator_eq {T u : ℝ} (hT : 1 < T) (hu : u ≤ 1) :
    scaledHeightCount T u =
      (∑ i : Copies T, if copyOrdinate T i / T ≤ u then (1 : ℝ) else 0) / unfoldedCutoff T := by
  have ht := zero_lt_one.trans hT
  rw [scaledHeightCount, cumulative_copy_steps (by simpa using mul_le_mul_of_nonneg_right hu ht.le)]
  simp only [div_le_iff₀ ht]

/-- Exact finite transposition for every interval-integrable density and
every nonnegative height width, including rows clipped at the cutoff. -/
theorem clipped_height_row_sum_eq_backward_count {T c : ℝ} (hT : 1 < T) (hc : 0 ≤ c)
    {w : ℝ → ℝ} (hw : IntervalIntegrable w volume 0 1) :
    (∑ i : Copies T, ∫ u in (copyOrdinate T i / T)..(min 1 (copyOrdinate T i / T+c)), w u) /
      unfoldedCutoff T =
      ∫ u in (0:ℝ)..1, w u * (scaledHeightCount T u-scaledHeightCount T (max 0 (u-c))) := by
  classical
  let x := fun i : Copies T => copyOrdinate T i/T
  let f := fun i : Copies T => fun u => (Ici (x i)).indicator w u -
    (Ici (x i+c)).indicator w u
  have ht := zero_lt_one.trans hT
  have hx (i : Copies T) : 0 < x i ∧ x i ≤ 1 := by
    exact ⟨div_pos (mem_cutoff.mp i.1.property).2.1 ht,
      (div_le_iff₀ ht).mpr (by rw [one_mul]; exact (mem_cutoff.mp i.1.property).2.2)⟩
  have hfi (i : Copies T) : IntervalIntegrable (f i) volume 0 1 :=
    (heightTail_intervalIntegrable hw _).sub (heightTail_intervalIntegrable hw _)
  have hf (i : Copies T) :
      (∫ u in (0:ℝ)..1, f i u) = ∫ u in (x i)..(min 1 (x i+c)), w u := by
    dsimp only [f]
    rw [intervalIntegral.integral_sub (heightTail_intervalIntegrable hw _) (heightTail_intervalIntegrable hw _),
      integral_heightTail (hx i).1, integral_heightTail (add_pos_of_pos_of_nonneg (hx i).1 hc),
      min_eq_right (hx i).2]
    have hxy : x i ≤ min 1 (x i+c) := le_min (hx i).2 (le_add_of_nonneg_right hc)
    have hpq : IntervalIntegrable w volume (x i) (min 1 (x i+c)) := by
      apply hw.mono_set
      rw [uIcc_of_le hxy,uIcc_of_le zero_le_one]
      exact Icc_subset_Icc (hx i).1.le (min_le_left _ _)
    have hqr : IntervalIntegrable w volume (min 1 (x i+c)) 1 := by
      apply hw.mono_set
      rw [uIcc_of_le (min_le_left _ _), uIcc_of_le zero_le_one]
      exact Icc_subset_Icc ((hx i).1.le.trans hxy) le_rfl
    linarith only [intervalIntegral.integral_add_adjacent_intervals hpq hqr]
  calc
    _ = (∑ i : Copies T, ∫ u in (0:ℝ)..1, f i u) / unfoldedCutoff T := by
      congr 1
      exact Finset.sum_congr rfl (fun i _ => (hf i).symm)
    _ = ∫ u in (0:ℝ)..1, (∑ i : Copies T, f i u)/unfoldedCutoff T := by
      rw [intervalIntegral.integral_div,intervalIntegral.integral_finsetSum (fun i _ => hfi i)]
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le zero_le_one] at hu
      change (∑ i : Copies T, f i u) / unfoldedCutoff T =
        w u * (scaledHeightCount T u - scaledHeightCount T (max 0 (u-c)))
      rw [scaledCount_indicator_eq hT hu.2,scaledCount_indicator_eq hT
        (max_le zero_le_one ((sub_le_self _ hc).trans hu.2)), ← sub_div, ← Finset.sum_sub_distrib]
      rw [← mul_div_assoc, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      have ha : x i ≤ max 0 (u-c) ↔ x i+c ≤ u := by
        rw [le_max_iff,or_iff_right (not_le.mpr (hx i).1),le_sub_iff_add_le]
      change (Ici (x i)).indicator w u - (Ici (x i+c)).indicator w u =
        w u * ((if x i ≤ u then 1 else 0) - if x i ≤ max 0 (u-c) then 1 else 0)
      rw [show (if x i ≤ max 0 (u-c) then (1:ℝ) else 0) =
        (if x i+c ≤ u then (1:ℝ) else 0) by simp only [ha]]
      by_cases h₁ : x i ≤ u <;> by_cases h₂ : x i+c ≤ u <;>
        simp [Set.indicator, Set.mem_Ici,h₁,h₂]

private theorem heightDensity_mul_monotone {w F : ℝ → ℝ}
    (hw : IntervalIntegrable w volume 0 1) (hF : Monotone F) :
    IntervalIntegrable (fun u => w u * F u) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hw ⊢
  have h : IntegrableOn (fun u => F u * w u) (Ioc (0:ℝ) 1) := by
    apply hw.bdd_mul (c := max |F 0| |F 1|) hF.measurable.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨(neg_le_neg (le_max_left _ _)).trans
      ((neg_abs_le (F 0)).trans (hF hu.1.le)), (hF hu.2).trans ((le_abs_self _).trans
      (le_max_right _ _))⟩
  simpa only [mul_comm] using h

/-- A continuous integral model for the height count controls the positive
pair count uniformly in the chosen fraction of the full cutoff. The bound
uses the L¹ norm of the model density and the measured number of ordinates. -/
theorem positiveGapMass_density_model_error_le {T c η : ℝ} (hT : 1 < T) (hc : 0 ≤ c)
    {w G : ℝ → ℝ} (hw : IntervalIntegrable w volume 0 1) (hGc : Continuous G)
    (hG : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, G y-G x = ∫ u in x..y, w u)
    (hclose : ∀ x ∈ Icc (0:ℝ) 1, |scaledHeightCount T x - G x| ≤ η) :
    |positiveGapMass T (c*unfoldedCutoff T)/unfoldedCutoff T -
      (∫ u in (0:ℝ)..1, w u * (G u-G (max 0 (u-c))))| ≤
      2*η*(((Ncount 0 T : ℝ)/unfoldedCutoff T)+(∫ u in (0:ℝ)..1, |w u|)) := by
  classical
  let x := fun i : Copies T => copyOrdinate T i/T
  let y := fun i : Copies T => min 1 (x i+c)
  let d := fun u : ℝ => max 0 (u-c)
  let F := scaledHeightCount T
  let A := fun u => w u*(F u-F (d u))
  let M := fun u => w u*(G u-G (d u))
  let D := unfoldedCutoff T
  have ht := zero_lt_one.trans hT
  have hD : 0 < D := div_pos (mul_pos ht (Real.log_pos hT)) (by positivity)
  have hx (i : Copies T) : x i ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg (mem_cutoff.mp i.1.property).2.1.le ht.le,
      (div_le_iff₀ ht).mpr (by rw [one_mul]; exact (mem_cutoff.mp i.1.property).2.2)⟩
  have hy (i : Copies T) : y i ∈ Icc (0:ℝ) 1 :=
    ⟨le_min zero_le_one (add_nonneg (hx i).1 hc),min_le_left _ _⟩
  have hd {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) : d u ∈ Icc (0:ℝ) 1 :=
    ⟨le_max_left _ _,max_le zero_le_one ((sub_le_self _ hc).trans hu.2)⟩
  have herr {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) :
      |(F b-F a)-(G b-G a)| ≤ 2*η := by
    have h1 := abs_le.mp (hclose a ha)
    have h2 := abs_le.mp (hclose b hb)
    dsimp only [F]
    exact abs_le.mpr ⟨by linarith only [h2.1,h1.2],by linarith only [h2.2,h1.1]⟩
  have hrow : |positiveGapMass T (c*D)/D - (∫ u in (0:ℝ)..1, A u)| ≤
      2*η*((Ncount 0 T : ℝ)/D) := by
    have hp := positiveGapMass_scaled_eq_height_rows hT hc
    change positiveGapMass T (c*D) = ∑ i : Copies T, (F (y i)-F (x i)) at hp
    have hm := clipped_height_row_sum_eq_backward_count hT hc hw
    change (∑ i : Copies T, ∫ u in (x i)..(y i), w u)/D = ∫ u in (0:ℝ)..1, A u at hm
    rw [hp,← hm,← sub_div,← Finset.sum_sub_distrib,abs_div,abs_of_pos hD]
    have hr (i : Copies T) :
        |(F (y i)-F (x i))-(∫ u in (x i)..(y i), w u)| ≤ 2*η := by
      rw [← hG _ (hx i) _ (hy i)]
      exact herr (hx i) (hy i)
    have h := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum
      (fun i (_ : i ∈ (Finset.univ : Finset (Copies T))) => hr i))
    simp only [Finset.sum_const,Finset.card_univ,card_copies,nsmul_eq_mul] at h
    exact (div_le_div_of_nonneg_right h hD.le).trans_eq (by ring)
  have hfm := scaledHeightCount_mono hT
  have hdm : Monotone d := fun _ _ hab => max_le_max_left _ (sub_le_sub_right hab c)
  have hAi : IntervalIntegrable A volume 0 1 := by
    simpa only [A,F,mul_sub,Function.comp_apply] using (heightDensity_mul_monotone hw hfm).sub
      (heightDensity_mul_monotone hw (hfm.comp hdm))
  have hMi : IntervalIntegrable M volume 0 1 :=
    hw.mul_continuousOn (hGc.sub (hGc.comp (continuous_const.max (continuous_id.sub continuous_const)))).continuousOn
  have hback : |(∫ u in (0:ℝ)..1, A u) - ∫ u in (0:ℝ)..1, M u| ≤
      2*η*(∫ u in (0:ℝ)..1, |w u|) := by
    rw [←intervalIntegral.integral_sub hAi hMi, ← intervalIntegral.integral_const_mul]
    apply (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans
    apply intervalIntegral.integral_mono_on zero_le_one (hAi.sub hMi).abs (hw.abs.const_mul _)
    intro u hu
    change |w u * (F u - F (d u))-w u*(G u-G (d u))| ≤ 2*η*|w u|
    rw [← mul_sub,abs_mul,mul_comm (2*η)]
    exact mul_le_mul_of_nonneg_left (herr (hd hu) hu) (abs_nonneg _)
  calc
    _ ≤ |positiveGapMass T (c*D)/D-(∫ u in (0:ℝ)..1, A u)| +
      |(∫ u in (0:ℝ)..1, A u)-(∫ u in (0:ℝ)..1, M u)| := abs_sub_le _ _ _
    _ ≤ _ := (add_le_add hrow hback).trans_eq (by dsimp only [D]; ring)

end RiemannResearch.Analysis.MontgomeryPositiveGap
