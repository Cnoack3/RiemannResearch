/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.ActualZeroDiscrepancy
import RiemannResearch.Analysis.ActualZeroWindowVariance
import RiemannResearch.RH.WeilExplicitFormula.RvM.NcountWindow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Zero-count variance and the clipped argument increment

Goldston, Lee, Schettler and Suriajaya, *Pair correlation conjecture for the
zeros of the Riemann zeta-function I*, Proposition 1,
https://doi.org/10.1112/mtk.70127, is the source of the moment comparison.
Here the top boundary is retained as `min T (t + h)` and the gamma drift
is the exact smooth increment from the formalized counting formula.
-/

noncomputable section

open Filter MeasureTheory Set Zeta23
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroWindowVariance

open ActualZeroDiscrepancy ActualZeroOrdinate OrdinateWindowVariance

/-- The pulse convention gives the usual zero count at good start and end heights.
At the observation cutoff the upper bound is inclusive in either representation. -/
theorem actualWindowCount_eq_count_min {T h t : ℝ} (ht : t ∈ Ioc 0 T)
    (hg : RvM.GoodHeight t) (hgh : RvM.GoodHeight (t + h)) :
    actualWindowCount T h t = (Ncount t (min T (t + h)) : ℝ) := by
  classical
  have hfilt : (cutoff T).filter (fun ρ => t < ρ.im ∧ ρ.im ≤ min T (t + h)) =
      (zerosIn_finite t (min T (t + h))).toFinset := by
    ext ρ
    simp only [Finset.mem_filter, mem_cutoff, Set.Finite.mem_toFinset, zerosIn,
      Set.mem_ofPred_eq]
    constructor
    · exact fun e => ⟨e.1.1, e.2.1, e.2.2⟩
    · intro e
      exact ⟨⟨e.1, ht.1.trans e.2.1, e.2.2.trans (min_le_left _ _)⟩, e.2⟩
  unfold actualWindowCount windowCount
  rw [← realSum_eq_copies (f := fun ρ : ℂ => windowPulse T h ρ.im t)]
  unfold realSum Ncount
  rw [finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite t (min T (t + h))),
    Nat.cast_sum, ← hfilt, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ρ hρ
  obtain ⟨hz, _, hT⟩ := mem_cutoff.mp hρ
  have hp : t ∈ Ioc (max 0 (ρ.im - h)) (min T ρ.im) ↔
      t < ρ.im ∧ ρ.im ≤ min T (t + h) := by
    simp only [mem_Ioc, max_lt_iff, le_min_iff]
    constructor
    · rintro ⟨⟨_, hlo⟩, _, hle⟩
      exact ⟨lt_of_le_of_ne hle (hg ρ hz).symm, hT, by linarith⟩
    · rintro ⟨hlo, _, hhi⟩
      have hhi' : ρ.im < t + h := lt_of_le_of_ne hhi (hgh ρ hz)
      exact ⟨⟨ht.1, by linarith⟩, ht.2, hlo.le⟩
  simp [windowPulse, pulse, Set.indicator, hp, mul_ite]

/-- The right-continuous count differs from the pulse convention only on a null set. -/
theorem ae_actualWindowCount_eq_count_min (T h : ℝ) :
    ∀ᵐ t : ℝ, t ∈ Ioc 0 T →
      actualWindowCount T h t = (Ncount t (min T (t + h)) : ℝ) := by
  filter_upwards [ae_goodHeight, ae_goodHeight_shift h] with t hg hgh
  exact fun ht => actualWindowCount_eq_count_min ht hg hgh

/-- An exact finite-height moment identity with the upper observation cutoff retained. -/
theorem integral_actualCenteredCount_sq_eq_clippedMoment {T h lam : ℝ} (hT : 0 ≤ T) :
    (∫ t : ℝ, actualCenteredCount T h lam t ^ 2) =
      ∫ t in (0 : ℝ)..T, ((Ncount t (min T (t + h)) : ℝ) - lam) ^ 2 := by
  rw [intervalIntegral.integral_of_le hT, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [ae_actualWindowCount_eq_count_min T h] with t hcount
  change (actualWindowCount T h t - lam * pulse 0 T t) ^ 2 = _
  by_cases ht : t ∈ Ioc 0 T
  · simp [pulse, ht, hcount ht]
  · have hsupport : actualWindowCount T h t * pulse 0 T t = actualWindowCount T h t :=
      windowCount_mul_support _ _ _ _ _
    have hz : actualWindowCount T h t = 0 := by simpa [pulse, ht] using hsupport.symm
    simp [pulse, ht, hz]

/-- The split between the exact argument increment and its gamma drift holds
with the usual right-continuous convention at the clipped upper bound. -/
theorem ae_actualWindowCount_eq_clipped_discrepancy_add_drift (T h : ℝ) (hh : 0 ≤ h) :
    ∀ᵐ t : ℝ, t ∈ Ioc 0 T →
      actualWindowCount T h t = discrepancy (min T (t + h)) - discrepancy t +
        ∫ u in t..min T (t + h), mu u := by
  filter_upwards [ae_actualWindowCount_eq_count_min T h] with t hcount ht
  have hcl : t ≤ min T (t + h) := le_min ht.2 (by linarith)
  rw [hcount ht, discrepancy_sub ht.1.le hcl]
  ring

private theorem integrable_actualCenteredCount_sq (T h lam : ℝ) :
    Integrable (fun t => actualCenteredCount T h lam t ^ 2) := by
  unfold actualCenteredCount
  simp_rw [centeredCount_sq_expansion]
  exact ((windowCount_sq_integrable _ _ _ _).sub
    ((windowCount_integrable _ _ _ _).const_mul (2 * lam))).add
      ((pulse_integrable 0 T).const_mul (lam ^ 2))

private theorem clippedMoment_intervalIntegrable (T h lam : ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    IntervalIntegrable (fun t => ((Ncount t (min T (t + h)) : ℝ) - lam) ^ 2) volume a b := by
  apply (integrable_actualCenteredCount_sq T h lam).intervalIntegrable.congr_ae
  refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
  filter_upwards [ae_actualWindowCount_eq_count_min T h] with t hcount ht
  rw [uIoc_of_le hab] at ht
  have hmem : t ∈ Ioc 0 T := ⟨ha.trans_lt ht.1, ht.2.trans hb⟩
  change (actualWindowCount T h t - lam * pulse 0 T t) ^ 2 = _
  simp [pulse, hmem, hcount hmem]

private theorem fullMoment_intervalIntegrable (h lam : ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hh : 0 ≤ h) :
    IntervalIntegrable (fun t => ((Ncount t (t + h) : ℝ) - lam) ^ 2) volume a b := by
  apply (clippedMoment_intervalIntegrable (b + h) h lam ha hab (by linarith)).congr_ae
  refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
  filter_upwards with t ht
  rw [uIoc_of_le hab] at ht
  rw [min_eq_right (show t + h ≤ b + h by linarith [ht.2])]

/-- The signed clipped-to-full second-moment error is supported on the top
height interval of length `h`. -/
theorem actualCenteredMoment_clip_error_eq {T h lam : ℝ} (hh : 0 ≤ h) (hhT : h ≤ T) :
    (∫ t : ℝ, actualCenteredCount T h lam t ^ 2) -
      (∫ t in (0 : ℝ)..T, ((Ncount t (t + h) : ℝ) - lam) ^ 2) =
      ∫ t in (T - h)..T, (((Ncount t T : ℝ) - lam) ^ 2 -
        ((Ncount t (t + h) : ℝ) - lam) ^ 2) := by
  let f := fun t : ℝ => ((Ncount t (min T (t + h)) : ℝ) - lam) ^ 2
  let g := fun t : ℝ => ((Ncount t (t + h) : ℝ) - lam) ^ 2
  have hu : 0 ≤ T - h := sub_nonneg.mpr hhT
  have huT : T - h ≤ T := by linarith
  have hfl := clippedMoment_intervalIntegrable T h lam le_rfl hu huT
  have hfr := clippedMoment_intervalIntegrable T h lam hu huT le_rfl
  have hgl := fullMoment_intervalIntegrable h lam le_rfl hu hh
  have hgr := fullMoment_intervalIntegrable h lam hu huT hh
  have hl : (∫ t in (0 : ℝ)..(T - h), f t) = ∫ t in (0 : ℝ)..(T - h), g t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hu] at ht
    dsimp [f, g]
    rw [min_eq_right (show t + h ≤ T by linarith [ht.2])]
  have hr : (∫ t in (T - h)..T, f t - g t) =
      ∫ t in (T - h)..T, (((Ncount t T : ℝ) - lam) ^ 2 - g t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le huT] at ht
    dsimp [f]
    rw [min_eq_left (show T ≤ t + h by linarith [ht.1])]
  rw [integral_actualCenteredCount_sq_eq_clippedMoment (hh.trans hhT)]
  change (∫ t in (0 : ℝ)..T, f t) - (∫ t in (0 : ℝ)..T, g t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hfl hfr,
    ← intervalIntegral.integral_add_adjacent_intervals hgl hgr, ← hr,
    intervalIntegral.integral_sub hfr hgr, hl]
  ring

/-- The cutoff-tail estimate obtained from the unconditional local zero count. -/
theorem exists_actualCenteredMoment_clip_error_le :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (T h lam : ℝ), 0 ≤ h → h ≤ 1 → h ≤ T →
      |(∫ t : ℝ, actualCenteredCount T h lam t ^ 2) -
        (∫ t in (0 : ℝ)..T, ((Ncount t (t + h) : ℝ) - lam) ^ 2)| ≤
        (A * Real.log (T + 3) + |lam|) ^ 2 * h := by
  obtain ⟨A, hA, hc⟩ := local_zero_count
  refine ⟨A, hA, ?_⟩
  intro T h lam hh hh1 hhT
  rw [actualCenteredMoment_clip_error_eq hh hhT]
  have huT : T - h ≤ T := by linarith
  have he := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := T - h) (b := T) (C := (A * Real.log (T + 3) + |lam|) ^ 2)
    (f := fun t : ℝ => (((Ncount t T : ℝ) - lam) ^ 2 -
      ((Ncount t (t + h) : ℝ) - lam) ^ 2)) (by
        intro t ht
        rw [uIoc_of_le huT] at ht
        have ht0 : 0 ≤ t := (sub_nonneg.mpr hhT).trans ht.1.le
        have hcl : (Ncount t T : ℝ) ≤ (Ncount t (t + h) : ℝ) := by
          exact_mod_cast Ncount_mono (a := t) (c := t) (b := T) (d := t + h) le_rfl
            (by linarith [ht.1])
        have hfl : (Ncount t (t + h) : ℝ) ≤ A * Real.log (T + 3) := by
          calc
            _ ≤ (Ncount t (t + 1) : ℝ) := by
              exact_mod_cast Ncount_mono (a := t) (c := t) (b := t + h) (d := t + 1)
                le_rfl (by linarith)
            _ ≤ A * Real.log (t + 3) := by simpa [abs_of_nonneg ht0] using hc t
            _ ≤ A * Real.log (T + 3) := mul_le_mul_of_nonneg_left
              (Real.log_le_log (by linarith) (by linarith [ht.2])) (by positivity)
        have hs (z : ℝ) (hz : 0 ≤ z) (hzb : z ≤ A * Real.log (T + 3)) :
            (z - lam) ^ 2 ≤ (A * Real.log (T + 3) + |lam|) ^ 2 := by
          have ha : |z - lam| ≤ A * Real.log (T + 3) + |lam| := by
            calc
              _ ≤ |z| + |lam| := by simpa [sub_eq_add_neg] using abs_add_le z (-lam)
              _ ≤ _ := by rw [abs_of_nonneg hz]; exact add_le_add hzb le_rfl
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ha 2
        have hcl_sq := hs _ (Nat.cast_nonneg (Ncount t T)) (hcl.trans hfl)
        have hfl_sq := hs _ (Nat.cast_nonneg (Ncount t (t + h))) hfl
        rw [Real.norm_eq_abs]
        apply abs_le.mpr
        constructor
        · linarith only [hfl_sq, sq_nonneg ((Ncount t T : ℝ) - lam)]
        · linarith only [hcl_sq, sq_nonneg ((Ncount t (t + h) : ℝ) - lam)])
  simpa only [Real.norm_eq_abs, show T - (T - h) = h by ring, abs_of_nonneg hh] using he

end RiemannResearch.Analysis.ActualZeroWindowVariance
