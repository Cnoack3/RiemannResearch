/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.ActualZeroDiscrepancy
import RiemannResearch.Analysis.ActualZeroWindowVariance
import RiemannResearch.RH.WeilExplicitFormula.RvM.NcountWindow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
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
open scoped BigOperators Topology

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

/-- Signed normalized loss at the upper height cutoff for a window of unfolded
width `R` and center `lam`. -/
def normalizedWindowClipError (T R lam : ℝ) : ℝ :=
  ((∫ t : ℝ, actualCenteredCount T (R / (Real.log T / (2 * Real.pi))) lam t ^ 2) -
    (∫ t in (0 : ℝ)..T, ((Ncount t (t + R / (Real.log T / (2 * Real.pi))) : ℝ) -
      lam) ^ 2)) / T

/-- The height-cutoff clipping rate retains a factor of the unfolded width,
uniformly down to arbitrarily small widths and for bounded centers. -/
theorem eventually_normalizedWindowClipError_le_width_mul {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ R lam : ℝ, 0 ≤ R → R ≤ B → |lam| ≤ B →
      |normalizedWindowClipError T R lam| ≤ R * (C * (Real.log T / T)) := by
  obtain ⟨A, hA, hclip⟩ := exists_actualCenteredMoment_clip_error_le
  let K := 2 * A + B
  refine ⟨K ^ 2 * (2 * Real.pi), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (2 * Real.pi * B))] with T hT hL
  intro R lam hR hRB hlam
  have hTp : 0 < T := by linarith
  have hL1 : 1 ≤ Real.log T := (le_max_left _ _).trans hL
  have hLp : 0 < Real.log T := by linarith
  have hscale : 0 < Real.log T / (2 * Real.pi) := div_pos hLp (by positivity)
  let h := R / (Real.log T / (2 * Real.pi))
  have hh : 0 ≤ h := div_nonneg hR hscale.le
  have hh1 : h ≤ 1 := by
    apply (div_le_iff₀ hscale).2
    rw [one_mul]
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    calc
      R * (2 * Real.pi) ≤ B * (2 * Real.pi) := mul_le_mul_of_nonneg_right hRB (by positivity)
      _ ≤ Real.log T := by simpa only [mul_comm B] using (le_max_right 1 (2 * Real.pi * B)).trans hL
  have hshift : Real.log (T + 3) ≤ 2 * Real.log T := by
    calc
      Real.log (T + 3) ≤ Real.log (T * T) :=
        Real.log_le_log (by linarith) (by nlinarith [mul_self_nonneg (T - 3)])
      _ = 2 * Real.log T := by rw [Real.log_mul hTp.ne' hTp.ne']; ring
  have hsum : A * Real.log (T + 3) + |lam| ≤ K * Real.log T := by
    have h1 := mul_le_mul_of_nonneg_left hshift (by linarith : 0 ≤ A)
    have h2 := mul_le_mul_of_nonneg_left hL1 hB
    dsimp [K]
    nlinarith only [h1, h2, hlam]
  have hspos : 0 ≤ A * Real.log (T + 3) + |lam| :=
    add_nonneg (mul_nonneg (by linarith) (Real.log_nonneg (by linarith))) (abs_nonneg _)
  have hw : h = (2 * Real.pi * R) / Real.log T := by
    dsimp [h]
    rw [div_div_eq_mul_div, mul_comm R]
  unfold normalizedWindowClipError
  rw [abs_div, abs_of_pos hTp]
  apply (div_le_iff₀ hTp).2
  calc
    _ ≤ (A * Real.log (T + 3) + |lam|) ^ 2 * h := hclip T h lam hh hh1 (by linarith)
    _ ≤ (K * Real.log T) ^ 2 * ((2 * Real.pi * R) / Real.log T) :=
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hspos hsum 2) hh).trans_eq (by rw [hw])
    _ = R * (K ^ 2 * (2 * Real.pi) * (Real.log T / T)) * T := by
      field_simp [hLp.ne', hTp.ne']
      <;> ring

/-- Uniform microscopic clipping rate on bounded sets of widths and centers.
The finite-height estimate already includes the square of the local count. -/
theorem eventually_normalizedWindowClipError_le {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ R lam : ℝ, 0 ≤ R → R ≤ B → |lam| ≤ B →
      |normalizedWindowClipError T R lam| ≤ C * (Real.log T / T) := by
  obtain ⟨C, hC, he⟩ := eventually_normalizedWindowClipError_le_width_mul hB
  refine ⟨B * C, mul_nonneg hB hC, ?_⟩
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with T hT ht R lam hR hRB hlam
  have hn : 0 ≤ C * (Real.log T / T) :=
    mul_nonneg hC (div_nonneg (Real.log_pos ht).le (zero_lt_one.trans ht).le)
  exact (hT R lam hR hRB hlam).trans
    ((mul_le_mul_of_nonneg_right hRB hn).trans_eq (by ring))

/-- At fixed unfolded width, centering at the limiting mean gives a
vanishing normalized clipped-to-full second-moment error. -/
theorem normalizedWindowClipError_tendsto {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun T : ℝ => normalizedWindowClipError T R R) atTop (𝓝 0) := by
  obtain ⟨C, _, he⟩ := eventually_normalizedWindowClipError_le hR
  have hlog : Tendsto (fun T : ℝ => Real.log T / T) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  apply squeeze_zero_norm' _ (by simpa using hlog.const_mul C)
  filter_upwards [he] with T hT
  simpa [Real.norm_eq_abs] using hT R R hR le_rfl (le_of_eq (abs_of_nonneg hR))

/-- The signed clipping contribution vanishes after integration over any
bounded interval of nonnegative unfolded widths. -/
theorem integral_normalizedWindowClipError_tendsto {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Tendsto (fun T : ℝ => ∫ r in a..b, normalizedWindowClipError T r r) atTop (𝓝 0) := by
  obtain ⟨C, _, he⟩ := eventually_normalizedWindowClipError_le (ha.trans hab)
  have hlog : Tendsto (fun T : ℝ => Real.log T / T) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  apply squeeze_zero_norm' _ (by simpa using (hlog.const_mul C).mul_const |b - a|)
  filter_upwards [he] with T hT
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro r hr
  rw [uIoc_of_le hab] at hr
  have hr0 := ha.trans hr.1.le
  simpa only [Real.norm_eq_abs] using hT r r hr0 hr.2 (by simpa only [abs_of_nonneg hr0] using hr.2)

end RiemannResearch.Analysis.ActualZeroWindowVariance
