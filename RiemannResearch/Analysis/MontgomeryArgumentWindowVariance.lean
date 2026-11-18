/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroWindowDiscrepancy
import RiemannResearch.Analysis.ActualZeroWindowCrossTerm
import RiemannResearch.Analysis.MicroscopicGammaDrift
import RiemannResearch.Analysis.MontgomeryDyadicWidthCriterion
import RiemannResearch.Analysis.MontgomeryWindowVarianceCriterion
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Signed width tests for the actual zero-argument increment

With the exact gamma drift retained, the full count square is an argument
increment square plus a signed cross term and a squared drift. Controlling
the latter two yields a sufficient half-width contrast criterion involving
only the square of the actual discrepancy increment. The convergence of
those contrasts remains open. Compare GLSS, Proposition 2,
https://doi.org/10.1112/mtk.70127.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroCollisionCertificate ActualZeroOrdinate ActualZeroWindowVariance
open ActualZeroDiscrepancy OrdinateWindowVariance

/-- The full increment of the actual discrepancy, with its exact gamma drift,
centered at unfolded width and integrated over start heights. -/
def fullArgumentWidthMoment (T R : ℝ) : ℝ :=
  let h := R / (Real.log T / (2 * Real.pi))
  (∫ t in (0 : ℝ)..T, (discrepancy (t + h) - discrepancy t +
    (smoothCount (t + h) - smoothCount t) - R) ^ 2) / T

theorem fullArgumentWidthMoment_eq_count {T R : ℝ} (hT : 1 < T) (hR : 0 ≤ R) :
    fullArgumentWidthMoment T R =
      (∫ t in (0 : ℝ)..T, ((Ncount t (t + R / (Real.log T / (2 * Real.pi))) : ℝ) - R) ^ 2) / T := by
  dsimp only [fullArgumentWidthMoment]
  apply congrArg (fun x : ℝ => x / T)
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (show 0 ≤ T by linarith)] at ht
  have hh : 0 ≤ R / (Real.log T / (2 * Real.pi)) :=
    div_nonneg hR (div_nonneg (Real.log_pos hT).le (by positivity))
  dsimp only
  rw [discrepancy_increment ht.1 hh, smoothCount_sub]
  ring

private theorem measurable_fullArgumentWidthMoment {T : ℝ} (hT : 0 ≤ T) :
    Measurable (fullArgumentWidthMoment T) := by
  let s := Real.log T / (2 * Real.pi)
  let f := fun p : ℝ × ℝ => (discrepancy (p.2 + p.1 / s) - discrepancy p.2 +
    (smoothCount (p.2 + p.1 / s) - smoothCount p.2) - p.1) ^ 2
  have hp : Measurable (fun p : ℝ × ℝ => p.2 + p.1 / s) :=
    measurable_snd.add (measurable_fst.div_const s)
  have hf : Measurable f :=
    (((discrepancy_measurable.comp hp).sub (discrepancy_measurable.comp measurable_snd)).add
      ((smoothCount_continuous.measurable.comp hp).sub
        (smoothCount_continuous.measurable.comp measurable_snd))).sub measurable_fst |>.pow_const 2
  have hi := hf.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 T))
  change Measurable (fun R : ℝ => fullArgumentWidthMoment T R)
  simpa only [fullArgumentWidthMoment, s, f, intervalIntegral.integral_of_le hT] using
    hi.measurable.div_const T

/-- The finite identity keeps the true count normalization and the signed
cutoff error for the physical height window. -/
theorem eventually_window_sub_argument_eq {B : ℝ} (hB : 0 ≤ B) :
    ∀ᶠ T : ℝ in atTop, ∀ R ∈ Icc 0 B,
      unfoldedWindowEnergy T R - R ^ 2 - fullArgumentWidthMoment T R =
        normalizedWindowClipError T R R +
        2 * R ^ 2 * (unfoldedWindowMean T 1 - 1) := by
  obtain ⟨d, hd, hfloor⟩ := exists_ordinate_floor
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.pi * B / d)] with T hT hlog
  intro R hR
  let s := Real.log T / (2 * Real.pi)
  have hs : 0 < s := div_pos (Real.log_pos hT) (by positivity)
  have hTp : 0 < T := by linarith
  have hw : B / s ≤ d := by
    apply (div_le_iff₀ hs).2
    dsimp [s]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    nlinarith only [(div_le_iff₀ hd).1 hlog]
  have hlow : ∀ c : Copies T, R / s ≤ c.1.1.im := fun c =>
    (div_le_div_of_nonneg_right hR.2 hs.le).trans (hw.trans (hfloor T c))
  have hc := integral_centeredCount_sq (Finset.univ : Finset (Copies T))
    (fun c => c.1.1.im) T (R / s) R
  change (∫ t : ℝ, actualCenteredCount T (R / s) R t ^ 2) =
    (∫ t : ℝ, actualWindowCount T (R / s) t ^ 2) -
      (2 * R) * (∫ t : ℝ, actualWindowCount T (R / s) t) + R ^ 2 * max T 0 at hc
  rw [integral_actualWindowCount_sq T _ hlow,
    integral_actualWindowCount T _ (div_nonneg hR.1 hs.le) hlow, max_eq_left hTp.le] at hc
  rw [fullArgumentWidthMoment_eq_count hT hR.1]
  unfold normalizedWindowClipError unfoldedWindowEnergy actualPhysicalTriangleEnergy unfoldedWindowMean
  dsimp only [s] at hc
  rw [hc]
  field_simp [hTp.ne', (Real.log_pos hT).ne', Real.pi_ne_zero] <;> ring

/-- The sole analytic input is convergence of the signed error integrated
over each positive rational width interval. The gamma drift is exact. -/
def RationalArgumentWidthAverages : Prop :=
  ∀ a b : ℚ, 0 < a → a < b →
    Tendsto (fun T : ℝ => ∫ r in (a : ℝ)..(b : ℝ),
      fullArgumentWidthMoment T r - (sineWindowEnergy r - r ^ 2)) atTop (𝓝 0)

private theorem integral_triangle_sub_comparison_tendsto
    (G : ℝ → ℝ → ℝ) (hm : ∀ T : ℝ, 0 ≤ T → Measurable (G T))
    (hbound : ∀ B : ℝ, 0 ≤ B → ∃ e : ℝ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ T : ℝ in atTop, ∀ r ∈ Icc 0 B, |unfoldedWindowEnergy T r - r ^ 2 - G T r| ≤ e T)
    {a b : ℚ} (ha : 0 < a) (hab : a < b) : Tendsto (fun T : ℝ =>
      (∫ r in (a : ℝ)..(b : ℝ), unfoldedWindowEnergy T r - sineWindowEnergy r) -
      (∫ r in (a : ℝ)..(b : ℝ), G T r - (sineWindowEnergy r - r ^ 2))) atTop (𝓝 0) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab.le
  have hb : (0 : ℝ) ≤ b := ha'.le.trans hab'
  obtain ⟨c, hc, hboundT⟩ := hbound b hb
  let δ := fun T r : ℝ => unfoldedWindowEnergy T r - r ^ 2 - G T r
  have hd : ∀ᶠ T : ℝ in atTop, ∀ r ∈ uIoc (a : ℝ) (b : ℝ), |δ T r| ≤ c T := by
    filter_upwards [hboundT] with T hT
    intro r hr
    rw [uIoc_of_le hab'] at hr
    exact hT r ⟨ha'.le.trans hr.1.le, hr.2⟩
  have hdist : Tendsto (fun T : ℝ => ∫ r in (a : ℝ)..(b : ℝ), δ T r) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa using hc.mul_const |(b : ℝ) - a|)
    filter_upwards [hd] with T hT
    exact intervalIntegral.norm_integral_le_of_norm_le_const (fun r hr => by
      simpa only [Real.norm_eq_abs] using hT r hr)
  apply hdist.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ), hd] with T hT hbd
  have hme := (unfoldedWindowEnergy_mono T hT).measurable
  have hmd : Measurable (δ T) := (hme.sub (measurable_id.pow_const 2)).sub
    (hm T (by linarith))
  have hid : IntervalIntegrable (δ T) volume (a : ℝ) (b : ℝ) := by
    apply (intervalIntegrable_const (c := c T)).mono_fun' hmd.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
    simpa only [Real.norm_eq_abs] using hbd r hr
  have hit := (unfoldedWindowEnergy_mono T hT).intervalIntegrable (μ := volume) (a := (a : ℝ)) (b := (b : ℝ))
  have his := continuous_sineWindowEnergy.intervalIntegrable (μ := volume) (a : ℝ) (b : ℝ)
  have hia : IntervalIntegrable (fun r => G T r -
      (sineWindowEnergy r - r ^ 2)) volume (a : ℝ) (b : ℝ) := by
    convert (hit.sub his).sub hid using 1
    funext r
    dsimp [δ]
    ring
  rw [← intervalIntegral.integral_sub (hit.sub his) hia]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp [δ]
  ring

private theorem rationalTriangleWidthAverages_of_uniformComparison
    (G : ℝ → ℝ → ℝ) (hm : ∀ T : ℝ, 0 ≤ T → Measurable (G T))
    (hbound : ∀ B : ℝ, 0 ≤ B → ∃ e : ℝ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ T : ℝ in atTop, ∀ r ∈ Icc 0 B, |unfoldedWindowEnergy T r - r ^ 2 - G T r| ≤ e T)
    (h : ∀ a b : ℚ, 0 < a → a < b →
      Tendsto (fun T : ℝ => ∫ r in (a : ℝ)..(b : ℝ),
        G T r - (sineWindowEnergy r - r ^ 2)) atTop (𝓝 0)) : RationalTriangleWidthAverages := by
  intro a b ha hab
  have hd := integral_triangle_sub_comparison_tendsto G hm hbound ha hab
  simpa only [sub_add_cancel, add_zero] using hd.add (h a b ha hab)

private theorem exists_window_sub_argument_bound {B : ℝ} (hB : 0 ≤ B) :
    ∃ c : ℝ → ℝ, Tendsto c atTop (𝓝 0) ∧ ∀ᶠ T : ℝ in atTop, ∀ r ∈ Icc 0 B,
      |unfoldedWindowEnergy T r - r ^ 2 - fullArgumentWidthMoment T r| ≤ c T := by
  obtain ⟨C, _, hCT⟩ := eventually_normalizedWindowClipError_le hB
  let e := fun T : ℝ => C * (Real.log T / T)
  have he : Tendsto e atTop (𝓝 0) := by
    have hl : Tendsto (fun T : ℝ => Real.log T / T) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
    simpa [e] using hl.const_mul C
  have hclip' : ∀ᶠ T : ℝ in atTop, ∀ r ∈ Icc 0 B, |normalizedWindowClipError T r r| ≤ e T := by
    filter_upwards [hCT] with T hCT'
    intro r hr
    exact hCT' r r hr.1 hr.2 (by simpa only [abs_of_nonneg hr.1] using hr.2)
  refine ⟨fun T => e T + (2 * B ^ 2) * |unfoldedWindowMean T 1 - 1|, ?_, ?_⟩
  · simpa using he.add (((unfoldedWindowMean_tendsto 1).sub_const 1).abs.const_mul (2 * B ^ 2))
  filter_upwards [hclip', eventually_window_sub_argument_eq hB] with T hclipT hT
  intro r hr
  rw [hT r hr]
  refine (abs_add_le _ _).trans (add_le_add (hclipT r hr) ?_)
  rw [abs_mul, abs_of_nonneg (show 0 ≤ 2 * r ^ 2 by positivity)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.1 hr.2 2) (by norm_num)) (abs_nonneg _)

theorem rationalTriangleWidthAverages_of_argument
    (h : RationalArgumentWidthAverages) : RationalTriangleWidthAverages :=
  rationalTriangleWidthAverages_of_uniformComparison fullArgumentWidthMoment
    (fun _ => measurable_fullArgumentWidthMoment) (fun _ hB => exists_window_sub_argument_bound hB) h

/-- The mean square of the bare argument increment at microscopic width. -/
def pureArgumentWidthMoment (T R : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..T, (discrepancy (t + R / (Real.log T / (2 * Real.pi))) -
    discrepancy t) ^ 2) / T

private theorem measurable_pureArgumentWidthMoment {T : ℝ} (hT : 0 ≤ T) :
    Measurable (pureArgumentWidthMoment T) := by
  let s := Real.log T / (2 * Real.pi)
  let f := fun p : ℝ × ℝ => (discrepancy (p.2 + p.1 / s) - discrepancy p.2) ^ 2
  have hp : Measurable (fun p : ℝ × ℝ => p.2 + p.1 / s) :=
    measurable_snd.add (measurable_fst.div_const s)
  have hf : Measurable f :=
    ((discrepancy_measurable.comp hp).sub (discrepancy_measurable.comp measurable_snd)).pow_const 2
  have hi := hf.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 T))
  change Measurable (fun R : ℝ => pureArgumentWidthMoment T R)
  simpa only [pureArgumentWidthMoment, s, f, intervalIntegral.integral_of_le hT] using
    hi.measurable.div_const T

/-- Exact decomposition of the gamma contribution to the centered full moment. -/
theorem fullArgumentWidthMoment_sub_pure (T R : ℝ) :
    let h := R / (Real.log T / (2 * Real.pi))
    let x := fun t : ℝ => discrepancy (t + h) - discrepancy t
    let d := fun t : ℝ => smoothCount (t + h) - smoothCount t - R
    fullArgumentWidthMoment T R - pureArgumentWidthMoment T R =
      (2 * (∫ t in (0 : ℝ)..T, x t * d t) + (∫ t in (0 : ℝ)..T, d t ^ 2)) / T := by
  intro h x d
  have hxd : Measurable x := (discrepancy_measurable.comp (measurable_id.add_const h)).sub
    discrepancy_measurable
  have hx : IntervalIntegrable x volume 0 T := by
    apply (IntervalIntegrable.intervalIntegrable_norm_iff hxd.aestronglyMeasurable).mp
    simpa [x] using discrepancy_increment_pow_intervalIntegrable h 0 T 1
  have hx2 : IntervalIntegrable (fun t => x t ^ 2) volume 0 T := by
    simpa [x, Real.norm_eq_abs, sq_abs] using discrepancy_increment_pow_intervalIntegrable h 0 T 2
  have hd : Continuous d :=
    ((smoothCount_continuous.comp (continuous_id.add continuous_const)).sub
      smoothCount_continuous).sub continuous_const
  have hcross := hx.mul_continuousOn hd.continuousOn
  have hds : IntervalIntegrable (fun t => d t ^ 2) volume 0 T :=
    (hd.pow 2).intervalIntegrable 0 T
  have hsum : (∫ t in (0 : ℝ)..T, (x t + d t) ^ 2) =
      (∫ t in (0 : ℝ)..T, x t ^ 2) +
      2 * (∫ t in (0 : ℝ)..T, x t * d t) + (∫ t in (0 : ℝ)..T, d t ^ 2) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hx2 (hcross.const_mul 2),
      ← intervalIntegral.integral_add (hx2.add (hcross.const_mul 2)) hds]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have he : fullArgumentWidthMoment T R = (∫ t in (0 : ℝ)..T, (x t + d t) ^ 2) / T := by
    dsimp only [fullArgumentWidthMoment]
    apply congrArg (fun z : ℝ => z / T)
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [x, d, h]
    ring
  rw [he, hsum]
  change (_ + _ + _) / T - (∫ t in (0 : ℝ)..T, x t ^ 2) / T = _
  ring

/-- Signed rational-width averages of the bare actual argument increment.
The height integral uses the canonical right-continuous discrepancy. -/
def RationalPureArgumentWidthAverages : Prop :=
  ∀ a b : ℚ, 0 < a → a < b →
    Tendsto (fun T : ℝ => ∫ r in (a : ℝ)..(b : ℝ),
      pureArgumentWidthMoment T r - (sineWindowEnergy r - r ^ 2)) atTop (𝓝 0)

/-- Uniform cost of removing the exact gamma drift from the microscopic
argument moment. The signed mixed term costs O(1/T), and the square of
the drift costs O(1/log² T). -/
theorem eventually_fullArgumentWidthMoment_sub_pure_le {B : ℝ} (hB : 0 ≤ B) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ r ∈ Icc 0 B,
      |fullArgumentWidthMoment T r - pureArgumentWidthMoment T r| ≤
        2 * K / T + C / (Real.log T) ^ 2 := by
  obtain ⟨K, hK, hk⟩ := eventually_abs_integral_discrepancy_increment_mul_gammaDrift_le hB
  obtain ⟨C, hC, hc⟩ := microscopicGammaDrift_mean_sq_bound B hB
  refine ⟨K, C, hK, hC, ?_⟩
  filter_upwards [hk, hc, eventually_gt_atTop (0 : ℝ)] with T hcross hdrift hT
  intro r hr
  let h := r / (Real.log T / (2 * Real.pi))
  let x := fun t : ℝ => discrepancy (t + h) - discrepancy t
  let d := microscopicGammaDrift T r
  have hmix : |∫ t in (0 : ℝ)..T, x t * d t| ≤ K := by
    simpa only [x, d, microscopicGammaDrift, h, smoothCount_sub] using
      hcross r r hr.1 hr.2 (by simpa only [abs_of_nonneg hr.1] using hr.2)
  have hdpos : 0 ≤ ∫ t in (0 : ℝ)..T, d t ^ 2 :=
    intervalIntegral.integral_nonneg hT.le (fun _ _ => sq_nonneg _)
  rw [fullArgumentWidthMoment_sub_pure]
  change |(2 * (∫ t in (0 : ℝ)..T, x t * d t) + (∫ t in (0 : ℝ)..T, d t ^ 2)) / T| ≤ _
  rw [abs_div, abs_of_pos hT]
  calc
    _ ≤ (|2 * (∫ t in (0 : ℝ)..T, x t * d t)| + |∫ t in (0 : ℝ)..T, d t ^ 2|) / T :=
      div_le_div_of_nonneg_right (abs_add_le _ _) hT.le
    _ ≤ (2 * K) / T + (∫ t in (0 : ℝ)..T, d t ^ 2) / T := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hdpos, add_div]
      exact add_le_add (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmix (by norm_num)) hT.le) le_rfl
    _ ≤ _ := add_le_add le_rfl (hdrift r hr)

private theorem full_sub_pure_vanishes_uniformly (B : ℝ) (hB : 0 ≤ B) :
    ∃ e : ℝ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ T : ℝ in atTop, ∀ r ∈ Icc 0 B,
      |fullArgumentWidthMoment T r - pureArgumentWidthMoment T r| ≤ e T := by
  obtain ⟨K, C, _, _, he⟩ := eventually_fullArgumentWidthMoment_sub_pure_le hB
  refine ⟨fun T => 2 * K / T + C / (Real.log T) ^ 2, ?_, he⟩
  have hi : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  simpa [Function.comp_def, div_eq_mul_inv, inv_pow] using
    (hi.const_mul (2 * K)).add (((hi.comp Real.tendsto_log_atTop).pow 2).const_mul C)

/-- The signed triangle and bare argument-square width errors differ by a vanishing quantity. -/
theorem integral_triangle_sub_pureArgument_tendsto
    {a b : ℚ} (ha : 0 < a) (hab : a < b) : Tendsto (fun T : ℝ =>
      (∫ r in (a : ℝ)..(b : ℝ), unfoldedWindowEnergy T r - sineWindowEnergy r) -
      (∫ r in (a : ℝ)..(b : ℝ), pureArgumentWidthMoment T r - (sineWindowEnergy r - r ^ 2))) atTop (𝓝 0) := by
  apply integral_triangle_sub_comparison_tendsto pureArgumentWidthMoment
    (fun _ => measurable_pureArgumentWidthMoment) _ ha hab
  intro B hB
  obtain ⟨c, hc, hct⟩ := exists_window_sub_argument_bound hB
  obtain ⟨e, he, het⟩ := full_sub_pure_vanishes_uniformly B hB
  refine ⟨fun T => c T + e T, by simpa using hc.add he, ?_⟩
  filter_upwards [hct, het] with T hT hT'
  intro r hr
  calc
    _ = |(unfoldedWindowEnergy T r - r ^ 2 - fullArgumentWidthMoment T r) +
          (fullArgumentWidthMoment T r - pureArgumentWidthMoment T r)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add (hT r hr) (hT' r hr))

/-- Convergence of the signed bare argument-square moments suffices for actual ordinate PCC. -/
theorem positiveGapPCC_of_rationalPureArgumentWidthAverages
    (h : RationalPureArgumentWidthAverages) : PositiveGapPCC := by
  apply positiveGapPCC_of_rationalTriangleWidthAverages
  intro a b ha hab
  simpa only [sub_add_cancel, add_zero] using
    (integral_triangle_sub_pureArgument_tendsto ha hab).add (h a b ha hab)

/-- Integrated error in the bare argument-increment square, with the full
sine variance subtracted at each unfolded width. -/
def pureArgumentWidthErrorIntegral (T : ℝ) (a b : ℚ) : ℝ :=
  ∫ r in (a : ℝ)..(b : ℝ), pureArgumentWidthMoment T r - (sineWindowEnergy r - r ^ 2)

/-- The mean signed error on each rational interval agrees asymptotically
with that on its half-sized interval. The factor two accounts for length. -/
def RationalPureArgumentHalfWidthContrasts : Prop :=
  ∀ a b : ℚ, 0 < a → a < b → Tendsto (fun T : ℝ =>
    pureArgumentWidthErrorIntegral T a b - 2 * pureArgumentWidthErrorIntegral T (a/2) (b/2))
    atTop (𝓝 0)

/-- This single signed cancellation input for the actual argument increments
implies ordinary ordinate pair correlation. -/
theorem positiveGapPCC_of_pureArgumentHalfWidthContrasts
    (h : RationalPureArgumentHalfWidthContrasts) : PositiveGapPCC := by
  apply positiveGapPCC_of_rationalHalfWidthContrasts
  intro a b ha hab
  have hhalf : (0 : ℚ) < a / 2 := by positivity
  have hhab : a / 2 < b / 2 := div_lt_div_of_pos_right hab (by norm_num)
  let I := fun (T : ℝ) (l u : ℚ) =>
    ∫ r in (l : ℝ)..(u : ℝ), unfoldedWindowEnergy T r - sineWindowEnergy r
  have hd (l u : ℚ) (hl : 0 < l) (hlu : l < u) :
      Tendsto (fun T : ℝ => I T l u - pureArgumentWidthErrorIntegral T l u) atTop (𝓝 0) :=
    integral_triangle_sub_pureArgument_tendsto hl hlu
  have he (T : ℝ) : dyadicTriangleWidthError T a b 1 = 2 * I T (a/2) (b/2) := by
    let f := fun r : ℝ => unfoldedWindowEnergy T r - sineWindowEnergy r
    have hscale := intervalIntegral.integral_comp_mul_right (a := (a : ℝ)) (b := (b : ℝ))
      f (by norm_num : (1 / 2 : ℝ) ≠ 0)
    simpa [dyadicTriangleWidthError, I, f, Rat.cast_div, smul_eq_mul, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using hscale
  have hh := ((hd a b ha hab).sub ((hd (a/2) (b/2) hhalf hhab).const_mul 2)).add (h a b ha hab)
  simp only [mul_zero, sub_zero, zero_add] at hh
  apply hh.congr'
  filter_upwards with T
  rw [he]
  have hzero : dyadicTriangleWidthError T a b 0 = I T a b := by simp [dyadicTriangleWidthError, I]
  rw [hzero]
  ring

end RiemannResearch.Analysis.MontgomeryPositiveGap
