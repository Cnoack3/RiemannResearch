/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryFormFactor
import RiemannResearch.Analysis.MontgomeryIntervalIdentity
import RiemannResearch.Analysis.MontgomeryCauchyGram
import RiemannResearch.Analysis.OrdinateTriangularIntegral
import RiemannResearch.Analysis.OrdinateCollisionCertificate
import RiemannResearch.Analysis.ActualZeroCollisionDensity
import RiemannResearch.Analysis.ActualZeroCollisionMultiplicity
import RiemannResearch.Analysis.ActualZeroCountNormalization
import RiemannResearch.Analysis.ActualZeroOrdinate
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fejér averages of the raw Montgomery form factor and critical-line density

Montgomery's Fourier prediction for all ordinate pairs has the limiting
measure δ₀ + min(|α|,1) dα. We formulate it as a test-function hypothesis
on the actual raw form factor. Testing a triangle of radius R ≥ 1 gives
the exact model value 1 + 1/(3R²). The physical-space kernel is nonnegative
and equals one on every equal-ordinate pair, including reflected zeros.
This gives the ES1 limit using only a one-sided family of triangular tests.

Sources for the form-factor convention and test kernels: Montgomery (1973),
https://websites.umich.edu/~hlm/paircor1.pdf, and BGSTB, §4,
https://arxiv.org/abs/2501.14545. For the distinct positive-gap formulation
and its implication for critical zeros see Goldston--Lee--Schettler--Suriajaya,
https://doi.org/10.1112/mtk.70127. Their positive-gap assumption excludes
equal ordinates. No equivalence with that assumption is used here.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.MontgomeryFormFactor
open ActualZeroOrdinate ActualZeroCollisionCertificate OrdinateCollisionCertificate
open MontgomeryPoisson

/-- Compactly supported continuous tests of the full Fourier prediction.
The value at zero accounts for the spike in normalized frequency. -/
def RawFormFactorTestLimit : Prop :=
  ∀ R : ℝ, 0 < R → ∀ f : ℝ → ℝ, Continuous f → f (-R) = 0 → f R = 0 →
    Tendsto (fun T : ℝ => ∫ α in (-R)..R, f α * formFactor T α) atTop
      (𝓝 (f 0 + ∫ α in (-R)..R, f α * min |α| 1))

def fejerFormFactor (T R : ℝ) : ℝ :=
  (1 / R) * ∫ α in (-R)..R, (1 - |α| / R) * formFactor T α

private theorem fejer_pair_integral {ι : Type*} [Fintype ι] (t : ι → ℝ)
    (L : ℝ) {R : ℝ} (hR : 0 < R) :
    (1 / R) * (∫ α in (-R)..R, (1 - |α| / R) * (pairSum t (α * L)).re) =
      kernelEnergy t (fun d => cauchyWeight d * sincSquared R (L * d)) := by
  classical
  let g := fun (i j : ι) (α : ℝ) =>
    cauchyWeight (t i - t j) * ((1 - |α| / R) * Real.cos ((L * (t i - t j)) * α))
  have hg (i j : ι) : Continuous (g i j) := by dsimp [g]; fun_prop
  have expand (α : ℝ) : (1 - |α| / R) * (pairSum t (α * L)).re = ∑ i, ∑ j, g i j α := by
    rw [pairSum_re_cos]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [g]
    rw [show α * L * (t i - t j) = (L * (t i - t j)) * α by ring]
    ring
  simp_rw [expand]
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    (continuous_finsetSum _ (fun j _ => hg i j)).intervalIntegrable (-R) R)]
  simp only [Finset.mul_sum, kernelEnergy]
  apply Finset.sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_finsetSum (fun j _ => (hg i j).intervalIntegrable (-R) R),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [g]
  rw [intervalIntegral.integral_const_mul, mul_left_comm, triangular_cos_transform hR]

/-- Exact physical-space identity, with every weighted ordered pair included. -/
theorem fejerFormFactor_eq_kernelEnergy (T : ℝ) {R : ℝ} (hR : 0 < R) :
    fejerFormFactor T R =
      kernelEnergy (copyOrdinate T) (fun d => cauchyWeight d * sincSquared R (Real.log T * d)) /
        (T * Real.log T / (2 * Real.pi)) := by
  unfold fejerFormFactor formFactor
  simp_rw [← mul_div_assoc]
  rw [intervalIntegral.integral_div, ← mul_div_assoc, fejer_pair_integral _ _ hR]

/-- The triangular raw statistic majorizes the entire equal-ordinate atom. -/
theorem collision_div_main_le_fejerFormFactor {T R : ℝ} (hT : 1 < T) (hR : 0 < R) :
    (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)) ≤ fejerFormFactor T R := by
  rw [fejerFormFactor_eq_kernelEnergy T hR]
  apply div_le_div_of_nonneg_right _ (div_nonneg (mul_nonneg
    (zero_le_one.trans hT.le) (Real.log_nonneg hT.le)) (by positivity))
  apply collision_le_kernelEnergy
  · intro d
    exact mul_nonneg (by unfold cauchyWeight; positivity) (sincSquared_nonneg _ _)
  · simp [cauchyWeight, sincSquared]

/-- Exact limiting tent integral of the spike, the ramp and the plateau. -/
theorem fejer_model_value {R : ℝ} (hR : 1 ≤ R) :
    (1 / R) * (1 + ∫ α in (-R)..R, (1 - |α| / R) * min |α| 1) =
      1 + 1 / (3 * R ^ 2) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  let f := fun α : ℝ => (1 - |α| / R) * min |α| 1
  have hc : Continuous f := by dsimp [f]; fun_prop
  have heven (α : ℝ) : f (-α) = f α := by simp [f]
  have hn : (∫ α in (-R)..0, f α) = ∫ α in (0 : ℝ)..R, f α := by
    simpa only [heven, neg_zero] using
      (intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := R)).symm
  have hsmall : (∫ α in (0 : ℝ)..1, f α) = 1 / 2 - 1 / (3 * R) := by
    have hrewrite : (∫ α in (0 : ℝ)..1, f α) =
        ∫ α in (0 : ℝ)..1, (1 - α / R) * α := by
      apply intervalIntegral.integral_congr
      intro α hα
      rw [uIcc_of_le zero_le_one] at hα
      simp [f, abs_of_nonneg hα.1, min_eq_left hα.2]
    rw [hrewrite]
    let p := fun x : ℝ => x ^ 2 / 2 - x ^ 3 / (3 * R)
    have hp (x : ℝ) : HasDerivAt p ((1 - x / R) * x) x := by
      have h := (((hasDerivAt_id x).pow 2).div_const 2).sub
        (((hasDerivAt_id x).pow 3).div_const (3 * R))
      convert h using 1 <;> first | rfl | (simp only [id_eq]; field_simp [hR0.ne']; ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hp x)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp [p]
  have hlarge : (∫ α in (1 : ℝ)..R, f α) = (R - R ^ 2 / (2 * R)) - (1 - 1 / (2 * R)) := by
    have hrewrite : (∫ α in (1 : ℝ)..R, f α) = ∫ α in (1 : ℝ)..R, (1 - α / R) := by
      apply intervalIntegral.integral_congr
      intro α hα
      rw [uIcc_of_le hR] at hα
      simp [f, abs_of_nonneg (zero_le_one.trans hα.1), min_eq_right hα.1]
    rw [hrewrite]
    let p := fun x : ℝ => x - x ^ 2 / (2 * R)
    have hp (x : ℝ) : HasDerivAt p (1 - x / R) x := by
      have h := (hasDerivAt_id x).sub (((hasDerivAt_id x).pow 2).div_const (2 * R))
      convert h using 1 <;> first | rfl | (simp only [id_eq]; field_simp [hR0.ne']; ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hp x)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp [p]
  change (1 / R) * (1 + ∫ α in (-R)..R, f α) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-R) 0)
    (hc.intervalIntegrable 0 R), hn, ← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 1) (hc.intervalIntegrable 1 R), hsmall, hlarge]
  field_simp [hR0.ne']
  ring

theorem fejer_limit_of_rawFormFactorTestLimit (h : RawFormFactorTestLimit) {R : ℝ} (hR : 1 ≤ R) :
    Tendsto (fun T : ℝ => fejerFormFactor T R) atTop (𝓝 (1 + 1 / (3 * R ^ 2))) := by
  have hR0 := zero_lt_one.trans_le hR
  let f := fun α : ℝ => 1 - |α| / R
  have he := h R hR0 f (by dsimp [f]; fun_prop)
    (by simp [f, abs_of_pos hR0, hR0.ne']) (by simp [f, abs_of_pos hR0, hR0.ne'])
  have hlim := he.const_mul (1 / R)
  simpa only [f, abs_zero, zero_div, sub_zero, fejerFormFactor, fejer_model_value hR] using hlim

/-- One fixed triangular limit M already gives every eventual joint
simple-and-critical proportion strictly below 2 - M. -/
theorem simpleCritical_proportion_of_fejer_limit {R M p : ℝ} (hR : 0 < R)
    (h : Tendsto (fun T : ℝ => fejerFormFactor T R) atTop (𝓝 M)) (hp : p < 2 - M) :
    ∀ᶠ T : ℝ in atTop, p < (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ) := by
  let D := fun T : ℝ => T * Real.log T / (2 * Real.pi)
  have hn := tendsto_count_div_mainTerm
  have hlim : Tendsto (fun T : ℝ =>
      (2 * ((Ncount 0 T : ℝ) / D T) - fejerFormFactor T R) / ((Ncount 0 T : ℝ) / D T))
      atTop (𝓝 (2 - M)) := by
    have hh := ((hn.const_mul 2).sub h).div hn (by norm_num : (1 : ℝ) ≠ 0)
    rw [mul_one, div_one] at hh
    exact hh.congr' (Eventually.of_forall (fun T => by rfl))
  filter_upwards [hlim.eventually (lt_mem_nhds hp), hn.eventually (lt_mem_nhds zero_lt_one),
    eventually_gt_atTop (1 : ℝ)] with T hlow hcount hT
  have hD : 0 < D T := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hfinite : 2 * (Ncount 0 T : ℝ) ≤ (simpleCriticalCount T : ℝ) + actualCollision T := by
    exact_mod_cast twice_count_le_simpleCriticalCount_add_collision T
  have hbound : 2 * ((Ncount 0 T : ℝ) / D T) - fejerFormFactor T R ≤ (simpleCriticalCount T : ℝ) / D T := by
    calc
      _ ≤ 2 * ((Ncount 0 T : ℝ) / D T) - (actualCollision T : ℝ) / D T :=
        sub_le_sub_left (collision_div_main_le_fejerFormFactor hT hR) _
      _ = (2 * (Ncount 0 T : ℝ) - actualCollision T) / D T := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hfinite]) hD.le
  apply hlow.trans_le
  calc
    _ ≤ ((simpleCriticalCount T : ℝ) / D T) / ((Ncount 0 T : ℝ) / D T) :=
      div_le_div_of_nonneg_right hbound hcount.le
    _ = _ := by field_simp [hD.ne']

/-- A one-sided family of raw triangular tests suffices for the collision asymptotic. -/
theorem collision_limit_of_fejer_upper
    (h : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ᶠ T : ℝ in atTop, fejerFormFactor T R < 1 + ε) :
    Tendsto (fun T : ℝ => (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)))
      atTop (𝓝 1) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [tendsto_count_div_mainTerm.eventually (lt_mem_nhds ha),
      eventually_gt_atTop (1 : ℝ)] with T hN hT
    apply hN.trans_le
    have hc := actualCollision_eq_count_add_excess T
    have hle : Ncount 0 T ≤ actualCollision T := by omega
    exact div_le_div_of_nonneg_right (by exact_mod_cast hle)
      (div_nonneg (mul_nonneg (zero_le_one.trans hT.le) (Real.log_nonneg hT.le)) (by positivity))
  · intro b hb
    obtain ⟨R, hR, hlim⟩ := h (b - 1) (sub_pos.mpr hb)
    filter_upwards [hlim, eventually_gt_atTop (1 : ℝ)] with T ht hT
    exact (collision_div_main_le_fejerFormFactor hT hR).trans_lt (by linarith)

/-- The full Fourier prediction for raw ordinates implies ES1 without RH. -/
theorem collision_limit_of_rawFormFactorTestLimit (h : RawFormFactorTestLimit) :
    Tendsto (fun T : ℝ => (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)))
      atTop (𝓝 1) := by
  apply collision_limit_of_fejer_upper
  intro ε hε
  let R := max 1 (2 / ε)
  have hR : 1 ≤ R := le_max_left _ _
  have hR0 := zero_lt_one.trans_le hR
  have htwo : 2 ≤ R * ε := (div_le_iff₀ hε).mp (le_max_right _ _)
  have hRle : R ≤ 3 * R ^ 2 := by nlinarith [mul_nonneg hR0.le (sub_nonneg.mpr hR)]
  have herr : 1 / (3 * R ^ 2) < ε := (div_lt_iff₀ (by positivity)).mpr (calc
    1 < ε * R := by linarith only [htwo, mul_comm R ε]
    _ ≤ ε * (3 * R ^ 2) := mul_le_mul_of_nonneg_left hRle hε.le)
  exact ⟨R, hR0, (fejer_limit_of_rawFormFactorTestLimit h hR).eventually
    (gt_mem_nhds (by linarith only [herr]))⟩

/-- Density one of actual zeros are simultaneously simple and critical, and
density one lie on the critical line, under the full raw Fourier law. -/
theorem density_one_of_rawFormFactorTestLimit (h : RawFormFactorTestLimit) :
    Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun T : ℝ => (criticalLineCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) :=
  density_one_of_collision_limit (collision_limit_of_rawFormFactorTestLimit h)

end RiemannResearch.Analysis.MontgomeryFormFactor
