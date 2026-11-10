/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.CauchyWeightPerturbation
import RiemannResearch.Analysis.ActualZeroBandCount
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Removing a localized height taper from the actual-ordinate form factor

The comparison concerns weights on the finite multiset 0 < γ ≤ T. The exact
signed cross term is followed by a coefficient-sensitive Cauchy bound. The
existing unconditional local zero counts discharge the boundary-strip mass.
Widths satisfying (Δ(T)+1) log(T)^2 / T → 0 give vanishing error uniformly in
frequency; a fixed-width linear taper is instantiated without zero hypotheses.

Identifying a full-height analytic window with one of these boundary tapers
still requires an independent truncation or tail estimate.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
open Filter
namespace RiemannResearch.Analysis.MontgomeryHeightCutoff
open MontgomeryPoisson MontgomeryFormFactor MontgomeryLocalMass
open CauchyWeightPerturbation ActualZeroOrdinate ZeroOrdinate

/-- A height weight on precisely the actual zero copies with 0 < γ ≤ T.
Weights outside this finite cutoff are not represented by this definition. -/
def heightFormFactor (T : ℝ) (w : Copies T → ℂ) (α : ℝ) : ℝ :=
  (kernelQuadratic (copyOrdinate T)
    (fun i => w i * phase (α * Real.log T) (copyOrdinate T i))).re /
      (T * Real.log T / (2 * Real.pi))

def heightDefect (T : ℝ) (w : Copies T → ℂ) (α : ℝ) : ℝ :=
  heightFormFactor T (fun i => w i - 1) α

def heightCross (T : ℝ) (w : Copies T → ℂ) (α : ℝ) : ℝ :=
  (crossKernel (copyOrdinate T)
    (fun i => phase (α * Real.log T) (copyOrdinate T i))
    (fun i => (w i - 1) * phase (α * Real.log T) (copyOrdinate T i))).re /
      (T * Real.log T / (2 * Real.pi))

theorem heightFormFactor_one (T α : ℝ) :
    heightFormFactor T (fun _ => 1) α = formFactor T α := by
  simp only [heightFormFactor, one_mul, formFactor, pairSum_eq_kernel]

theorem heightFormFactor_nonneg {T : ℝ} (hT : 1 < T)
    (w : Copies T → ℂ) (α : ℝ) : 0 ≤ heightFormFactor T w α := by
  unfold heightFormFactor
  apply div_nonneg (kernelQuadratic_nonneg _ _)
  have ht : 0 < T := by linarith
  have hl : 0 < Real.log T := Real.log_pos hT
  positivity

/-- Exact signed two-term identity, before any positive majorization. -/
theorem height_sub_raw_exact (T : ℝ) (w : Copies T → ℂ) (α : ℝ) :
    heightFormFactor T w α - formFactor T α =
      2 * heightCross T w α + heightDefect T w α := by
  have h := kernel_sub_exact (copyOrdinate T)
    (fun i => w i * phase (α * Real.log T) (copyOrdinate T i))
    (fun i => phase (α * Real.log T) (copyOrdinate T i))
  have he : (fun i => w i * phase (α * Real.log T) (copyOrdinate T i)) -
      (fun i => phase (α * Real.log T) (copyOrdinate T i)) =
      (fun i => (w i - 1) * phase (α * Real.log T) (copyOrdinate T i)) := by
    ext i
    simp [sub_mul]
  rw [he] at h
  unfold heightDefect heightCross heightFormFactor formFactor
  rw [pairSum_eq_kernel, ← sub_div, h]
  ring

theorem sqrt_height_sub_raw {T : ℝ} (hT : 1 < T)
    (w : Copies T → ℂ) (α : ℝ) :
    |Real.sqrt (heightFormFactor T w α) - Real.sqrt (formFactor T α)| ≤
      Real.sqrt (heightDefect T w α) := by
  have hn : 0 < T * Real.log T / (2 * Real.pi) := by
    have ht : 0 < T := by linarith
    have hl : 0 < Real.log T := Real.log_pos hT
    positivity
  have h := sqrt_kernel_difference (copyOrdinate T)
    (fun i => w i * phase (α * Real.log T) (copyOrdinate T i))
    (fun i => phase (α * Real.log T) (copyOrdinate T i))
  have he : (fun i => w i * phase (α * Real.log T) (copyOrdinate T i)) -
      (fun i => phase (α * Real.log T) (copyOrdinate T i)) =
      (fun i => (w i - 1) * phase (α * Real.log T) (copyOrdinate T i)) := by
    ext i
    simp [sub_mul]
  rw [he] at h
  unfold heightDefect heightFormFactor formFactor
  rw [pairSum_eq_kernel]
  simp only [Real.sqrt_div (kernelQuadratic_nonneg _ _), ← sub_div, abs_div,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right h (Real.sqrt_nonneg _)

/-- The coefficient-sensitive normalized defect bound has no zero-density or RH hypothesis. -/
theorem exists_height_defect_coefficient_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 9 ≤ T → ∀ (w : Copies T → ℂ) (α : ℝ),
      heightDefect T w α ≤ C / T * ∑ i, ‖w i - 1‖^2 := by
  obtain ⟨A,hA,hgram⟩ := exists_actual_cauchy_gram_bound
  refine ⟨4 * Real.pi * A, by positivity, ?_⟩
  intro T hT w α
  have ht : 0 < T := by linarith
  have hl : 0 < Real.log T := Real.log_pos (by linarith)
  have hlog : Real.log (T+3) ≤ 2 * Real.log T := by
    calc
      _ ≤ Real.log (T*T) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_mul ht.ne' ht.ne']; ring
  have hg := hgram T ht.le
    (fun i => (w i - 1) * phase (α * Real.log T) (copyOrdinate T i))
  simp only [norm_mul, phase_norm, mul_one] at hg
  unfold heightDefect heightFormFactor
  apply (div_le_iff₀ (by positivity : 0 < T * Real.log T / (2 * Real.pi))).mpr
  calc
    _ ≤ ‖kernelQuadratic (copyOrdinate T)
        (fun i => (w i - 1) * phase (α * Real.log T) (copyOrdinate T i))‖ :=
      Complex.re_le_norm _
    _ ≤ A * Real.log (T+3) * ∑ i, ‖w i - 1‖^2 := hg
    _ ≤ A * (2 * Real.log T) * ∑ i, ‖w i - 1‖^2 := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hA.le)
        (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    _ = _ := by field_simp; ring

/-- The height taper is allowed to be arbitrary complex-valued within the top strip. -/
theorem exists_height_defect_band_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T Δ : ℝ, 9 ≤ T → 0 ≤ Δ → Δ ≤ T →
      ∀ (w : Copies T → ℂ), (∀ i, ‖w i - 1‖ ≤ 1) →
      (∀ i, copyOrdinate T i ≤ T - Δ → w i = 1) →
      ∀ α : ℝ, heightDefect T w α ≤ C * (Δ + 1) * Real.log T / T := by
  obtain ⟨A,hA,hcoeff⟩ := exists_height_defect_coefficient_bound
  obtain ⟨B,hB,hband⟩ := ActualZeroBandCount.exists_band_count_bound
  refine ⟨A*B, mul_pos hA hB, ?_⟩
  intro T Δ hT hΔ hΔT w hw hi α
  have ht : 0 < T := by linarith
  calc
    _ ≤ A / T * ∑ i, ‖w i - 1‖^2 := hcoeff T hT w α
    _ ≤ A / T * (Zeta23.Ncount (T - Δ) T : ℝ) :=
      mul_le_mul_of_nonneg_left (ActualZeroBandCount.coefficient_error_le_count T Δ w hw hi)
        (by positivity)
    _ ≤ A / T * (B * (Δ+1) * Real.log T) :=
      mul_le_mul_of_nonneg_left (hband T Δ hT hΔ hΔT) (by positivity)
    _ = _ := by ring

theorem height_sub_raw_bound {T : ℝ} (hT : 1 < T)
    (w : Copies T → ℂ) (α : ℝ) :
    |heightFormFactor T w α - formFactor T α| ≤ heightDefect T w α +
      2 * Real.sqrt (formFactor T α) * Real.sqrt (heightDefect T w α) :=
  WeightedSqrtTransfer.abs_sub_le_of_sqrt (heightFormFactor_nonneg hT w α)
    (formFactor_nonneg hT α) (heightFormFactor_nonneg hT (fun i => w i - 1) α)
    (sqrt_height_sub_raw hT w α)


/-- Uniform in every real frequency. Only the width of the modified height strip enters. -/
theorem exists_height_band_error_bound :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ T Δ : ℝ, 9 ≤ T → 0 ≤ Δ → Δ ≤ T →
      ∀ (w : Copies T → ℂ), (∀ i, ‖w i - 1‖ ≤ 1) →
      (∀ i, copyOrdinate T i ≤ T - Δ → w i = 1) → ∀ α : ℝ,
      |heightFormFactor T w α - formFactor T α| ≤
        B * (Δ+1) * Real.log T / T +
          2 * Real.sqrt (A * B * (Δ+1) * (Real.log T)^2 / T) := by
  obtain ⟨A,hA,hraw⟩ := exists_formFactor_le_log
  obtain ⟨B,hB,hdef⟩ := exists_height_defect_band_bound
  refine ⟨A,B,hA,hB,?_⟩
  intro T Δ hT hΔ hΔT w hw hi α
  have ht : 0 < T := by linarith
  have hl : 0 < Real.log T := Real.log_pos (by linarith)
  have hd0 : 0 ≤ heightDefect T w α :=
    heightFormFactor_nonneg (by linarith) _ _
  have hr0 := formFactor_nonneg (by linarith : 1 < T) α
  have hd := hdef T Δ hT hΔ hΔT w hw hi α
  have hprod : formFactor T α * heightDefect T w α ≤
      A * B * (Δ+1) * (Real.log T)^2 / T := by
    calc
      _ ≤ (A * Real.log T) * (B * (Δ+1) * Real.log T / T) :=
        mul_le_mul (hraw T α hT) hd hd0 (by positivity)
      _ = _ := by ring
  calc
    _ ≤ heightDefect T w α +
        2 * Real.sqrt (formFactor T α) * Real.sqrt (heightDefect T w α) :=
      height_sub_raw_bound (by linarith) w α
    _ = heightDefect T w α +
        2 * Real.sqrt (formFactor T α * heightDefect T w α) := by
      rw [Real.sqrt_mul hr0]
      ring
    _ ≤ _ := add_le_add hd (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hprod) (by norm_num))

/-- A boundary taper with width o(T/log²T) has vanishing raw-form-factor error,
uniformly enough to allow an arbitrary frequency α(T). This has no hypothesis
about pair correlation or the real parts of the zeros. -/
theorem height_sub_raw_tendsto_zero
    (Δ : ℝ → ℝ) (w : (T : ℝ) → Copies T → ℂ) (α : ℝ → ℝ)
    (hwidth : ∀ᶠ T in atTop, 0 ≤ Δ T ∧ Δ T ≤ T)
    (hw : ∀ᶠ T in atTop, ∀ i, ‖w T i - 1‖ ≤ 1)
    (hinner : ∀ᶠ T in atTop, ∀ i, copyOrdinate T i ≤ T - Δ T → w T i = 1)
    (hsmall : Tendsto (fun T => (Δ T+1) * (Real.log T)^2 / T) atTop (nhds 0)) :
    Tendsto (fun T => heightFormFactor T (w T) (α T) - formFactor T (α T))
      atTop (nhds 0) := by
  obtain ⟨A,B,hA,hB,hbound⟩ := exists_height_band_error_bound
  let q : ℝ → ℝ := fun T => (Δ T+1) * (Real.log T)^2 / T
  have hq : Tendsto q atTop (nhds 0) := hsmall
  have hu : Tendsto (fun T => B*q T + 2*Real.sqrt (A*B*q T)) atTop (nhds 0) := by
    have h1 := hq.const_mul B
    have h2 := (hq.const_mul (A*B)).sqrt.const_mul 2
    simpa only [mul_zero, Real.sqrt_zero, add_zero] using h1.add h2
  have hevent : ∀ᶠ T in atTop,
      |heightFormFactor T (w T) (α T) - formFactor T (α T)| ≤
        B*q T + 2*Real.sqrt (A*B*q T) := by
    filter_upwards [eventually_ge_atTop (9:ℝ), eventually_ge_atTop (Real.exp 1),
        hwidth, hw, hinner] with T hT hTe hΔ hwT hiT
    have ht : 0 < T := by linarith
    have hΔ0 : 0 ≤ Δ T := hΔ.1
    have hl : 1 ≤ Real.log T := by
      have hh := Real.log_le_log (Real.exp_pos 1) hTe
      simpa only [Real.log_exp] using hh
    have hb := hbound T (Δ T) hT hΔ.1 hΔ.2 (w T) hwT hiT (α T)
    have hfirst : B*(Δ T+1)*Real.log T/T ≤ B*q T := by
      dsimp [q]
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ ht.le
      calc
        _ ≤ B*(Δ T+1)*(Real.log T)^2 :=
          mul_le_mul_of_nonneg_left (by nlinarith : Real.log T ≤ (Real.log T)^2)
            (by positivity)
        _ = _ := by ring
    have he : A*B*(Δ T+1)*(Real.log T)^2/T = A*B*q T := by dsimp [q]; ring
    rw [he] at hb
    exact hb.trans (add_le_add hfirst le_rfl)

  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hevent, hu.eventually_lt_const hε] with T hboundT hsmallT
  simpa only [Real.dist_eq, sub_zero] using lt_of_le_of_lt hboundT hsmallT

theorem log_sq_div_height_tendsto_zero :
    Tendsto (fun T : ℝ => (Real.log T)^2 / T) atTop (nhds 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp Real.tendsto_log_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  simp only [Function.comp_apply, Real.exp_neg, Real.exp_log hT, div_eq_mul_inv]

/-- In particular every fixed boundary width is admissible. -/
theorem fixed_width_height_sub_raw_tendsto_zero
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (w : (T : ℝ) → Copies T → ℂ) (α : ℝ → ℝ)
    (hw : ∀ᶠ T in atTop, ∀ i, ‖w T i - 1‖ ≤ 1)
    (hinner : ∀ᶠ T in atTop, ∀ i, copyOrdinate T i ≤ T - Δ → w T i = 1) :
    Tendsto (fun T => heightFormFactor T (w T) (α T) - formFactor T (α T))
      atTop (nhds 0) := by
  apply height_sub_raw_tendsto_zero (fun _ => Δ) w α
  · filter_upwards [eventually_ge_atTop Δ] with T hT
    exact ⟨hΔ,hT⟩
  · exact hw
  · exact hinner
  · have h := log_sq_div_height_tendsto_zero.const_mul (Δ+1)
    simpa only [mul_zero, mul_div_assoc] using h


/-- A concrete linear taper in the final Δ units of height. -/
def linearHeightWeight (T Δ : ℝ) (i : Copies T) : ℂ :=
  ((min 1 ((T - copyOrdinate T i) / Δ) : ℝ) : ℂ)

theorem linearHeightWeight_error_le_one (T Δ : ℝ) (hΔ : 0 < Δ) (i : Copies T) :
    ‖linearHeightWeight T Δ i - 1‖ ≤ 1 := by
  have ht : copyOrdinate T i ≤ T := (mem_cutoff.mp i.1.property).2.2
  have hv : 0 ≤ min 1 ((T - copyOrdinate T i) / Δ) :=
    le_min (by norm_num) (div_nonneg (sub_nonneg.mpr ht) hΔ.le)
  have hu : min 1 ((T - copyOrdinate T i) / Δ) ≤ 1 := min_le_left _ _
  change ‖((min 1 ((T - copyOrdinate T i) / Δ) : ℝ) : ℂ) - (1 : ℂ)‖ ≤ 1
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith)]
  linarith

theorem linearHeightWeight_eq_one (T Δ : ℝ) (hΔ : 0 < Δ) (i : Copies T)
    (hi : copyOrdinate T i ≤ T - Δ) : linearHeightWeight T Δ i = 1 := by
  have hr : 1 ≤ (T - copyOrdinate T i) / Δ :=
    (le_div_iff₀ hΔ).mpr (by linarith)
  simp only [linearHeightWeight, min_eq_left hr, Complex.ofReal_one]

/-- A completely instantiated unconditional example: replacing the final fixed-width
height strip by a linear taper leaves the raw form factor asymptotically unchanged,
even along an arbitrarily varying real frequency. -/
theorem linear_height_sub_raw_tendsto_zero (Δ : ℝ) (hΔ : 0 < Δ) (α : ℝ → ℝ) :
    Tendsto (fun T => heightFormFactor T (linearHeightWeight T Δ) (α T) -
      formFactor T (α T)) atTop (nhds 0) := by
  apply fixed_width_height_sub_raw_tendsto_zero Δ hΔ.le
  · exact Filter.Eventually.of_forall (fun T i => linearHeightWeight_error_le_one T Δ hΔ i)
  · exact Filter.Eventually.of_forall (fun T i hi => linearHeightWeight_eq_one T Δ hΔ i hi)

end RiemannResearch.Analysis.MontgomeryHeightCutoff

/--
info: 'RiemannResearch.Analysis.MontgomeryHeightCutoff.linear_height_sub_raw_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.Analysis.MontgomeryHeightCutoff.linear_height_sub_raw_tendsto_zero
