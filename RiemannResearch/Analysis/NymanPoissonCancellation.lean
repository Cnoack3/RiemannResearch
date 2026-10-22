import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Exact Poisson cancellation for the arithmetic return kernel

Source: equation (4.5) of the user-provided Nyman--Weil note. Poisson summation
itself is Mathlib's Schwartz-space theorem. This module proves the exact
rescaling and cancellation used by that argument. The smooth logarithmic
substitution is supplied in `LogarithmicSchwartzTransport`; the resulting
rapid-decay estimate is supplied in `NymanReturnRapidDecay`.
-/

noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap BigOperators

namespace RiemannResearch.Analysis

private def realScaleEquiv (a : ℝ) (ha : a ≠ 0) : ℝ ≃L[ℝ] ℝ where
  toFun x := a * x
  invFun x := a⁻¹ * x
  left_inv x := by simp [← mul_assoc, ha]
  right_inv x := by simp [← mul_assoc, ha]
  map_add' x y := mul_add a x y
  map_smul' c x := by simp only [smul_eq_mul, RingHom.id_apply]; ring
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

/-- Positive dilation of a Schwartz test, represented as an actual Schwartz map. -/
def schwartzScale (f : SchwartzMap ℝ ℂ) (a : ℝ) (ha : a ≠ 0) :
    SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realScaleEquiv a ha) f

@[simp] theorem schwartzScale_apply (f : SchwartzMap ℝ ℂ) (a : ℝ)
    (ha : a ≠ 0) (x : ℝ) : schwartzScale f a ha x = f (a * x) := rfl

/-- Fourier scaling with all Jacobian and frequency factors explicit. -/
theorem fourier_comp_pos_mul (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (w : ℝ) :
    𝓕 (fun x => f (a * x)) w = a⁻¹ • 𝓕 f (w / a) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  have heq : (fun v : ℝ =>
      Complex.exp ((-2 * Real.pi * v * w : ℝ) * Complex.I) • f (a * v)) =
      (fun v : ℝ =>
        (fun t : ℝ => Complex.exp ((-2 * Real.pi * t * (w / a) : ℝ) *
          Complex.I) • f t) (a * v)) := by
    funext v
    have hr : -2 * Real.pi * (a * v) * (w / a) =
        -2 * Real.pi * v * w := by field_simp
    dsimp only
    rw [hr]
  rw [heq]
  simpa only [abs_of_pos (inv_pos.mpr ha)] using
    Measure.integral_comp_mul_left
      (fun t : ℝ => Complex.exp ((-2 * Real.pi * t * (w / a) : ℝ) *
        Complex.I) • f t) a

/-- Integer samples of a Schwartz function are absolutely summable. -/
theorem summable_schwartz_int (f : SchwartzMap ℝ ℂ) :
    Summable (fun k : ℤ => f (k : ℝ)) := by
  exact summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
    ((f.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)

/-- Poisson's formula at an arbitrary positive lattice spacing. -/
theorem schwartz_poisson_pos_scale (f : SchwartzMap ℝ ℂ) {a : ℝ} (ha : 0 < a) :
    (∑' k : ℤ, f (a * k)) =
      a⁻¹ • ∑' k : ℤ, (𝓕 f) ((k : ℝ) / a) := by
  have hp := (schwartzScale f a ha.ne').tsum_eq_tsum_fourier 0
  have hcoe : (schwartzScale f a ha.ne' : ℝ → ℂ) = fun x => f (a * x) := rfl
  simpa [SchwartzMap.fourier_coe, hcoe,
    fourier_comp_pos_mul (f : ℝ → ℂ) ha, tsum_const_smul'', tsum_mul_left] using hp

/-- The exact lattice discrepancy before the logarithmic half-density factor.
The normalization `1/n` is part of the actual conductor coefficient. -/
def conductorLatticeDiscrepancy (f : SchwartzMap ℝ ℂ) (n a : ℝ) : ℂ :=
  (n⁻¹ : ℝ) • (∑' k : ℤ, f (a * k)) - ∑' k : ℤ, f ((n * a) * k)

/-- Exact Poisson representation of the conductor discrepancy; both zero
frequencies occur with the identical coefficient `1/(n*a)`. -/
theorem conductorLatticeDiscrepancy_poisson (f : SchwartzMap ℝ ℂ)
    {n a : ℝ} (hn : 0 < n) (ha : 0 < a) :
    conductorLatticeDiscrepancy f n a =
      (n * a)⁻¹ • ((∑' k : ℤ, (𝓕 f) ((k : ℝ) / a)) -
        ∑' k : ℤ, (𝓕 f) ((k : ℝ) / (n * a))) := by
  rw [conductorLatticeDiscrepancy, schwartz_poisson_pos_scale f ha,
    schwartz_poisson_pos_scale f (mul_pos hn ha), smul_smul, smul_sub]
  simp [mul_inv, mul_comm]

end RiemannResearch.Analysis

namespace RiemannResearch.Analysis

private theorem summable_schwartz_int_div (f : SchwartzMap ℝ ℂ)
    {a : ℝ} (ha : 0 < a) : Summable (fun k : ℤ => f ((k : ℝ) / a)) := by
  simpa [schwartzScale_apply, div_eq_mul_inv, mul_comm] using
    summable_schwartz_int (schwartzScale f a⁻¹ (inv_ne_zero ha.ne'))

/-- The zero frequencies cancel exactly, leaving only genuinely nonzero modes.
No estimate or sign-discarding argument is used in this cancellation. -/
theorem conductorLatticeDiscrepancy_nonzero_modes (f : SchwartzMap ℝ ℂ)
    {n a : ℝ} (hn : 0 < n) (ha : 0 < a) :
    conductorLatticeDiscrepancy f n a =
      (n * a)⁻¹ •
        ((∑' k : ℤ, if k = 0 then 0 else (𝓕 f) ((k : ℝ) / a)) -
          ∑' k : ℤ, if k = 0 then 0 else (𝓕 f) ((k : ℝ) / (n * a))) := by
  rw [conductorLatticeDiscrepancy_poisson f hn ha,
    (summable_schwartz_int_div (𝓕 f) ha).tsum_eq_add_tsum_ite 0,
    (summable_schwartz_int_div (𝓕 f) (mul_pos hn ha)).tsum_eq_add_tsum_ite 0]
  simp only [Int.cast_zero, zero_div, add_sub_add_left_eq_sub]

end RiemannResearch.Analysis

namespace RiemannResearch.Analysis

/-- Quantitative decay of the nonzero Fourier lattice. The constant is an
actual Schwartz seminorm times an absolutely convergent integer p-series.
In particular the power `A` can be chosen arbitrarily large. -/
theorem norm_nonzero_schwartz_modes_le (f : SchwartzMap ℝ ℂ)
    (A : ℕ) (hA : 1 < A) {T : ℝ} (hT : 0 < T) :
    ‖∑' k : ℤ, if k = 0 then 0 else f (T * k)‖ ≤
      (SchwartzMap.seminorm ℂ A 0 f / T ^ A) *
        ∑' k : ℤ, |(k : ℝ)| ^ (-(A : ℝ)) := by
  classical
  let C := SchwartzMap.seminorm ℂ A 0 f
  let F : ℤ → ℂ := fun k => if k = 0 then 0 else f (T * k)
  let B : ℤ → ℝ := fun k => (C / T ^ A) * |(k : ℝ)| ^ (-(A : ℝ))
  have hC : 0 ≤ C := by positivity
  have hbound : ∀ k : ℤ, ‖F k‖ ≤ B k := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp only [F, if_pos rfl, norm_zero]
      exact mul_nonneg (div_nonneg hC (pow_nonneg hT.le _))
        (Real.rpow_nonneg (abs_nonneg _) _)
    · have hkR : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
      have hprod : 0 < T * |(k : ℝ)| := mul_pos hT (abs_pos.mpr hkR)
      have hs : (T * |(k : ℝ)|) ^ A * ‖f (T * k)‖ ≤ C := by
        simpa [C, norm_mul, Real.norm_of_nonneg hT.le, Real.norm_eq_abs] using
          SchwartzMap.norm_pow_mul_le_seminorm ℂ f A (T * k)
      have hq : ‖f (T * k)‖ ≤ C / (T * |(k : ℝ)|) ^ A := by
        apply (le_div_iff₀ (pow_pos hprod A)).mpr
        simpa only [mul_comm] using hs
      simp only [F, if_neg hk]
      calc
        ‖f (T * k)‖ ≤ C / (T * |(k : ℝ)|) ^ A := hq
        _ = B k := by
          dsimp [B]
          rw [Real.rpow_neg (abs_nonneg _), Real.rpow_natCast, mul_pow]
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
  have hB : Summable B := by
    exact (Real.summable_abs_int_rpow (by exact_mod_cast hA)).mul_left _
  have hFnorm : Summable (fun k => ‖F k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hbound hB
  calc
    ‖∑' k : ℤ, F k‖ ≤ ∑' k : ℤ, ‖F k‖ := norm_tsum_le_tsum_norm hFnorm
    _ ≤ ∑' k : ℤ, B k := Summable.tsum_le_tsum hbound hFnorm hB
    _ = _ := by simp [B, C, tsum_mul_left]

end RiemannResearch.Analysis
