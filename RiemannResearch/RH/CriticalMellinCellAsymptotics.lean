import RiemannResearch.RH.CriticalMellinMixtureEnergy
import RiemannResearch.Analysis.MellinDifferenceBounds
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Exact Mellin cell slopes and their asymptotic limit

Source: user-provided critical Mellin mixture argument, 21 September 2026.
The actual first-difference factorization, derivative limit, and uniform
slope bound are proved here without RH or spectral-provider assumptions.
-/

noncomputable section
set_option autoImplicit false
open Filter Set
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.SpectralObstruction

/-- The dimensionless first difference of the actual Mellin power. -/
def cellSlope (s : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) + 1) *
    (1 - (((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) ^ (-s)))

theorem cellSlope_tendsto (s : ℂ) :
    Tendsto (cellSlope s) atTop (𝓝 s) := by
  by_cases hs : s = 0
  · subst s
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)) using 1
    ext n
    simp only [cellSlope, neg_zero, Complex.cpow_zero, sub_self, mul_zero]
  have hd : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-s)) (-s) 1 := by
    simpa using hasDerivAt_ofReal_cpow_const (show (1 : ℝ) ≠ 0 by norm_num)
      (neg_ne_zero.mpr hs)
  have heps : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop
      (nhdsWithin (0 : ℝ) {0}ᶜ) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Filter.Eventually.of_forall (fun n => by simp; positivity)
  have hh := (hd.tendsto_slope_zero.comp heps).neg
  convert hh using 1
  · ext n
    simp [cellSlope, Complex.real_smul, one_div]
    ring
  · simp

theorem cellSlope_norm_le (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    ‖cellSlope s n‖ ≤ ‖s‖ := by
  let h : ℝ := 1 / ((n : ℝ) + 1)
  have hh : 0 < h := by dsimp [h]; positivity
  have hd : ∀ x ∈ Icc 1 (1 + h),
      HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (-s))
        (-s * (x : ℂ) ^ (-s - 1)) (Icc 1 (1 + h)) x := by
    intro x hx
    exact (RiemannResearch.Analysis.Cesaro.power_hasDerivAt s hs x
      (lt_of_lt_of_le zero_lt_one hx.1)).hasDerivWithinAt
  have hb : ∀ x ∈ Ico 1 (1 + h), ‖-s * (x : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ := by
    intro x hx
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos
      (lt_of_lt_of_le zero_lt_one hx.1)]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    have hp := Real.rpow_le_rpow_of_nonpos zero_lt_one hx.1
      (show -s.re - 1 ≤ 0 by linarith)
    simpa using mul_le_mul_of_nonneg_left hp (norm_nonneg s)
  have hm := norm_image_sub_le_of_norm_deriv_le_segment' hd hb
    (1 + h) (by constructor <;> linarith)
  have hm' : ‖1 - (((1 + h : ℝ) : ℂ) ^ (-s))‖ ≤ ‖s‖ * h := by
    simpa only [Complex.ofReal_one, Complex.one_cpow, add_sub_cancel_left, norm_sub_rev] using hm
  have hmul := mul_le_mul_of_nonneg_left hm' (show 0 ≤ (n : ℝ) + 1 by positivity)
  have hcast : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    have he : (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) := by simp
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [cellSlope, norm_mul, hcast]
  change ((n : ℝ) + 1) * ‖1 - (((1 + h : ℝ) : ℂ) ^ (-s))‖ ≤ _
  apply hmul.trans_eq
  dsimp [h]
  field_simp

theorem mellinMode_eq_cellSlope (s : ℂ) (n : ℕ) :
    mellinMode s n = ((n : ℂ) + 2) * ((n : ℂ) + 1) ^ (-s) * cellSlope s n := by
  let x : ℝ := (n : ℝ) + 1
  have hx : 0 < x := by dsimp [x]; positivity
  have hprod : (x : ℂ) * ((1 + 1 / x : ℝ) : ℂ) = (n : ℂ) + 2 := by
    dsimp [x]
    push_cast
    field_simp
    <;> ring
  have hp := Complex.mul_cpow_ofReal_nonneg hx.le
    (show 0 ≤ 1 + 1 / x by positivity) (-s)
  rw [hprod] at hp
  have hxcast : (x : ℂ) = (n : ℂ) + 1 := by simp [x]
  rw [hxcast] at hp
  rw [mellinMode, hp, cellSlope]
  dsimp [x]
  ring

end RiemannResearch.RH.Pareto.SpectralObstruction
