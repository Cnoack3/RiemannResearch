/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualUniformRationalLandau
import RiemannResearch.Analysis.ActualZeroSelbergDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Actual rational FMZ modes

The centered Landau limits below are unconditional consequences of the
repository's proved actual rational contour bound. The ordinate limits use
only the explicitly named classical Selberg density proposition. No rational
Landau limit, arithmetic main term, or desired FMZ limit is an input.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate

private theorem log_pow_div_self_tendsto_zero (n : ℕ) :
    Tendsto (fun T : ℝ => (Real.log T) ^ n / T) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
    Real.tendsto_log_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  simp only [Function.comp_def, Real.exp_neg, Real.exp_log hT, div_eq_mul_inv]

private theorem shifted_log_pow_div_self_tendsto_zero (n : ℕ) :
    Tendsto (fun T : ℝ => (Real.log (T + 3)) ^ n / T) atTop (𝓝 0) := by
  have hshift : Tendsto (fun T : ℝ => T + 3) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with T hT
    linarith
  have hr : Tendsto (fun T : ℝ => (T + 3) / T) atTop (𝓝 1) := by
    have h : Tendsto (fun T : ℝ => 3 / T) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h' : Tendsto (fun T : ℝ => 1 + 3 / T) atTop (𝓝 1) := by
      simpa using h.const_add 1
    apply h'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    field_simp
  have h := ((log_pow_div_self_tendsto_zero n).comp hshift).mul hr
  have h' : Tendsto (fun T : ℝ =>
      ((Real.log (T + 3)) ^ n / (T + 3)) * ((T + 3) / T))
      atTop (𝓝 0) := by simpa only [Function.comp_def, zero_mul] using h
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have h3 : T + 3 ≠ 0 := by linarith
  field_simp

/-- The full signed rational Landau error vanishes at height normalization. -/
theorem tendsto_rational_landau_error_div {n m : ℕ}
    (hm : 1 ≤ m) (hmn : m < n) :
    Tendsto (fun T : ℝ =>
      (landauSum T (Real.log ((n : ℝ) / (m : ℝ))) +
        ((T * rationalLandauMain n m : ℝ) : ℂ)) / (T : ℂ))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_rational_landau_rpow_bound
  let A : ℝ := (n : ℝ) ^ (5 / 2 : ℝ)
  let B : ℝ := (n : ℝ) ^ (3 / 2 : ℝ)
  have h0 : Tendsto (fun T : ℝ => A / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h1 := (shifted_log_pow_div_self_tendsto_zero 1).const_mul (n : ℝ)
  have h2 := (shifted_log_pow_div_self_tendsto_zero 2).const_mul B
  have hmajor : Tendsto (fun T : ℝ =>
      C * (A + B * (Real.log (T + 3)) ^ 2 +
        (n : ℝ) * Real.log (T + 3)) / T) atTop (𝓝 0) := by
    have h := ((h0.add h2).add h1).const_mul C
    convert h using 1
    · funext T
      simp only [pow_one]
      ring
    · norm_num
  apply squeeze_zero_norm' _ hmajor
  filter_upwards [eventually_ge_atTop (9 : ℝ)] with T hT
  have hT0 : 0 < T := by linarith
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
  exact div_le_div_of_nonneg_right
    (hbound T (n : ℝ) n m hT hm hmn le_rfl) hT0.le

/-- Actual centered rational Landau main term, with no density or RH premise. -/
theorem tendsto_rational_landau_div {n m : ℕ}
    (hm : 1 ≤ m) (hmn : m < n) :
    Tendsto (fun T : ℝ =>
      landauSum T (Real.log ((n : ℝ) / (m : ℝ))) / (T : ℂ))
      atTop (𝓝 (-(rationalLandauMain n m : ℂ))) := by
  have h := (tendsto_rational_landau_error_div hm hmn).sub_const
    (rationalLandauMain n m : ℂ)
  simp only [zero_sub] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  push_cast
  field_simp [hTc]
  ring

/-- Rational ordinate FMZ mode. The sole unresolved analytic input is Selberg. -/
theorem tendsto_rational_ordinate_div_of_uniformSelberg {n m : ℕ}
    (hm : 1 ≤ m) (hmn : m < n)
    (hD : UniformSelbergDensity (1 / 4)) :
    Tendsto (fun T : ℝ =>
      ordinateSum T (Real.log ((n : ℝ) / (m : ℝ))) / (T : ℂ))
      atTop (𝓝 (-(rationalLandauMain n m : ℂ))) := by
  have h := (tendsto_ordinate_landau_error_of_uniformSelberg
    (Real.log ((n : ℝ) / (m : ℝ))) hD).add
      (tendsto_rational_landau_div hm hmn)
  simp only [zero_add] at h
  convert h using 1
  funext T
  ring

/-- Prime-power support is the actual von Mangoldt support, including rational
nonintegral modes, whose main coefficient is exactly zero. -/
theorem tendsto_rational_ordinate_div_vonMangoldt_of_uniformSelberg {n m : ℕ}
    (hm : 1 ≤ m) (hmn : m < n)
    (hD : UniformSelbergDensity (1 / 4)) :
    Tendsto (fun T : ℝ =>
      ordinateSum T (Real.log ((n : ℝ) / (m : ℝ))) / (T : ℂ))
      atTop (𝓝 (-((if m ∣ n then
        (ArithmeticFunction.vonMangoldt (n / m) : ℝ) /
          ((2 * Real.pi) * Real.sqrt ((n : ℝ) / (m : ℝ)))
        else 0 : ℝ) : ℂ))) := by
  simpa only [rationalLandauMain_eq_vonMangoldt_div_sqrt hm hmn] using
    tendsto_rational_ordinate_div_of_uniformSelberg hm hmn hD

/-- Positive and negative rational modes have the same real main term;
the diagonal is centered by the exact actual zero count. -/
def rationalFMZMain (n m : ℕ) : ℂ :=
  if m < n then -(rationalLandauMain n m : ℂ)
  else if n < m then -(rationalLandauMain m n : ℂ) else 0

def centeredRationalOrdinate (T : ℝ) (n m : ℕ) : ℂ :=
  ordinateSum T (Real.log ((n : ℝ) / (m : ℝ))) -
    if n = m then (Ncount 0 T : ℂ) else 0

theorem ordinateSum_neg (T u : ℝ) :
    ordinateSum T (-u) = star (ordinateSum T u) := by
  simp [ordinateSum, sum, ZeroOrdinate.phase_neg]

@[simp] theorem ordinateSum_zero (T : ℝ) :
    ordinateSum T 0 = (Ncount 0 T : ℂ) := by
  simp [ordinateSum, ZeroOrdinate.phase_zero]

/-- Every rational frequency, including its conjugate and constant modes.
The arithmetic limit is proved; only Selberg's density remains as an input. -/
theorem tendsto_centeredRationalOrdinate_div_of_uniformSelberg
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hD : UniformSelbergDensity (1 / 4)) :
    Tendsto (fun T : ℝ => centeredRationalOrdinate T n m / (T : ℂ))
      atTop (𝓝 (rationalFMZMain n m)) := by
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · have hne : n ≠ m := by omega
    simpa only [centeredRationalOrdinate, rationalFMZMain, if_pos hmn,
      if_neg hne, sub_zero] using
      tendsto_rational_ordinate_div_of_uniformSelberg hm hmn hD
  · subst n
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    simp [centeredRationalOrdinate, rationalFMZMain, hm0]
  · have hne : n ≠ m := by omega
    have hnot : ¬ m < n := by omega
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    have hlog : Real.log ((n : ℝ) / (m : ℝ)) =
        -Real.log ((m : ℝ) / (n : ℝ)) := by
      rw [Real.log_div hn0 hm0, Real.log_div hm0 hn0]
      ring
    have h := (tendsto_rational_ordinate_div_of_uniformSelberg hn hnm hD).star
    simpa [centeredRationalOrdinate, rationalFMZMain, hnot,
      hnm, hne, hlog, ordinateSum_neg] using h

/-- Finite rational Fourier synthesis with the complete exact centering and
the complete signed arithmetic main term. This is immediately applicable
to any finite prime-torus trigonometric polynomial after the exact prime
numerator/denominator character identity. -/
theorem tendsto_finite_rational_ordinate_synthesis_of_uniformSelberg
    {ι : Type*} (s : Finset ι) (a : ι → ℂ) (n m : ι → ℕ)
    (hn : ∀ i ∈ s, 1 ≤ n i) (hm : ∀ i ∈ s, 1 ≤ m i)
    (hD : UniformSelbergDensity (1 / 4)) :
    Tendsto (fun T : ℝ =>
      (∑ i ∈ s, a i * centeredRationalOrdinate T (n i) (m i)) / (T : ℂ))
      atTop (𝓝 (∑ i ∈ s, a i * rationalFMZMain (n i) (m i))) := by
  have h := tendsto_finsetSum s (fun i hi =>
    (tendsto_centeredRationalOrdinate_div_of_uniformSelberg
      (hn i hi) (hm i hi) hD).const_mul (a i))
  convert h using 1
  funext T
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end RiemannResearch.Analysis.ActualZeroOrdinate

#print axioms RiemannResearch.Analysis.ActualZeroOrdinate.tendsto_rational_landau_div
#print axioms RiemannResearch.Analysis.ActualZeroOrdinate.tendsto_centeredRationalOrdinate_div_of_uniformSelberg
#print axioms RiemannResearch.Analysis.ActualZeroOrdinate.tendsto_finite_rational_ordinate_synthesis_of_uniformSelberg
