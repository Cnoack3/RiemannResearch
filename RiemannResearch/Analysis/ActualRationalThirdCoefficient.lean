/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroHorizontalRemainder
import RiemannResearch.Analysis.ActualZeroHorizontalMomentRate
import RiemannResearch.Analysis.LogarithmicRemainder
import RiemannResearch.Analysis.ActualUniformRationalLandau
import RiemannResearch.Analysis.ActualRationalFMZDomination
import RiemannResearch.Analysis.ActualZeroSelbergDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Rational third phase coefficients and horizontal-energy limits

The Landau remainder is uniformly inverse-cubic-log in its rational
logarithmic-height band; this conclusion has no density assumption.
Exact horizontal reflection then identifies existence of the next phase
coefficient with convergence of the oscillatory second horizontal moment.

The actual moment has a frequency-independent bound, so compactness gives
a convergent subsequence along every divergent sequence of heights.
These are conditional research reductions: the classical Selberg provider
remains an explicit hypothesis. No full-height moment limit or RH statement
is concluded. The subsequence theorem is for a fixed rational mode; the
simultaneous measure-level extension is an ordinary proof in
HorizontalThirdCoefficient.md.

Source for Landau and density inputs and the comparison strategy:
Ford--Zaharescu, Lemmas 1--2 and equation (3.8),
https://ford126.web.illinois.edu/wwwpapers/fz.pdf.
The rate, equivalence and subsequence deductions here use the existing
project theorems and elementary compactness; no novelty claim is made.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroOrdinate


/-- The oscillatory second moment is dominated by actual horizontal energy. -/
theorem norm_evenHorizontalMoment_one_le (T u : ℝ) :
    ‖evenHorizontalMoment T u 1‖ ≤ horizontalEnergy T := by
  unfold evenHorizontalMoment
  calc
    _ ≤ realSum T (fun ρ => ‖phase u ρ.im *
        ((ρ.re - 1 / 2 : ℝ) : ℂ) ^ (2 * 1)‖) := norm_sum_le _ _
    _ = _ := by
      unfold horizontalEnergy
      congr 1
      funext ρ
      simp only [norm_mul, ZeroOrdinate.phase_norm, one_mul, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, mul_one, sq_abs]

/-- Uniform boundedness at the third-coefficient scale, independent of u. -/
theorem normalized_evenHorizontalMoment_one_le
    (T u C a : ℝ) (hT : 1 < T) (hC : 0 ≤ C) (ha : 0 < a)
    (hD : SelbergDensityBound T C a) :
    ‖(Real.log T : ℂ) * (evenHorizontalMoment T u 1 / (T : ℂ))‖ ≤
      4 * C / a ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
  calc
    _ ≤ Real.log T * (horizontalEnergy T / T) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (norm_evenHorizontalMoment_one_le T u) hT0.le) hL.le
    _ ≤ Real.log T * (4 * C / (a ^ 2 * Real.log T)) :=
      mul_le_mul_of_nonneg_left
        (horizontalEnergy_div_height_le_log_rate T C a hT hC ha hD) hL.le
    _ = _ := by field_simp

private theorem log_cube_landau_envelope_tendsto_zero :
    Tendsto (fun T : ℝ => (Real.log T) ^ 3 *
      (Real.exp (Real.log T / 2) *
        (1 + 4 * (Real.log T) ^ 2 + 2 * Real.log T) / T)) atTop (𝓝 0) := by
  have hhalf : Tendsto (fun T : ℝ => Real.log T / 2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [(tendsto_atTop.1 Real.tendsto_log_atTop) (2 * b)] with T hT
    linarith
  have h1 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp hhalf).const_mul 8
  have h2 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp hhalf).const_mul 32
  have h3 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 5).comp hhalf).const_mul 128
  have h := (h1.add h2).add h3
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  simp only [Function.comp_def]
  have he : Real.exp (Real.log T / 2) / T = Real.exp (-(Real.log T / 2)) := by
    calc
      _ = Real.exp (Real.log T / 2) / Real.exp (Real.log T) := by rw [Real.exp_log hT]
      _ = _ := by rw [← Real.exp_sub]; congr 1; ring
  calc
    _ = ((Real.log T) ^ 3 * (1 + 4 * (Real.log T) ^ 2 + 2 * Real.log T)) *
        (Real.exp (Real.log T / 2) / T) := by rw [he]; ring
    _ = _ := by ring

/-- Uniform normalized Landau error O(1/(log T)^3) throughout the logarithmic
rational-frequency band. This estimate has no Selberg or RH premise. -/
theorem eventually_rational_landau_error_le_inv_log_cube :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ,
      1 ≤ m → m < n → Real.log (n : ℝ) ≤ Real.log T / 8 →
      ‖(landauSum T (Real.log ((n : ℝ) / (m : ℝ))) +
        ((T * rationalLandauMain n m : ℝ) : ℂ)) / (T : ℂ)‖ ≤ C / (Real.log T) ^ 3 := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_rational_landau_rpow_bound
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (9 : ℝ),
    log_cube_landau_envelope_tendsto_zero.eventually_le_const (by norm_num : (0 : ℝ) < 1)]
    with T hT henv
  intro n m hm hmn hn
  have hT0 : 0 < T := by linarith
  have hLp : 0 < Real.log T := Real.log_pos (by linarith)
  have hL : 0 ≤ Real.log T := hLp.le
  have hn0 : (0 : ℝ) < n := by
    have hnpos : 0 < n := by omega
    exact_mod_cast hnpos
  let X := Real.exp (Real.log T / 8)
  have hX : 0 < X := Real.exp_pos _
  have hnX : (n : ℝ) ≤ X := by
    rw [← Real.exp_log hn0]
    exact Real.exp_le_exp.mpr hn
  have hp (r : ℝ) (hr : r ≤ 4) : X ^ r ≤ Real.exp (Real.log T / 2) := by
    rw [Real.rpow_def_of_pos hX]
    dsimp [X]
    rw [Real.log_exp]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hXhalf : X ≤ Real.exp (Real.log T / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hlog : Real.log (T + 3) ≤ 2 * Real.log T := by
    calc
      _ ≤ Real.log (T * T) := Real.log_le_log (by linarith) (by nlinarith)
      _ = _ := by rw [Real.log_mul hT0.ne' hT0.ne']; ring
  have hlog0 : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
  have hsq : (Real.log (T + 3)) ^ 2 ≤ 4 * (Real.log T) ^ 2 := by
    nlinarith
  have hterms : X ^ (5 / 2 : ℝ) + X ^ (3 / 2 : ℝ) * (Real.log (T + 3)) ^ 2 +
      X * Real.log (T + 3) ≤
      Real.exp (Real.log T / 2) * (1 + 4 * (Real.log T) ^ 2 + 2 * Real.log T) := by
    have h1 := hp (5 / 2) (by norm_num)
    have h2 := mul_le_mul (hp (3 / 2) (by norm_num)) hsq
      (sq_nonneg _) (Real.exp_pos _).le
    have h3 := mul_le_mul hXhalf hlog hlog0 (Real.exp_pos _).le
    nlinarith
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
  calc
    _ ≤ C * (X ^ (5 / 2 : ℝ) + X ^ (3 / 2 : ℝ) * (Real.log (T + 3)) ^ 2 +
      X * Real.log (T + 3)) / T :=
      div_le_div_of_nonneg_right (hb T X n m hT hm hmn hnX) hT0.le
    _ ≤ C * (Real.exp (Real.log T / 2) *
      (1 + 4 * (Real.log T) ^ 2 + 2 * Real.log T) / T) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hterms hC.le) hT0.le
    _ ≤ C / (Real.log T) ^ 3 := by
      have hs : Real.exp (Real.log T / 2) *
          (1 + 4 * (Real.log T) ^ 2 + 2 * Real.log T) / T ≤ 1 / (Real.log T) ^ 3 :=
        (le_div_iff₀ (pow_pos hLp 3)).2 (by nlinarith [henv])
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hs hC.le

/-- The quartic comparison is negligible on the third-coefficient scale. -/
theorem tendsto_log_mul_horizontalTaylorError
    (u a : ℝ) (ha : 0 < a) (hD : UniformSelbergDensity a) :
    Tendsto (fun T : ℝ => (Real.log T : ℂ) *
      (horizontalTaylorError T u 1 / (T : ℂ))) atTop (𝓝 0) := by
  obtain ⟨C, T₀, hC, hT₀, hden⟩ := hD
  apply log_mul_tendsto_zero_of_inv_log_cube _ (32 * C / (3 * a ^ 4) * u ^ 4)
  filter_upwards [eventually_ge_atTop T₀,
    (tendsto_atTop.1 Real.tendsto_log_atTop) (2 * |u| / a)] with T hT hL
  have hT1 : 1 < T := hT₀.trans_le hT
  have hu : |u| ≤ a * Real.log T / 2 := by
    have hh := (div_le_iff₀ ha).mp hL
    nlinarith
  have h := normalized_horizontalTaylorError_one_of_selberg T u C a
    hT1 hC ha hu (hden T hT)
  simpa only [horizontalTaylorError_one] using h

/-- Rational Landau error is negligible on the third-coefficient scale;
this theorem has no zero-density or RH assumption. -/
theorem tendsto_log_mul_rational_landau_error {n m : ℕ}
    (hm : 1 ≤ m) (hmn : m < n) :
    Tendsto (fun T : ℝ => (Real.log T : ℂ) *
      ((landauSum T (Real.log ((n : ℝ) / (m : ℝ))) +
        ((T * rationalLandauMain n m : ℝ) : ℂ)) / (T : ℂ)))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := eventually_rational_landau_error_le_inv_log_cube
  apply log_mul_tendsto_zero_of_inv_log_cube _ C
  filter_upwards [hb, (tendsto_atTop.1 Real.tendsto_log_atTop)
    (8 * Real.log (n : ℝ))] with T hT hband
  exact hT n m hm hmn (by linarith)

/-- Conditional research reduction: a limit of the rescaled second horizontal
moment supplies exactly the next rational phase coefficient. The density
provider and moment limit are both explicit premises. -/
theorem tendsto_rational_thirdCoefficient_of_horizontalMoment {n m : ℕ}
    (hm : 1 ≤ m) (hmn : m < n) (a : ℝ) (ha : 0 < a)
    (hD : UniformSelbergDensity a) (m₂ : ℂ)
    (hM : Tendsto (fun T : ℝ => (Real.log T : ℂ) *
      (evenHorizontalMoment T (Real.log ((n : ℝ) / (m : ℝ))) 1 / (T : ℂ)))
      atTop (𝓝 m₂)) :
    Tendsto (fun T : ℝ => (Real.log T : ℂ) *
      (ordinateSum T (Real.log ((n : ℝ) / (m : ℝ))) / (T : ℂ) +
        (rationalLandauMain n m : ℂ)))
      atTop (𝓝 (-((Real.log ((n : ℝ) / (m : ℝ)) : ℂ) ^ 2 / 2 * m₂))) := by
  let u := Real.log ((n : ℝ) / (m : ℝ))
  have hE := tendsto_log_mul_horizontalTaylorError u a ha hD
  have hL := tendsto_log_mul_rational_landau_error hm hmn
  have h := (hE.add hL).sub (hM.const_mul ((u : ℂ) ^ 2 / 2))
  simp only [zero_add, zero_sub] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  rw [horizontalTaylorError_one]
  dsimp [u]
  push_cast
  field_simp [hTc]
  ring


/-- Equivalent formulation of the open analytic target: for a nonzero
rational frequency the third coefficient exists with this value exactly when
the rescaled second horizontal moment has the corresponding limit. -/
theorem rational_thirdCoefficient_iff_horizontalMoment {n m : ℕ}
    (hm : 1 ≤ m) (hmn : m < n) (a : ℝ) (ha : 0 < a)
    (hD : UniformSelbergDensity a) (m₂ : ℂ) :
    Tendsto (fun T : ℝ => (Real.log T : ℂ) *
      (ordinateSum T (Real.log ((n : ℝ) / (m : ℝ))) / (T : ℂ) +
        (rationalLandauMain n m : ℂ)))
      atTop (𝓝 (-((Real.log ((n : ℝ) / (m : ℝ)) : ℂ) ^ 2 / 2 * m₂))) ↔
    Tendsto (fun T : ℝ => (Real.log T : ℂ) *
      (evenHorizontalMoment T (Real.log ((n : ℝ) / (m : ℝ))) 1 / (T : ℂ)))
      atTop (𝓝 m₂) := by
  constructor
  · intro hZ
    let u := Real.log ((n : ℝ) / (m : ℝ))
    let c : ℂ := (u : ℂ) ^ 2 / 2
    have hu : 0 < u := (rational_frequency_bounds hm hmn (le_refl (n : ℝ))).1
    have hc : c ≠ 0 := div_ne_zero
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hu.ne')) (by norm_num)
    have hE := tendsto_log_mul_horizontalTaylorError u a ha hD
    have hL := tendsto_log_mul_rational_landau_error hm hmn
    have h := ((hE.add hL).sub hZ).const_mul c⁻¹
    have he : c⁻¹ * (0 + 0 - -(c * m₂)) = m₂ := by
      simp [hc]
    change Tendsto _ atTop (𝓝 (c⁻¹ * (0 + 0 - -(c * m₂)))) at h
    rw [he] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
    rw [horizontalTaylorError_one]
    change c⁻¹ * ((Real.log T : ℂ) *
      ((ordinateSum T u - landauSum T u + c * evenHorizontalMoment T u 1) / (T : ℂ)) +
      (Real.log T : ℂ) * ((landauSum T u + ((T * rationalLandauMain n m : ℝ) : ℂ)) /
        (T : ℂ)) -
      (Real.log T : ℂ) * (ordinateSum T u / (T : ℂ) + (rationalLandauMain n m : ℂ))) =
      (Real.log T : ℂ) * (evenHorizontalMoment T u 1 / (T : ℂ))
    push_cast
    field_simp [hc, hTc]
    ring
  · exact tendsto_rational_thirdCoefficient_of_horizontalMoment hm hmn a ha hD m₂


/-- Every divergent height sequence has a subsequence with a third
coefficient at this rational mode. Only the explicit Selberg provider is
assumed; the horizontal-moment subsequence is supplied by compactness. -/
theorem exists_subseq_rational_thirdCoefficient {n m : ℕ}
    (hm : 1 ≤ m) (hmn : m < n) (a : ℝ) (ha : 0 < a)
    (hD : UniformSelbergDensity a)
    (τ : ℕ → ℝ) (hτ : Tendsto τ atTop atTop) :
    ∃ (m₂ : ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k => (Real.log (τ (φ k)) : ℂ) *
        (evenHorizontalMoment (τ (φ k)) (Real.log ((n : ℝ) / (m : ℝ))) 1 /
          (τ (φ k) : ℂ))) atTop (𝓝 m₂) ∧
      Tendsto (fun k => (Real.log (τ (φ k)) : ℂ) *
        (ordinateSum (τ (φ k)) (Real.log ((n : ℝ) / (m : ℝ))) / (τ (φ k) : ℂ) +
          (rationalLandauMain n m : ℂ)))
        atTop (𝓝 (-((Real.log ((n : ℝ) / (m : ℝ)) : ℂ) ^ 2 / 2 * m₂))) := by
  let u := Real.log ((n : ℝ) / (m : ℝ))
  let E : ℝ → ℂ := fun T => (Real.log T : ℂ) *
    (evenHorizontalMoment T u 1 / (T : ℂ))
  have hErr := tendsto_log_mul_horizontalTaylorError u a ha hD
  have hLand := tendsto_log_mul_rational_landau_error hm hmn
  obtain ⟨C, T₀, hC, hT₀, hden⟩ := hD
  have hb : ∀ᶠ T : ℝ in atTop, ‖E T‖ ≤ 4 * C / a ^ 2 := by
    filter_upwards [eventually_ge_atTop T₀] with T hT
    exact normalized_evenHorizontalMoment_one_le T u C a
      (hT₀.trans_le hT) hC ha (hden T hT)
  have hmem : ∀ᶠ k : ℕ in atTop,
      E (τ k) ∈ Metric.closedBall (0 : ℂ) (4 * C / a ^ 2) := by
    filter_upwards [hτ.eventually hb] with k hk
    simpa only [Metric.mem_closedBall, dist_zero_right] using hk
  obtain ⟨m₂, hm₂, φ, hφ, hM⟩ :=
    (isCompact_closedBall (0 : ℂ) (4 * C / a ^ 2)).tendsto_subseq' hmem.frequently
  refine ⟨m₂, φ, hφ, hM, ?_⟩
  have hheight : Tendsto (fun k => τ (φ k)) atTop atTop :=
    hτ.comp hφ.tendsto_atTop
  have h := ((hErr.comp hheight).add (hLand.comp hheight)).sub
    (hM.const_mul ((u : ℂ) ^ 2 / 2))
  simp only [zero_add, zero_sub] at h
  apply h.congr'
  filter_upwards [hheight.eventually (eventually_gt_atTop (0 : ℝ))] with k hk
  have hTc : (τ (φ k) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
  simp only [Function.comp_apply, E]
  rw [horizontalTaylorError_one]
  dsimp [u]
  push_cast
  field_simp [hTc]
  ring

end RiemannResearch.Analysis.ActualZeroOrdinate
