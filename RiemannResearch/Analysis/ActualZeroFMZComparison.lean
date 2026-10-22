/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroTailDensityTransfer
import RiemannResearch.Analysis.ActualZeroTailReflection
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual-zero ordinate comparison from an explicit exponential density input

Source for the comparison strategy and the classical input: Ford--Zaharescu,
"On the distribution of imaginary parts of zeros of the Riemann zeta function",
Lemma 2 and equation (3.8), and Ford--Meng--Zaharescu,
"Simultaneous distribution of the fractional parts of Riemann zeta zeros",
Lemma 2. https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf
https://www.ford126.web.illinois.edu/wwwpapers/FMZ.pdf

The exact actual-zero reflection identity and finite layer cake are imported.
The classical Selberg exponential zero-density theorem is unconditional for
zeta, but remains an explicit actual-count input because its analytic proof
is not yet formalized here. It is neither replaced by RH nor declared as an axiom.
The new deduction retains the finite endpoint formula before deriving the
uniform rational majorant and the explicit small-frequency constant.
-/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroOrdinate

/-- The entire signed reflection correction is dominated by its complete
cosh weight. Critical-line terms vanish exactly at the strict cutoff zero. -/
theorem ordinate_landau_error_le_coshSum (T u : ℝ) :
    ‖ordinateSum T u - landauSum T u‖ ≤
      badWeightedSum T 0 (fun t => Real.cosh (|u| * t) - 1) := by
  rw [ordinateSum, landauSum_eq_cosh, ← sum_sub]
  calc
    _ ≤ realSum T (fun ρ => ‖phase u ρ.im -
        phase u ρ.im * (Real.cosh (u * (ρ.re - 1 / 2)) : ℂ)‖) := norm_sum_le _ _
    _ = _ := by
      rw [badWeightedSum_eq_realSum]
      congr 1
      funext ρ
      by_cases ha : ρ.re - 1 / 2 = 0
      · simp only [ha, mul_zero, Real.cosh_zero, Complex.ofReal_one, mul_one,
          sub_self, norm_zero, abs_zero, ite_false, lt_self_iff_false]
      · have hpos : 0 < |ρ.re - 1 / 2| := abs_pos.mpr ha
        rw [if_pos hpos]
        have heq : phase u ρ.im - phase u ρ.im *
            (Real.cosh (u * (ρ.re - 1 / 2)) : ℂ) =
            phase u ρ.im * (1 - (Real.cosh (u * (ρ.re - 1 / 2)) : ℂ)) := by ring
        rw [heq, norm_mul, phase_norm, one_mul, norm_sub_rev,
          ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_cosh _))]
        congr 1
        rw [← abs_mul, Real.cosh_abs]

/-- Complete finite endpoint bound; the density hypothesis is the only
domain-specific analytic premise. The frequency can have either sign. -/
theorem ordinate_landau_error_of_expTail_closed
    (T u K q : ℝ) (huq : |u| < q)
    (htail : ∀ t ∈ Icc (0 : ℝ) (1 / 2),
      strictTail T t ≤ K * Real.exp (-q * t)) :
    ‖ordinateSum T u - landauSum T u‖ ≤
      K * (|u| / 2) *
        ((1 - Real.exp (-(q - |u|) / 2)) / (q - |u|) -
          (1 - Real.exp (-(q + |u|) / 2)) / (q + |u|)) := by
  have h := badCoshSum_le_of_expTail_closed T 0 |u| K q
    (by norm_num) (by norm_num) (abs_nonneg u) huq htail
  apply (ordinate_landau_error_le_coshSum T u).trans
  simpa only [mul_zero, Real.cosh_zero, sub_self, zero_mul, Real.exp_zero,
    zero_add, mul_assoc] using h

/-- Both finite exponential endpoint terms have the correct sign when the
frequency is below the density exponent. -/
theorem coshTail_endpoint_remainder_nonneg (y q : ℝ)
    (hy : 0 ≤ y) (hyq : y < q) :
    0 ≤ Real.exp (-(q - y) / 2) / (q - y) -
      Real.exp (-(q + y) / 2) / (q + y) := by
  have hm : 0 < q - y := sub_pos.mpr hyq
  have hp : 0 < q + y := by linarith
  apply sub_nonneg.mpr
  apply (div_le_div_iff₀ hp hm).mpr
  have he : Real.exp (-(q + y) / 2) ≤ Real.exp (-(q - y) / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ Real.exp (-(q - y) / 2) * (q - y) :=
      mul_le_mul_of_nonneg_right he hm.le
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg _)

/-- The rational majorant of the exact finite cosh layer cake. -/
theorem coshTail_closed_le_rational (y q : ℝ) (hy : 0 ≤ y) (hyq : y < q) :
    (y / 2) *
      ((1 - Real.exp (-(q - y) / 2)) / (q - y) -
        (1 - Real.exp (-(q + y) / 2)) / (q + y)) ≤
      y ^ 2 / (q ^ 2 - y ^ 2) := by
  have hm : 0 < q - y := sub_pos.mpr hyq
  have hp : 0 < q + y := by linarith
  have hd : 0 < q ^ 2 - y ^ 2 := by nlinarith [mul_pos hm hp]
  have hb :
      (1 - Real.exp (-(q - y) / 2)) / (q - y) -
        (1 - Real.exp (-(q + y) / 2)) / (q + y) ≤
      1 / (q - y) - 1 / (q + y) := by
    calc
      _ = (1 / (q - y) - 1 / (q + y)) -
          (Real.exp (-(q - y) / 2) / (q - y) -
            Real.exp (-(q + y) / 2) / (q + y)) := by ring
      _ ≤ _ := sub_le_self _ (coshTail_endpoint_remainder_nonneg y q hy hyq)
  calc
    _ ≤ (y / 2) * (1 / (q - y) - 1 / (q + y)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by
      field_simp [ne_of_gt hm, ne_of_gt hp, ne_of_gt hd]
      ring

/-- Actual ordinate weight removal from an absolute exponential tail bound. -/
theorem ordinate_landau_error_of_expTail
    (T u K q : ℝ) (hK : 0 ≤ K) (huq : |u| < q)
    (htail : ∀ t ∈ Icc (0 : ℝ) (1 / 2),
      strictTail T t ≤ K * Real.exp (-q * t)) :
    ‖ordinateSum T u - landauSum T u‖ ≤
      K * u ^ 2 / (q ^ 2 - u ^ 2) := by
  have h := ordinate_landau_error_of_expTail_closed T u K q huq htail
  calc
    _ ≤ K * ((|u| / 2) *
        ((1 - Real.exp (-(q - |u|) / 2)) / (q - |u|) -
          (1 - Real.exp (-(q + |u|) / 2)) / (q + |u|))) := by
      simpa only [mul_assoc] using h
    _ ≤ K * (|u| ^ 2 / (q ^ 2 - |u| ^ 2)) :=
      mul_le_mul_of_nonneg_left (coshTail_closed_le_rational |u| q (abs_nonneg u) huq) hK
    _ = _ := by simp only [sq_abs]; ring

/-- The paper's right-half tail convention introduces precisely the factor
two supplied by actual multiplicity-preserving reflection. -/
theorem ordinate_landau_error_of_right_expTail
    (T u K q : ℝ) (hK : 0 ≤ K) (huq : |u| < q)
    (htail : ∀ t ∈ Icc (0 : ℝ) (1 / 2),
      rightStrictTail T t ≤ K * Real.exp (-q * t)) :
    ‖ordinateSum T u - landauSum T u‖ ≤
      2 * K * u ^ 2 / (q ^ 2 - u ^ 2) := by
  apply ordinate_landau_error_of_expTail T u (2 * K) q (by positivity) huq
  intro t ht
  rw [strictTail_eq_twice_right T t ht.1]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (htail t ht) (by norm_num : (0 : ℝ) ≤ 2)

/-- Quantitative FMZ comparison, deduced from the explicitly supplied actual
Selberg right-tail estimate. No hypothesis about RH is used. -/
theorem normalized_ordinate_landau_error_of_selberg
    (T u C : ℝ) (hT : 0 < T) (hL : 0 < Real.log T) (hC : 0 ≤ C)
    (hu : |u| < Real.log T / 4)
    (htail : ∀ t ∈ Icc (0 : ℝ) (1 / 2),
      rightStrictTail T t ≤ C * T * Real.log T * Real.exp (-(Real.log T / 4) * t)) :
    ‖(ordinateSum T u - landauSum T u) / (T : ℂ)‖ ≤
      2 * C * Real.log T * u ^ 2 / ((Real.log T) ^ 2 / 16 - u ^ 2) := by
  have h := ordinate_landau_error_of_right_expTail T u
    (C * T * Real.log T) (Real.log T / 4) (by positivity) hu htail
  have hm : 0 < Real.log T / 4 - |u| := sub_pos.mpr hu
  have hp : 0 < Real.log T / 4 + |u| := by positivity
  have hd : 0 < (Real.log T) ^ 2 / 16 - u ^ 2 := by
    nlinarith [mul_pos hm hp, sq_abs u]
  have hdeq : (Real.log T / 4) ^ 2 - u ^ 2 =
      (Real.log T) ^ 2 / 16 - u ^ 2 := by ring
  rw [hdeq] at h
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  apply (div_le_iff₀ hT).mpr
  calc
    _ ≤ 2 * (C * T * Real.log T) * u ^ 2 /
        ((Real.log T) ^ 2 / 16 - u ^ 2) := h
    _ = _ := by
      field_simp [ne_of_gt hT, ne_of_gt hd]

/-- The explicit small-frequency constant on the complete band `|u| ≤ log T/8`. -/
theorem normalized_ordinate_landau_error_of_selberg_band
    (T u C : ℝ) (hT : 0 < T) (hL : 0 < Real.log T) (hC : 0 ≤ C)
    (hu : |u| ≤ Real.log T / 8)
    (htail : ∀ t ∈ Icc (0 : ℝ) (1 / 2),
      rightStrictTail T t ≤ C * T * Real.log T * Real.exp (-(Real.log T / 4) * t)) :
    ‖(ordinateSum T u - landauSum T u) / (T : ℂ)‖ ≤
      (128 * C / 3) * u ^ 2 / Real.log T := by
  have hu' : |u| < Real.log T / 4 := by linarith
  have h := normalized_ordinate_landau_error_of_selberg T u C hT hL hC hu' htail
  have hs : 0 < 3 * (Real.log T) ^ 2 / 64 := by positivity
  have hprod : 0 ≤ (Real.log T / 8 - |u|) * (Real.log T / 8 + |u|) :=
    mul_nonneg (by linarith) (by positivity)
  have hden : 3 * (Real.log T) ^ 2 / 64 ≤ (Real.log T) ^ 2 / 16 - u ^ 2 := by
    nlinarith [hprod, sq_abs u]
  have hd : 0 < (Real.log T) ^ 2 / 16 - u ^ 2 := lt_of_lt_of_le hs hden
  apply h.trans
  calc
    _ ≤ (2 * C * Real.log T * u ^ 2) / (3 * (Real.log T) ^ 2 / 64) := by
      apply (div_le_div_iff₀ hd hs).mpr
      exact mul_le_mul_of_nonneg_left hden (by positivity)
    _ = _ := by
      field_simp [ne_of_gt hL]
      ring

/-- Actual finite Fourier synthesis retains every signed coefficient; only
the complete horizontal remainder is estimated. This is the quadratic
frequency budget used for the weighted Wiener extension on paper. -/
theorem finiteFourier_ordinate_landau_error_of_selberg
    {ι : Type*} (s : Finset ι) (a : ι → ℂ) (frequency : ι → ℝ)
    (T C : ℝ) (hT : 0 < T) (hL : 0 < Real.log T) (hC : 0 ≤ C)
    (hfrequency : ∀ i ∈ s, |frequency i| ≤ Real.log T / 8)
    (htail : ∀ t ∈ Icc (0 : ℝ) (1 / 2),
      rightStrictTail T t ≤ C * T * Real.log T * Real.exp (-(Real.log T / 4) * t)) :
    ‖∑ i ∈ s, a i *
        ((ordinateSum T (frequency i) - landauSum T (frequency i)) / (T : ℂ))‖ ≤
      ((128 * C / 3) / Real.log T) * ∑ i ∈ s, ‖a i‖ * (frequency i) ^ 2 := by
  calc
    _ ≤ ∑ i ∈ s, ‖a i *
        ((ordinateSum T (frequency i) - landauSum T (frequency i)) / (T : ℂ))‖ :=
      _root_.norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ((128 * C / 3) / Real.log T) *
        (‖a i‖ * (frequency i) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      have hb := normalized_ordinate_landau_error_of_selberg_band T (frequency i) C
        hT hL hC (hfrequency i hi) htail
      calc
        _ ≤ ‖a i‖ * ((128 * C / 3) * (frequency i) ^ 2 / Real.log T) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [← Finset.mul_sum]

/-- Every fixed ordinate-only Fourier mode differs from its centered Landau
mode by a term tending to zero at the `T` normalization, given the classical
eventual actual right-tail estimate. The density provider is explicit. -/
theorem tendsto_ordinate_landau_error_div_of_selberg
    (u C : ℝ) (hC : 0 ≤ C)
    (htail : ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc (0 : ℝ) (1 / 2),
      rightStrictTail T t ≤ C * T * Real.log T * Real.exp (-(Real.log T / 4) * t)) :
    Tendsto (fun T : ℝ => (ordinateSum T u - landauSum T u) / (T : ℂ))
      atTop (𝓝 0) := by
  have hg : Tendsto (fun T : ℝ => ((128 * C / 3) * u ^ 2) * (Real.log T)⁻¹)
      atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul
      ((128 * C / 3) * u ^ 2)
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [htail, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (8 * |u|)] with T hd hT hband
  have hfreq : |u| ≤ Real.log T / 8 := by linarith
  simpa only [div_eq_mul_inv] using normalized_ordinate_landau_error_of_selberg_band
    T u C (by linarith) (Real.log_pos hT) hC hfreq hd

end RiemannResearch.Analysis.ActualZeroOrdinate
