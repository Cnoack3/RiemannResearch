/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroSelbergDensity
import RiemannResearch.Analysis.ActualZeroCountUpper
import RiemannResearch.Analysis.ActualZeroDensityLogExcess
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Selberg density endpoints and exact exponent transfer

Source for the target and proof strategy: Simonic, arXiv:1910.08274,
Sections 4.3--4.5, https://arxiv.org/html/1910.08274v2 .

This module does not supply positive-exponent uniform Selberg density.
It proves the zero-exponent total-count endpoint, bounded logarithmic strips,
monotonicity in the exponent, and a conditional partial-strip extension.
The exact shifted-window identity retains both nonnegative excess terms
before the exponent-preserving estimate. Its optimal shift is elementary.

The substantive weighted-zero-excess or partial-strip density input remains
explicit. See RH/SelbergDensityFormalization20261028.md for the remaining
mollifier-moment and horizontal-boundary obligations. These results feed the
actual prime-phase FMZ program without introducing a new analytic axiom.
-/

noncomputable section
open Set Filter Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Lowering the exponential density exponent weakens the bound. -/
theorem selbergDensityBound_mono_exponent {T C a b : ℝ}
    (hT : 1 < T) (hC : 0 ≤ C) (hba : b ≤ a)
    (hD : SelbergDensityBound T C a) :
    SelbergDensityBound T C b := by
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  apply (selbergDensityBound_iff_exp T C b hT0).mpr
  intro σ hσ
  have hδ : 0 ≤ σ - 1 / 2 := sub_nonneg.mpr hσ.1
  have hexp : Real.exp (-(a * Real.log T) * (σ - 1 / 2)) ≤
      Real.exp (-(b * Real.log T) * (σ - 1 / 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hba) (mul_nonneg hL.le hδ)]
  exact ((selbergDensityBound_iff_exp T C a hT0).mp hD σ hσ).trans
    (mul_le_mul_of_nonneg_left hexp (by positivity))

theorem uniformSelbergDensity_mono {a b : ℝ} (hba : b ≤ a)
    (hD : UniformSelbergDensity a) : UniformSelbergDensity b := by
  obtain ⟨C, T₀, hC, hT₀, hD⟩ := hD
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T hT
  exact selbergDensityBound_mono_exponent (hT₀.trans_le hT) hC hba (hD T hT)

/-- The exponent-zero endpoint is the unconditional total-count estimate.
It gives no decay as sigma moves to the right and does not discharge the
positive-exponent Selberg hypothesis. -/
theorem uniformSelbergDensity_zero : UniformSelbergDensity 0 := by
  obtain ⟨C, hC, hb⟩ := exists_count_le_height_log
  refine ⟨C, 9, hC.le, by norm_num, ?_⟩
  intro T hT σ hσ
  simpa only [zero_mul, sub_zero, Real.rpow_one] using
    (rightInclusiveCount_le_count T σ).trans (hb T hT)

/-- On a strip of bounded logarithmic width, any fixed nonnegative exponent
can be inserted into the total-count bound, with an explicit factor exp(a*A).
This is unconditional, but its width condition is essential. It is NOT a
positive-exponent full-strip Selberg theorem. A may be any real number. -/
theorem exists_selberg_form_on_logarithmic_strip (a A : ℝ) (ha : 0 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 9 ≤ T → ∀ σ : ℝ,
      (σ - 1 / 2) * Real.log T ≤ A →
      rightInclusiveCount T σ ≤
        C * T ^ (1 - a * (σ - 1 / 2)) * Real.log T := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_count_le_height_log
  refine ⟨C₀ * Real.exp (a * A), by positivity, ?_⟩
  intro T hT σ hband
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  have he : 1 ≤ Real.exp (a * A) *
      Real.exp (-(a * Real.log T) * (σ - 1 / 2)) := by
    rw [← Real.exp_add]
    calc
      1 = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        nlinarith [mul_nonneg ha (sub_nonneg.mpr hband)])
  calc
    rightInclusiveCount T σ ≤ C₀ * T * Real.log T :=
      (rightInclusiveCount_le_count T σ).trans (hb T hT)
    _ ≤ (C₀ * Real.exp (a * A)) *
        (T * Real.log T * Real.exp (-(a * Real.log T) * (σ - 1 / 2))) := by
      have hh := mul_le_mul_of_nonneg_left he
        (show 0 ≤ C₀ * T * Real.log T by positivity)
      calc
        C₀ * T * Real.log T = (C₀ * T * Real.log T) * 1 := by ring
        _ ≤ (C₀ * T * Real.log T) * (Real.exp (a * A) *
          Real.exp (-(a * Real.log T) * (σ - 1 / 2))) := hh
        _ = _ := by ring
    _ = (C₀ * Real.exp (a * A)) * T ^ (1 - a * (σ - 1 / 2)) *
        Real.log T := by
      rw [← selberg_power_kernel_eq_exp T a σ hT0]
      ring


/-- Inclusive actual-zero counts are antitone in the real-part cutoff. -/
theorem rightInclusiveCount_antitone (T : ℝ) : Antitone (rightInclusiveCount T) := by
  intro α β hab
  unfold rightInclusiveCount
  apply realSum_mono
  intro ρ hρ
  by_cases hb : β ≤ ρ.re
  · simp [hb, hab.trans hb]
  · simp only [if_neg hb]
    split_ifs <;> norm_num

/-- A stronger estimate on a truncated strip extends to a weaker exponent
on the whole strip. The cutoff and exponent loss are explicit. -/
theorem selbergDensityBound_of_partial
    {T C a b σ₀ : ℝ} (hT : 1 < T) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hba : b ≤ a) (hσ₀ : σ₀ ∈ Icc (1 / 2 : ℝ) 1)
    (hcover : b / 2 ≤ a * (σ₀ - 1 / 2))
    (hpartial : ∀ σ ∈ Icc (1 / 2 : ℝ) σ₀,
      rightInclusiveCount T σ ≤ C * T ^ (1 - a * (σ - 1 / 2)) * Real.log T) :
    SelbergDensityBound T C b := by
  intro σ hσ
  have hL : 0 ≤ Real.log T := (Real.log_pos hT).le
  by_cases hs : σ ≤ σ₀
  · apply (hpartial σ ⟨hσ.1, hs⟩).trans
    apply mul_le_mul_of_nonneg_right _ hL
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.rpow_le_rpow_of_exponent_le hT.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr hσ.1)]
  · apply ((rightInclusiveCount_antitone T (le_of_not_ge hs)).trans
      (hpartial σ₀ ⟨hσ₀.1, le_rfl⟩)).trans
    apply mul_le_mul_of_nonneg_right _ hL
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.rpow_le_rpow_of_exponent_le hT.le
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hσ.2)]

/-- Concrete closure of the full one-quarter Selberg strip from a
five-sixteenths estimate only up to sigma = 9/10.
The partial-strip analytic estimate remains a substantive premise. -/
theorem uniformSelbergDensity_quarter_of_five_sixteenths
    (hpartial : ∃ C T₀ : ℝ, 0 ≤ C ∧ 1 < T₀ ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ σ ∈ Icc (1 / 2 : ℝ) (9 / 10),
        rightInclusiveCount T σ ≤
          C * T ^ (1 - (5 / 16 : ℝ) * (σ - 1 / 2)) * Real.log T) :
    UniformSelbergDensity (1 / 4) := by
  obtain ⟨C, T₀, hC, hT₀, hb⟩ := hpartial
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T hT
  exact selbergDensityBound_of_partial (a := 5 / 16) (σ₀ := 9 / 10)
    (hT₀.trans_le hT) hC (by norm_num) (by norm_num)
    (by constructor <;> norm_num) (by norm_num) (hb T hT)

/-- Exact count recovery at the shift 1/(c log T), retaining both nonnegative
log-excess terms before any inequality is applied. -/
theorem selberg_shift_count_exact (H T σ c : ℝ) (hT : 1 < T) (hc : 0 < c) :
    rightInclusiveWindow H T σ =
      (c * Real.log T) *
        (rightLogExcessWindow H T (σ - 1 / (c * Real.log T)) -
          rightLogExcessAboveWindow H T σ -
          rightLogExcessBandWindow H T (σ - 1 / (c * Real.log T)) σ) := by
  have hq : 0 < c * Real.log T := mul_pos hc (Real.log_pos hT)
  rw [rightLogExcessWindow_exact H T _ σ (by linarith [one_div_pos.mpr hq])]
  field_simp [hc.ne', (Real.log_pos hT).ne']
  ring

/-- The optimized logarithmic shift preserves the source density exponent.
This is a transfer from an actual weighted-zero-excess estimate, not a
provider of that still-substantive analytic estimate. -/
theorem densityWindow_le_of_shifted_logExcess
    {H T σ c D E : ℝ} (hT : 1 < T) (hc : 0 < c)
    (hsource : rightLogExcessWindow H T (σ - 1 / (c * Real.log T)) ≤
      D * T * Real.exp (-(c * Real.log T) * (σ - 1 / (c * Real.log T) - 1 / 2)) +
        E * Real.log T) :
    rightInclusiveWindow H T σ ≤
      (c * Real.exp 1 * D) * T * Real.log T *
        Real.exp (-(c * Real.log T) * (σ - 1 / 2)) +
        c * E * (Real.log T) ^ 2 := by
  have hq : 0 < c * Real.log T := mul_pos hc (Real.log_pos hT)
  have he : -(c * Real.log T) * (σ - 1 / (c * Real.log T) - 1 / 2) =
      1 + (-(c * Real.log T) * (σ - 1 / 2)) := by
    field_simp [hc.ne', (Real.log_pos hT).ne']
    ring
  have hh := rightLogExcessAboveWindow_nonneg H T σ
  have hb := rightLogExcessBandWindow_nonneg H T (σ - 1 / (c * Real.log T)) σ
  rw [selberg_shift_count_exact H T σ c hT hc]
  calc
    _ ≤ (c * Real.log T) *
        (D * T * Real.exp (-(c * Real.log T) *
          (σ - 1 / (c * Real.log T) - 1 / 2)) + E * Real.log T) := by
      apply mul_le_mul_of_nonneg_left _ hq.le
      linarith
    _ = _ := by rw [he, Real.exp_add]; ring

/-- The chosen shift minimizes exp(q*h)/h over all positive h.
This sharp elementary constant is independent of any zeta hypothesis. -/
theorem selberg_shift_optimal {q h : ℝ} (hh : 0 < h) :
    q * Real.exp 1 ≤ Real.exp (q * h) / h := by
  apply (le_div_iff₀ hh).mpr
  nlinarith [Real.exp_one_mul_le_exp (x := q * h)]

end RiemannResearch.Analysis.ActualZeroOrdinate

#print axioms RiemannResearch.Analysis.ActualZeroOrdinate.uniformSelbergDensity_zero
#print axioms RiemannResearch.Analysis.ActualZeroOrdinate.selberg_shift_count_exact
