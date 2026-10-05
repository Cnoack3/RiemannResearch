/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.WeilExplicitFormula.WeilEF.GoodHeights
import RiemannResearch.RH.WeilExplicitFormula.ThmE.FullLineChiProof
import RiemannResearch.RH.WeilExplicitFormula.XiPrime.Hardy.TwoLine
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Full norm bounds for actual zeta on good horizontal segments [-1,2].
The providers are the established actual zeta good heights, Gamma growth,
and functional equation. No horizontal bound is assumed in the final theorem.
Source: existing zeta23 good-height argument and actual functional equation;
fixed-c=2 Landau contour route as in Gonek's 1985 Theorem 1,
https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf.
This module supplies horizontal-side bounds, not the full Landau theorem.
-/

noncomputable section
open Complex Set MeasureTheory
open scoped BigOperators

namespace Zeta23

/-- Full logarithmic-derivative functional equation, retaining its minus sign. -/
theorem logDeriv_riemannZeta_functional {s : ℂ} (him : s.im ≠ 0)
    (hz : riemannZeta (1 - s) ≠ 0) :
    logDeriv riemannZeta s =
      logDeriv XiPrime.chiFE s - logDeriv riemannZeta (1 - s) := by
  have hc := XiPrime.Hardy.chiFE_ne_zero him
  rw [logDeriv_apply, XiPrime.Hardy.deriv_riemannZeta_eq him,
    XiPrime.Hardy.zeta_eq_chiFE_mul him, logDeriv_apply, logDeriv_apply]
  field_simp [hc, hz]

namespace WeilEF

/-- Actual Gamma logarithmic derivative throughout the fixed Landau strip.
The shift is used where the real part is too small for the right-strip bound. -/
theorem norm_logDeriv_GammaR_high_strip :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → 7 ≤ |s.im| →
      ‖logDeriv Gammaℝ s‖ ≤ K * Real.log (2 + |s.im|) := by
  obtain ⟨C, hC, hψ⟩ := ThmE.digamma_growth_wide
  let K₀ : ℝ := |Real.log Real.pi| / 2 + C
  refine ⟨K₀ + 1, by dsimp [K₀]; positivity, ?_⟩
  intro s hs1 hs2 hsim
  let L : ℝ := Real.log (2 + |s.im|)
  have hL : 1 ≤ L := by
    dsimp [L]
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9
    linarith
  have hL0 : 0 ≤ L := by linarith
  have him : s.im ≠ 0 := by intro h; rw [h] at hsim; norm_num at hsim
  have hright : ∀ q : ℂ, 1 / 2 ≤ q.re → q.re ≤ 4 → q.im = s.im →
      ‖logDeriv Gammaℝ q‖ ≤ K₀ * L := by
    intro q hq1 hq2 hqi
    have hψq := hψ (q / 2) (by simp; linarith) (by simp; linarith)
    have hlog : Real.log (2 + |(q / 2).im|) ≤ L := by
      simp only [Complex.div_ofNat_im, hqi, abs_div, abs_two]
      dsimp [L]
      exact Real.log_le_log (by positivity) (by linarith [abs_nonneg s.im])
    have hψL : ‖Complex.digamma (q / 2)‖ ≤ C * L :=
      hψq.trans (mul_le_mul_of_nonneg_left hlog hC.le)
    rw [logDeriv_Gammaℝ (by linarith : 0 < q.re)]
    calc
      _ ≤ ‖-((Real.log Real.pi : ℝ) : ℂ) / 2‖ +
          ‖(1 / 2 : ℂ) * Complex.digamma (q / 2)‖ := norm_add_le _ _
      _ = |Real.log Real.pi| / 2 + (1 / 2) * ‖Complex.digamma (q / 2)‖ := by
        rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_mul]
        norm_num
      _ ≤ |Real.log Real.pi| / 2 * L + C * L := by
        have hconst : |Real.log Real.pi| / 2 ≤ |Real.log Real.pi| / 2 * L := by
          nlinarith [abs_nonneg (Real.log Real.pi)]
        have hhalf : (1 / 2) * ‖Complex.digamma (q / 2)‖ ≤ C * L := by
          nlinarith [norm_nonneg (Complex.digamma (q / 2))]
        linarith
      _ = K₀ * L := by dsimp [K₀]; ring
  by_cases hre : 1 / 2 ≤ s.re
  · exact (hright s hre (by linarith) rfl).trans (by nlinarith)
  · have hshift := XiPrime.Hardy.logDeriv_Gammaℝ_shift him
    have hq := hright (s + 2) (by simp; linarith) (by simp; linarith) (by simp)
    have hinv : ‖(1 : ℂ) / s‖ ≤ L := by
      have hs : 1 ≤ ‖s‖ := le_trans (by linarith) (Complex.abs_im_le_norm s)
      rw [norm_div, norm_one]
      exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hs).trans
        (by simpa using hL)
    rw [hshift]
    calc
      _ ≤ ‖logDeriv Gammaℝ (s + 2)‖ + ‖(1 : ℂ) / s‖ := norm_sub_le _ _
      _ ≤ K₀ * L + L := add_le_add hq hinv
      _ = (K₀ + 1) * L := by ring

/-- Actual good heights with a full complex norm bound on all of [-1,2]. -/
theorem good_heights_full_landau_strip :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℕ → ℝ, ∀ j : ℕ,
      (j : ℝ) + 7 ≤ R j ∧ R j ≤ (j : ℝ) + 8 ∧
      ∀ s : ℂ, (s.im = R j ∨ s.im = -R j) → -1 ≤ s.re → s.re ≤ 2 →
        riemannZeta s ≠ 0 ∧
          ‖logDeriv riemannZeta s‖ ≤ C * (Real.log ((j : ℝ) + 10)) ^ 2 := by
  obtain ⟨Cg, hCg, R, hR⟩ := good_heights
  obtain ⟨K, hK, hΓ⟩ := norm_logDeriv_GammaR_high_strip
  refine ⟨Cg + 2 * K, by positivity, R, ?_⟩
  intro j
  obtain ⟨hR1, hR2, hRs⟩ := hR j
  refine ⟨hR1, hR2, ?_⟩
  intro s hsim hs1 hs2
  let L : ℝ := Real.log ((j : ℝ) + 10)
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hL : 1 ≤ L := by
    dsimp [L]
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9
    linarith
  have hsim7 : 7 ≤ |s.im| := by
    rcases hsim with h | h
    · rw [h, abs_of_nonneg (by linarith : 0 ≤ R j)]; linarith
    · rw [h, abs_neg, abs_of_nonneg (by linarith : 0 ≤ R j)]; linarith
  have hsim8 : |s.im| ≤ (j : ℝ) + 8 := by
    rcases hsim with h | h
    · rw [h, abs_of_nonneg (by linarith : 0 ≤ R j)]; exact hR2
    · rw [h, abs_neg, abs_of_nonneg (by linarith : 0 ≤ R j)]; exact hR2
  have hlog : Real.log (2 + |s.im|) ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by positivity) (by linarith)
  have hLL : L ≤ L ^ 2 := by nlinarith
  by_cases hre : 1 / 2 ≤ s.re
  · obtain ⟨hz, hb⟩ := hRs s hsim hre hs2
    refine ⟨hz, hb.trans ?_⟩
    change Cg * L ^ 2 ≤ (Cg + 2 * K) * L ^ 2
    nlinarith [sq_nonneg L]
  · have him : s.im ≠ 0 := by intro h; rw [h] at hsim7; norm_num at hsim7
    have hrSim : (1 - s).im = R j ∨ (1 - s).im = -R j := by
      rcases hsim with h | h
      · right; simpa [h]
      · left; simpa [h]
    obtain ⟨hz, hb⟩ := hRs (1 - s) hrSim (by simp; linarith) (by simp; linarith)
    have hsZ : riemannZeta s ≠ 0 := by
      rw [XiPrime.Hardy.zeta_eq_chiFE_mul him]
      exact mul_ne_zero (XiPrime.Hardy.chiFE_ne_zero him) hz
    have hΓs := (hΓ s hs1 hs2 hsim7).trans
      (mul_le_mul_of_nonneg_left (hlog.trans hLL) hK.le)
    have hΓr := hΓ (1 - s) (by simp; linarith) (by simp; linarith)
      (by simpa [abs_neg] using hsim7)
    have hΓr' : ‖logDeriv Gammaℝ (1 - s)‖ ≤ K * L ^ 2 := by
      simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at hΓr
      exact hΓr.trans (mul_le_mul_of_nonneg_left (hlog.trans hLL) hK.le)
    refine ⟨hsZ, ?_⟩
    rw [logDeriv_riemannZeta_functional him hz, XiPrime.Hardy.logDeriv_chiFE him]
    have h1 := norm_sub_le
      (-logDeriv Gammaℝ (1 - s) - logDeriv Gammaℝ s)
      (logDeriv riemannZeta (1 - s))
    have h2 := norm_sub_le (-logDeriv Gammaℝ (1 - s)) (logDeriv Gammaℝ s)
    rw [norm_neg] at h2
    change ‖-logDeriv Gammaℝ (1 - s) - logDeriv Gammaℝ s -
      logDeriv riemannZeta (1 - s)‖ ≤ (Cg + 2 * K) * L ^ 2
    change ‖logDeriv riemannZeta (1 - s)‖ ≤ Cg * L ^ 2 at hb
    linarith only [h1, h2, hΓs, hΓr', hb]

/-- Full weighted horizontal integral at an actual good height, uniformly in
the signed frequency u. This is the fixed-c=2 side needed by Landau's contour. -/
theorem good_heights_centered_exponential_horizontals :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℕ → ℝ, ∀ j : ℕ,
      (j : ℝ) + 7 ≤ R j ∧ R j ≤ (j : ℝ) + 8 ∧
      (∀ s : ℂ, (s.im = R j ∨ s.im = -R j) → -1 ≤ s.re → s.re ≤ 2 →
        riemannZeta s ≠ 0) ∧
      ∀ (u y : ℝ), (y = R j ∨ y = -R j) →
        ‖∫ σ in (-1 : ℝ)..2,
          Complex.exp ((u : ℂ) * ((σ : ℂ) + y * I - 1 / 2)) *
            logDeriv riemannZeta ((σ : ℂ) + y * I)‖ ≤
          3 * Real.exp (3 * |u| / 2) * C * (Real.log ((j : ℝ) + 10)) ^ 2 := by
  obtain ⟨C, hC, R, hR⟩ := good_heights_full_landau_strip
  refine ⟨C, hC, R, ?_⟩
  intro j
  obtain ⟨hR1, hR2, hRs⟩ := hR j
  refine ⟨hR1, hR2, fun s hs h1 h2 => (hRs s hs h1 h2).1, ?_⟩
  intro u y hy
  calc
    _ ≤ (Real.exp (3 * |u| / 2) * (C * (Real.log ((j : ℝ) + 10)) ^ 2)) *
        |(2 : ℝ) - (-1)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro σ hσ
      rw [Set.uIoc_of_le (by norm_num)] at hσ
      have hσ1 := hσ.1
      have hσ2 := hσ.2
      have hs : ((σ : ℂ) + y * I).im = R j ∨
          ((σ : ℂ) + y * I).im = -R j := by simpa using hy
      have hζ := (hRs ((σ : ℂ) + y * I) hs (by simp; linarith)
        (by simp; linarith)).2
      have he : ‖Complex.exp ((u : ℂ) * ((σ : ℂ) + y * I - 1 / 2))‖ ≤
          Real.exp (3 * |u| / 2) := by
        rw [Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        have hre : (((u : ℂ) * ((σ : ℂ) + y * I - 1 / 2))).re =
            u * (σ - 1 / 2) := by simp [Complex.mul_re]
        rw [hre]
        have hσabs : |σ - 1 / 2| ≤ 3 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
        calc
          _ ≤ |u * (σ - 1 / 2)| := le_abs_self _
          _ = |u| * |σ - 1 / 2| := abs_mul _ _
          _ ≤ |u| * (3 / 2) := mul_le_mul_of_nonneg_left hσabs (abs_nonneg u)
          _ = _ := by ring
      rw [norm_mul]
      exact mul_le_mul he hζ (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by norm_num; ring

end WeilEF
end Zeta23
