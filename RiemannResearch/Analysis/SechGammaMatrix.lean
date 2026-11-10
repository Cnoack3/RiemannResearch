/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.SechGammaBounds
import RiemannResearch.Analysis.IntegerGapSchur
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The cubic Schur bound for the explicit spatial off-diagonal matrix.
Source: user-provided MontgomeryGammaAudit20261110.md, Sections 4--5.
This module bounds its explicitly defined real kernel. The exact identification
with the centered actual-zero matrix is proved in PrimeBandlimitedMatrix. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace RiemannResearch.Analysis.SechGammaMatrix
open SechGammaBounds

theorem log_gap_mul_bound {a b D : ℝ} (ha : 0 < a) (hb : 0 < b)
    (haD : a ≤ D) (hbD : b ≤ D) : |a-b| ≤ D * |Real.log a - Real.log b| := by
  have ho (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y) (hyD : y ≤ D) :
      y-x ≤ D * (Real.log y-Real.log x) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hx hy)
    rw [Real.log_div hx.ne' hy.ne'] at h
    have he : (y-x)/y = 1-x/y := by field_simp
    have hd : (y-x)/y ≤ Real.log y-Real.log x := by rw [he]; linarith
    have hh := (div_le_iff₀ hy).mp hd
    have hl := sub_nonneg.mpr (Real.log_le_log hx hxy)
    calc
      y-x ≤ (Real.log y-Real.log x)*y := hh
      _ ≤ (Real.log y-Real.log x)*D := mul_le_mul_of_nonneg_left hyD hl
      _ = _ := by ring
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr hab), abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log ha hab))]
    simpa only [neg_sub] using ho a b ha hb hab hbD
  · rw [abs_of_nonneg (sub_nonneg.mpr hba), abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hb hba))]
    exact ho b a hb ha hba haD

theorem nat_gap_one_le {n m : ℕ} (hne : n ≠ m) : 1 ≤ |(n : ℝ)-(m : ℝ)| := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hh : (n : ℝ)+1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hh : (m : ℝ)+1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    rw [abs_of_nonneg (by linarith)]
    linarith

def entry (F : ℝ → ℝ) (T : ℝ) (n m : ℕ) : ℝ :=
  if n = m then 0 else
    -(windowSample F T |Real.log n - Real.log m|) / (T * Real.log T)

theorem entry_bound (F : ℝ → ℝ) (hF : Continuous F)
    (hFe : ∀ x, F (-x) = F x) (h0 : windowMoment F 0 = 0)
    {T : ℝ} {D n m : ℕ} (hT : 1 < T) (hTD : 2 * (D : ℝ) ≤ T)
    (hn : 0 < n) (hm : 0 < m) (hnD : n ≤ D) (hmD : m ≤ D) :
    |entry F T n m| ≤
      (24 * absoluteSecondMoment F * (D : ℝ)^3 / (T ^ 3 * Real.log T)) *
        IntegerGapSchur.weight n m := by
  have hM : 0 ≤ absoluteSecondMoment F := integral_nonneg (fun x => by positivity)
  by_cases hne : n = m
  · subst m; simp [entry]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hDR : 0 < (D : ℝ) := hnR.trans_le (by exact_mod_cast hnD)
  have hT0 : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos hT
  let u : ℝ := |Real.log n - Real.log m|
  let d : ℝ := |(n : ℝ)-(m : ℝ)|
  have hd : 1 ≤ d := nat_gap_one_le hne
  have hgap : d ≤ (D : ℝ)*u := log_gap_mul_bound hnR hmR
    (by exact_mod_cast hnD) (by exact_mod_cast hmD)
  have hu0 : 0 < u := by
    by_contra hu
    have hu' : u ≤ 0 := le_of_not_gt hu
    have hprod := mul_nonpos_of_nonneg_of_nonpos hDR.le hu'
    linarith
  have hscale : 1 / T ≤ u / 2 := by
    apply (div_le_iff₀ hT0).mpr
    nlinarith [mul_le_mul_of_nonneg_right hTD hu0.le]
  have hdu : d/(D : ℝ) ≤ u := (div_le_iff₀ hDR).mpr (by nlinarith [hgap])
  have hdp : 0 < d := by linarith
  rw [entry, if_neg hne]
  calc
    _ ≤ 24 * absoluteSecondMoment F / (T ^ 3 * Real.log T * u ^ 3) :=
      normalized_window_bound_of_even F hF hFe h0 hT hu0 hscale
    _ ≤ 24 * absoluteSecondMoment F / (T ^ 3 * Real.log T * (d/(D : ℝ))^3) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hdu 3) (by positivity)
    _ = _ := by
      unfold IntegerGapSchur.weight
      change 24 * absoluteSecondMoment F / (T ^ 3 * Real.log T * (d/(D : ℝ))^3) =
        (24 * absoluteSecondMoment F * (D : ℝ)^3 / (T ^ 3 * Real.log T)) * (1/d^3)
      field_simp

/-- The exact scalar diagonal is absent by definition; this is the spatial
off-diagonal estimate, not an uncentered or raw-pair-correlation assertion. -/
theorem quadratic_bound (F : ℝ → ℝ) (hF : Continuous F)
    (hFe : ∀ x, F (-x) = F x) (h0 : windowMoment F 0 = 0)
    (s : Finset ℕ) (c : ℕ → ℂ) {T : ℝ} {D : ℕ}
    (hT : 1 < T) (hTD : 2 * (D : ℝ) ≤ T)
    (hs : ∀ n ∈ s, 0 < n ∧ n ≤ D) :
    ‖∑ n ∈ s, ∑ m ∈ s, c n * conj (c m) * (entry F T n m : ℂ)‖ ≤
      (72 * absoluteSecondMoment F * ((D : ℝ)/T)^3 / Real.log T) *
        ∑ n ∈ s, ‖c n‖^2 := by
  have hM : 0 ≤ absoluteSecondMoment F := integral_nonneg (fun x => by positivity)
  have hT0 : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos hT
  have h := IntegerGapSchur.quadratic_le s c (fun n m => (entry F T n m : ℂ))
    (B := 24 * absoluteSecondMoment F * (D : ℝ)^3 / (T ^ 3 * Real.log T))
    (by positivity) (fun n hn => (hs n hn).2) (by
      intro n hn m hm
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact entry_bound F hF hFe h0 hT hTD (hs n hn).1 (hs m hm).1
        (hs n hn).2 (hs m hm).2)
  convert! h using 1
  ring

end RiemannResearch.Analysis.SechGammaMatrix
