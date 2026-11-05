/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QTreeDigitMellin
import RiemannResearch.RH.ParetoAtomMellinSignature
import RiemannResearch.RH.ParetoUnscaledDilation
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Mellin transform of the conductor staircase

Source for the limiting law: T. Nakamura, *A modified Riemann zeta distribution
in the critical strip*, Proc. Amer. Math. Soc. 143 (2015), 897–905.
The finite staircases and their dilation identity are those of Section 4 of
*Prime trees, fractional parts, and zeta zeros* (5 Nov 2026). -/

noncomputable section
open Set MeasureTheory
namespace RiemannResearch.RH.PrimeTreeMellinLaws
open Pareto ParetoAtomMellinSignature QMellinTransfer ZetaTwoHilbert

/-- The atom at the physical site obtained by magnifying the argument by its conductor. -/
def staircase (D : ℕ) (y : ℝ) : ℝ := normalizedAtom D ⌊(D : ℝ) * y⌋₊

/-- Equation (10) holds for every positive radix at every nonnegative site. -/
theorem staircase_eq_fract (D : ℕ) (hD : 0 < D) (y : ℝ) (hy : 0 ≤ y) :
    staircase D y = Int.fract y - Int.fract ((D : ℝ) * y) / D := by
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hdiv : (D : ℝ) * y / D = y := by field_simp <;> ring
  simpa only [staircase, hdiv] using normalizedAtom_floor_eq_corrected_fract
    D ((D : ℝ) * y) (mul_nonneg (Nat.cast_nonneg _) hy)

theorem staircase_nonneg (D : ℕ) (y : ℝ) : 0 ≤ staircase D y := by
  unfold staircase normalizedAtom Pareto.residue
  positivity

theorem staircase_error (D : ℕ) (hD : 0 < D) (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ Int.fract y - staircase D y ∧
      Int.fract y - staircase D y < 1 / (D : ℝ) := by
  rw [staircase_eq_fract D hD y hy, sub_sub_cancel]
  exact ⟨div_nonneg (Int.fract_nonneg _) (Nat.cast_nonneg _),
    div_lt_div_of_pos_right (Int.fract_lt_one _) (by exact_mod_cast hD)⟩

/-- The unnormalized density increment underlying the entire prime mixture (14). -/
theorem staircase_refine (D p : ℕ) (hD : 0 < D) (hp : 0 < p) (y : ℝ) (hy : 0 ≤ y) :
    staircase (D * p) y = staircase D y + staircase p ((D : ℝ) * y) / D := by
  rw [staircase_eq_fract (D * p) (Nat.mul_pos hD hp) y hy,
    staircase_eq_fract D hD y hy,
    staircase_eq_fract p hp ((D : ℝ) * y) (mul_nonneg (Nat.cast_nonneg _) hy),
    Nat.cast_mul]
  have hprod : (D : ℝ) * p * y = (p : ℝ) * ((D : ℝ) * y) := by ring
  rw [hprod]
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [hD0, hp0]
  <;> ring

theorem staircase_mono_dvd {D D' : ℕ} (hD : 0 < D) (hD' : 0 < D')
    (hdiv : D ∣ D') (y : ℝ) (hy : 0 ≤ y) : staircase D y ≤ staircase D' y := by
  obtain ⟨p, rfl⟩ := hdiv
  have hp : 0 < p := Nat.pos_of_ne_zero (fun e => by simp [e] at hD')
  rw [staircase_refine D p hD hp y hy]
  apply le_add_of_nonneg_right
  exact div_nonneg (staircase_nonneg p _) (Nat.cast_nonneg D)

private theorem mellin_physical (D : ℕ) (s : ℂ) :
    mellin (fun x : ℝ => (normalizedAtom D ⌊x⌋₊ : ℂ)) (-s) =
      qMellin (qResidue D) s := by
  rw [mellin, qMellin_eq_step_integral, qSequence_qResidue]
  simp only [smul_eq_mul]
  let f (x : ℝ) := (x : ℂ) ^ (-s - 1) * (normalizedAtom D ⌊x⌋₊ : ℂ)
  change (∫ x in Ioi 0, f x) = _
  calc
    _ = ∫ x in Ici 1, f x := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun x hx => zero_lt_one.trans_le hx)
      intro x hx
      have hx1 : x < 1 := lt_of_not_ge hx.2
      simp [f, Nat.floor_eq_zero.mpr hx1]
    _ = ∫ x in Ioi 1, f x := integral_Ici_eq_integral_Ioi
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      exact mul_comm _ _

/-- The Mellin transform in (11) preserves the full dilation, even when
the integral falls outside the space of bounded Hilbert functionals. -/
theorem mellin_staircase (D : ℕ) (hD : 0 < D) (s : ℂ) :
    mellin (fun y : ℝ => (staircase D y : ℂ)) (-s) =
      (D : ℂ) ^ s * qMellin (qResidue D) s := by
  have h := mellin_comp_mul_left (fun x : ℝ => (normalizedAtom D ⌊x⌋₊ : ℂ)) (-s)
    (a := (D : ℝ)) (by exact_mod_cast hD)
  simpa only [staircase, neg_neg, smul_eq_mul, Complex.ofReal_natCast,
    mellin_physical] using h

/-- The explicit zeta multiplier of (11), with the removable point excluded. -/
theorem mellin_staircase_zeta (D : ℕ) (hD : 0 < D) (s : ℂ)
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    mellin (fun y : ℝ => (staircase D y : ℂ)) (-s) =
      (1 - (D : ℂ) ^ (s - 1)) * (-(riemannZeta s) / s) := by
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hpow : (D : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hDc)
  have hs0 : s ≠ 0 := by rintro rfl; simpa using hs
  rw [mellin_staircase D hD, qMellin_residue_zeta D hD s hs hs1,
    Complex.cpow_sub _ _ hDc, Complex.cpow_one, Complex.cpow_neg]
  field_simp [hDc, hpow, hs0]
  <;> ring

/-- Finite unnormalized measures already have precisely the intended zeros. -/
theorem mellin_staircase_zero_iff (D : ℕ) (hD : 1 < D) (s : ℂ)
    (hs : 0 < s.re) (hline : s.re ≠ 1) :
    mellin (fun y : ℝ => (staircase D y : ℂ)) (-s) = 0 ↔ riemannZeta s = 0 := by
  have hd : 0 < D := by omega
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpow : (D : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hDc)
  rw [mellin_staircase D hd, mul_eq_zero, or_iff_right hpow]
  exact QTreeDigitMellin.atom_zero_iff D hD s hs hline

end RiemannResearch.RH.PrimeTreeMellinLaws
