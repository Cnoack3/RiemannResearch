/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroHorizontalEnergy
import Mathlib.Tactic.FieldSimp

/-!
A second-order horizontal energy, retaining all actual zeta zeros and their
multiplicities.  Its unconditional convergence strengthens the fourth-order
energy: it also supplies the absolute second moment of the latter's ordinate
Fourier measure.  The curvature identity below is algebraic; this module does
not claim a formal proof of differentiability of a Fourier series.

Source: the positive-defect and moving-observable priorities in the user-provided
`Zeta_Zero_Unconditional_Open_Research_Agenda_20261011(1).md` motivate this
development.  Convergence uses the existing unconditional zero-summability
provider, with no RH assumption.  Vanishing remains RH-equivalent.
-/

noncomputable section

open Complex Zeta23
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroHorizontalEnergy

/-- Second-order ordinate damping of the full horizontal displacement. -/
def horizontalSecondTerm (ρ : ActualZero) : ℝ :=
  (zeroMult (ρ : ℂ) : ℝ) * ((ρ : ℂ).re - 1 / 2) ^ 2 /
    (1 + (ρ : ℂ).im ^ 2)

theorem horizontalSecondTerm_nonneg (ρ : ActualZero) :
    0 ≤ horizontalSecondTerm ρ := by
  unfold horizontalSecondTerm
  positivity

theorem horizontalSecondTerm_le_inv_sq (ρ : ActualZero) :
    horizontalSecondTerm ρ ≤ (5 / 16 : ℝ) *
      ((zeroMult (ρ : ℂ) : ℝ) / (1 + normSq (gammaOf (ρ : ℂ)))) := by
  let d : ℝ := (ρ : ℂ).re - 1 / 2
  let B : ℝ := 1 + (ρ : ℂ).im ^ 2
  let M : ℝ := (zeroMult (ρ : ℂ) : ℝ)
  have hstrip : IsNontrivialZero (ρ : ℂ) := ρ.property
  have hd : d ^ 2 ≤ 1 / 4 := by
    dsimp only [d]
    nlinarith [hstrip.2.1, hstrip.2.2, sq_nonneg ((ρ : ℂ).re - 1 / 2)]
  have hB : 1 ≤ B := by
    dsimp only [B]
    nlinarith [sq_nonneg (ρ : ℂ).im]
  have hBp : 0 < B := by linarith
  have hnorm : 1 + normSq (gammaOf (ρ : ℂ)) = B + d ^ 2 := by
    dsimp only [B, d]
    rw [normSq_apply, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im]
    ring
  have hscale : B + d ^ 2 ≤ (5 / 4 : ℝ) * B := by linarith
  have hmain : d ^ 2 * (B + d ^ 2) ≤ (5 / 16 : ℝ) * B := by
    calc
      d ^ 2 * (B + d ^ 2) ≤ (1 / 4 : ℝ) * (B + d ^ 2) :=
        mul_le_mul_of_nonneg_right hd (by positivity)
      _ ≤ (1 / 4 : ℝ) * ((5 / 4 : ℝ) * B) :=
        mul_le_mul_of_nonneg_left hscale (by norm_num)
      _ = (5 / 16 : ℝ) * B := by ring
  have hM : 0 ≤ M := Nat.cast_nonneg _
  change M * d ^ 2 / B ≤ (5 / 16 : ℝ) *
    (M / (1 + normSq (gammaOf (ρ : ℂ))))
  rw [hnorm, ← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hmain hM]

theorem horizontalSecondTerm_summable : Summable horizontalSecondTerm := by
  have hs := (Zeta23.WeilEF.zero_sum_inv_sq zetaSeam).mul_left (5 / 16 : ℝ)
  exact Summable.of_nonneg_of_le horizontalSecondTerm_nonneg
    horizontalSecondTerm_le_inv_sq hs

def horizontalSecondEnergy : ℝ := ∑' ρ : ActualZero, horizontalSecondTerm ρ

theorem horizontalSecondEnergy_nonneg : 0 ≤ horizontalSecondEnergy :=
  tsum_nonneg horizontalSecondTerm_nonneg

theorem horizontalSecondTerm_le_energy (ρ : ActualZero) :
    horizontalSecondTerm ρ ≤ horizontalSecondEnergy := by
  classical
  have h := horizontalSecondTerm_summable.sum_le_tsum ({ρ} : Finset ActualZero)
    (fun σ _ => horizontalSecondTerm_nonneg σ)
  simpa only [Finset.sum_singleton, horizontalSecondEnergy] using h

theorem horizontalTerm_le_secondTerm (ρ : ActualZero) :
    horizontalTerm ρ ≤ horizontalSecondTerm ρ := by
  have hB : 1 ≤ 1 + (ρ : ℂ).im ^ 2 := by nlinarith [sq_nonneg (ρ : ℂ).im]
  have hBp : 0 < 1 + (ρ : ℂ).im ^ 2 := by positivity
  have hnum : 0 ≤ (zeroMult (ρ : ℂ) : ℝ) * ((ρ : ℂ).re - 1 / 2) ^ 2 := by
    positivity
  unfold horizontalTerm horizontalSecondTerm
  exact div_le_div_of_nonneg_left hnum hBp (by nlinarith)

theorem horizontalFourthEnergy_le_secondEnergy :
    horizontalFourthEnergy ≤ horizontalSecondEnergy := by
  exact horizontalTerm_summable.tsum_le_tsum horizontalTerm_le_secondTerm
    horizontalSecondTerm_summable

theorem horizontalSecondEnergy_le :
    horizontalSecondEnergy ≤ (5 / 16 : ℝ) *
      ∑' ρ : ActualZero, (zeroMult (ρ : ℂ) : ℝ) /
        (1 + normSq (gammaOf (ρ : ℂ))) := by
  have hs := Zeta23.WeilEF.zero_sum_inv_sq zetaSeam
  have h := horizontalSecondTerm_summable.tsum_le_tsum
    horizontalSecondTerm_le_inv_sq (hs.mul_left (5 / 16 : ℝ))
  simpa only [horizontalSecondEnergy, tsum_mul_left] using h

theorem horizontalSecondEnergy_eq_zero_iff_RH :
    horizontalSecondEnergy = 0 ↔ RiemannHypothesis := by
  constructor
  · intro hE
    apply horizontalFourthEnergy_eq_zero_iff_RH.mp
    have h := horizontalFourthEnergy_le_secondEnergy
    rw [hE] at h
    exact le_antisymm h horizontalFourthEnergy_nonneg
  · intro hRH
    have hterm : ∀ ρ : ActualZero, horizontalSecondTerm ρ = 0 := by
      intro ρ
      have hline := Zeta23.RH_implies_on_line hRH ρ.property
      simp [horizontalSecondTerm, hline]
    simp only [horizontalSecondEnergy, hterm, tsum_zero]

/-- The second ordinate moment of the fourth-order term has an exact identity. -/
theorem horizontalCurvatureTerm_eq (ρ : ActualZero) :
    (ρ : ℂ).im ^ 2 * horizontalTerm ρ =
      horizontalSecondTerm ρ - horizontalTerm ρ := by
  have hB : 1 + (ρ : ℂ).im ^ 2 ≠ 0 := by positivity
  unfold horizontalTerm horizontalSecondTerm
  field_simp [hB]
  <;> ring

theorem horizontalCurvatureTerm_summable :
    Summable (fun ρ : ActualZero => (ρ : ℂ).im ^ 2 * horizontalTerm ρ) := by
  simpa only [horizontalCurvatureTerm_eq] using
    horizontalSecondTerm_summable.sub horizontalTerm_summable

/-- No endpoint or square term is discarded in this moment identity. -/
theorem horizontalCurvatureEnergy_eq :
    (∑' ρ : ActualZero, (ρ : ℂ).im ^ 2 * horizontalTerm ρ) =
      horizontalSecondEnergy - horizontalFourthEnergy := by
  simp only [horizontalCurvatureTerm_eq]
  exact horizontalSecondTerm_summable.tsum_sub horizontalTerm_summable

/-- A quantitative bound for the displacement of each individual zero. -/
theorem multiplicity_displacement_sq_le_fourthEnergy (ρ : ActualZero) :
    (zeroMult (ρ : ℂ) : ℝ) * ((ρ : ℂ).re - 1 / 2) ^ 2 ≤
      horizontalFourthEnergy * (1 + (ρ : ℂ).im ^ 2) ^ 2 := by
  have h := horizontalTerm_le_energy ρ
  change (zeroMult (ρ : ℂ) : ℝ) * ((ρ : ℂ).re - 1 / 2) ^ 2 /
    (1 + (ρ : ℂ).im ^ 2) ^ 2 ≤ horizontalFourthEnergy at h
  exact (div_le_iff₀ (by positivity)).mp h

/-- The stronger summability theorem gives only quadratic height loss. -/
theorem multiplicity_displacement_sq_le_secondEnergy (ρ : ActualZero) :
    (zeroMult (ρ : ℂ) : ℝ) * ((ρ : ℂ).re - 1 / 2) ^ 2 ≤
      horizontalSecondEnergy * (1 + (ρ : ℂ).im ^ 2) := by
  have h := horizontalSecondTerm_le_energy ρ
  change (zeroMult (ρ : ℂ) : ℝ) * ((ρ : ℂ).re - 1 / 2) ^ 2 /
    (1 + (ρ : ℂ).im ^ 2) ≤ horizontalSecondEnergy at h
  exact (div_le_iff₀ (by positivity)).mp h

end RiemannResearch.Analysis.ActualZeroHorizontalEnergy
