/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.WeilExplicitFormula.Statement.SeamClosed
import RiemannResearch.RH.WeilExplicitFormula.WeilEF.ZeroSummability
import RiemannResearch.RH.RiemannHypothesisStrip
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
An absolutely convergent nonnegative horizontal-displacement energy for all
actual nontrivial zeros of Mathlib's `riemannZeta`, with analytic multiplicity.

The existing unconditional reciprocal-square zero sum supplies convergence.
The denominator `1 + im(rho)^2` avoids any low-height or nonreal-zero provider.
The equality to zero is exactly equivalent to Mathlib's Riemann hypothesis;
this module does not prove that equality.

Source: the user-provided `Ordinate_Harmonic_Theory_20261010(1).md`, Section 4,
motivates retaining a positive horizontal-displacement obstruction. The
regularized fourth-order energy below is independently developed finite and
summability algebra, using the existing actual-zeta summability provider.
-/

noncomputable section

open Complex Zeta23
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroHorizontalEnergy

/-- All actual nontrivial zeros; no ordinate sign or height cutoff is imposed. -/
abbrev ActualZero := (zetaZeros zetaSeam).carrier

/-- A fourth-order ordinate weight retaining every horizontal displacement. -/
def horizontalTerm (ρ : ActualZero) : ℝ :=
  (zeroMult (ρ : ℂ) : ℝ) * ((ρ : ℂ).re - 1 / 2) ^ 2 /
    (1 + (ρ : ℂ).im ^ 2) ^ 2

theorem horizontalTerm_nonneg (ρ : ActualZero) : 0 ≤ horizontalTerm ρ := by
  unfold horizontalTerm
  positivity

/-- The open critical strip gives a concrete domination by the known zero sum. -/
theorem horizontalTerm_le_inv_sq (ρ : ActualZero) :
    horizontalTerm ρ ≤ (5 / 16 : ℝ) *
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
  have hmain : d ^ 2 * (B + d ^ 2) ≤ (5 / 16 : ℝ) * B ^ 2 := by
    calc
      d ^ 2 * (B + d ^ 2) ≤ (1 / 4 : ℝ) * (B + d ^ 2) :=
        mul_le_mul_of_nonneg_right hd (by positivity)
      _ ≤ (1 / 4 : ℝ) * ((5 / 4 : ℝ) * B) :=
        mul_le_mul_of_nonneg_left hscale (by norm_num)
      _ = (5 / 16 : ℝ) * B := by ring
      _ ≤ (5 / 16 : ℝ) * B ^ 2 := by nlinarith
  have hM : 0 ≤ M := Nat.cast_nonneg _
  change M * d ^ 2 / B ^ 2 ≤ (5 / 16 : ℝ) *
    (M / (1 + normSq (gammaOf (ρ : ℂ))))
  rw [hnorm, ← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hmain hM]

/-- Actual-zero summability is supplied unconditionally by the existing theorem. -/
theorem horizontalTerm_summable : Summable horizontalTerm := by
  have hs := (Zeta23.WeilEF.zero_sum_inv_sq zetaSeam).mul_left (5 / 16 : ℝ)
  exact Summable.of_nonneg_of_le horizontalTerm_nonneg horizontalTerm_le_inv_sq hs

/-- Every zero contributes its full positive multiplicity-weighted displacement. -/
def horizontalFourthEnergy : ℝ := ∑' ρ : ActualZero, horizontalTerm ρ

theorem horizontalFourthEnergy_nonneg : 0 ≤ horizontalFourthEnergy :=
  tsum_nonneg horizontalTerm_nonneg

/-- An explicit finite upper bound in terms of the known reciprocal-square sum. -/
theorem horizontalFourthEnergy_le :
    horizontalFourthEnergy ≤ (5 / 16 : ℝ) *
      ∑' ρ : ActualZero, (zeroMult (ρ : ℂ) : ℝ) /
        (1 + normSq (gammaOf (ρ : ℂ))) := by
  have hs := Zeta23.WeilEF.zero_sum_inv_sq zetaSeam
  have h := horizontalTerm_summable.tsum_le_tsum horizontalTerm_le_inv_sq
    (hs.mul_left (5 / 16 : ℝ))
  simpa only [horizontalFourthEnergy, tsum_mul_left] using h

/-- A single actual zero's term cannot exceed the total nonnegative energy. -/
theorem horizontalTerm_le_energy (ρ : ActualZero) :
    horizontalTerm ρ ≤ horizontalFourthEnergy := by
  classical
  have h := horizontalTerm_summable.sum_le_tsum ({ρ} : Finset ActualZero)
    (fun σ _ => horizontalTerm_nonneg σ)
  simpa only [Finset.sum_singleton, horizontalFourthEnergy] using h

/-- Zero energy forces every individual horizontal displacement to vanish. -/
theorem on_line_of_horizontalFourthEnergy_zero (hE : horizontalFourthEnergy = 0)
    (ρ : ActualZero) : (ρ : ℂ).re = 1 / 2 := by
  have ht := horizontalTerm_le_energy ρ
  rw [hE] at ht
  have hden : 0 < (1 + (ρ : ℂ).im ^ 2) ^ 2 := by positivity
  change (zeroMult (ρ : ℂ) : ℝ) * ((ρ : ℂ).re - 1 / 2) ^ 2 /
    (1 + (ρ : ℂ).im ^ 2) ^ 2 ≤ 0 at ht
  have hnum := (div_le_iff₀ hden).mp ht
  simp only [zero_mul] at hnum
  have hm : (0 : ℝ) < (zeroMult (ρ : ℂ) : ℝ) := by
    have hmnat : 0 < zeroMult (ρ : ℂ) :=
      zetaSeam.one_le_mult (ρ : ℂ) ρ.property
    exact_mod_cast hmnat
  have hsq : ((ρ : ℂ).re - 1 / 2) ^ 2 ≤ 0 :=
    nonpos_of_mul_nonpos_left (by simpa [mul_comm] using hnum) hm
  nlinarith [sq_nonneg ((ρ : ℂ).re - 1 / 2)]

/-- The all-zero energy is zero exactly when Mathlib's Riemann hypothesis holds. -/
theorem horizontalFourthEnergy_eq_zero_iff_RH :
    horizontalFourthEnergy = 0 ↔ RiemannHypothesis := by
  constructor
  · intro hE
    apply RiemannResearch.RH.riemannHypothesis_iff_strip_zeros_on_line.mpr
    intro s hz h0 h1
    exact on_line_of_horizontalFourthEnergy_zero hE (⟨s, hz, h0, h1⟩ : ActualZero)
  · intro hRH
    have hterm : ∀ ρ : ActualZero, horizontalTerm ρ = 0 := by
      intro ρ
      have hline := Zeta23.RH_implies_on_line hRH ρ.property
      simp [horizontalTerm, hline]
    simp only [horizontalFourthEnergy, hterm, tsum_zero]

/-- Failure of RH is equivalent to a strictly positive, convergent obstruction. -/
theorem horizontalFourthEnergy_pos_iff_not_RH :
    0 < horizontalFourthEnergy ↔ ¬ RiemannHypothesis := by
  constructor
  · intro hpos hRH
    have hzero := horizontalFourthEnergy_eq_zero_iff_RH.mpr hRH
    rw [hzero] at hpos
    exact lt_irrefl _ hpos
  · intro hnot
    have hzero : horizontalFourthEnergy ≠ 0 := by
      intro hzero
      exact hnot (horizontalFourthEnergy_eq_zero_iff_RH.mp hzero)
    exact lt_of_le_of_ne horizontalFourthEnergy_nonneg (Ne.symm hzero)

end RiemannResearch.Analysis.ActualZeroHorizontalEnergy
