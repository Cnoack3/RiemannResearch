/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PrimeTowerQuadratic

/-!
# Finite-kernel stability and zero-extension boundary

Source: Signed_Quadratic_Correction_Research_Note.pdf, §§3.2 and 10.4.
These are exact finite identities, independent of an analytic phase law.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.PrimeTowerQuadratic

/-- Left endpoint row in the general geometric tridiagonal inverse identity. -/
theorem geometric_inverse_left_row (r : ℝ) (i : ℕ) :
    r ^ i - r * r ^ ((i - 1) + (1 - i)) =
      if i = 0 then 1 - r ^ 2 else 0 := by
  cases i with
  | zero => norm_num; ring
  | succ i => simp [pow_succ]; ring

/-- Right endpoint row, retaining its finite boundary hypothesis. -/
theorem geometric_inverse_right_row (r : ℝ) (i K : ℕ)
    (hK : 1 ≤ K) (hi : i ≤ K) :
    r ^ (K - i) - r * r ^ ((i - (K - 1)) + ((K - 1) - i)) =
      if i = K then 1 - r ^ 2 else 0 := by
  have hd : (i - (K - 1)) + ((K - 1) - i) =
      ((K - i) - 1) + (1 - (K - i)) := by omega
  have hz : K - i = 0 ↔ i = K := by omega
  rw [hd]
  simpa only [hz] using geometric_inverse_left_row r (K - i)

/-- Every interior row in the general geometric tridiagonal inverse identity.
The center is j+1; the two neighboring columns are j and j+2. -/
theorem geometric_inverse_interior_row (r : ℝ) (i j : ℕ) :
    (1 + r ^ 2) * r ^ ((i - (j + 1)) + ((j + 1) - i)) -
      r * r ^ ((i - j) + (j - i)) -
      r * r ^ ((i - (j + 2)) + ((j + 2) - i)) =
        if i = j + 1 then 1 - r ^ 2 else 0 := by
  rcases lt_trichotomy i (j + 1) with h | h | h
  · have hne : i ≠ j + 1 := by omega
    have h0 : (i - j) + (j - i) = j - i := by omega
    have h1 : (i - (j + 1)) + ((j + 1) - i) = (j - i) + 1 := by omega
    have h2 : (i - (j + 2)) + ((j + 2) - i) = (j - i) + 2 := by omega
    rw [h0, h1, h2, if_neg hne, pow_add, pow_add]
    ring
  · subst i
    have hj : j + 2 - (j + 1) = 1 := by omega
    norm_num
    rw [hj]
    ring
  · have hne : i ≠ j + 1 := by omega
    have h0 : (i - j) + (j - i) = (i - (j + 2)) + 2 := by omega
    have h1 : (i - (j + 1)) + ((j + 1) - i) = (i - (j + 2)) + 1 := by omega
    have h2 : (i - (j + 2)) + ((j + 2) - i) = i - (j + 2) := by omega
    rw [h0, h1, h2, if_neg hne, pow_add, pow_add]
    ring

/-- A quadratic zero need not be an operator-kernel vector. -/
theorem threeTower_middle_kernel_defect (r : ℝ) :
    (∑ j : Fin 3, r ^ ((1 - j.val) + (j.val - 1)) * threeTowerCoeff r j) -
      threeTowerCoeff r ⟨1, by decide⟩ = 2 * r := by
  norm_num [threeTowerCoeff, Fin.sum_univ_succ]
  ring

/-- The sixth row of the zero-extended five-coordinate kernel vector. -/
theorem fiveTower_zero_extension_row (r : ℝ) (hr : 2 * r ^ 2 = 1) :
    (∑ j : Fin 5, r ^ (5 - j.val) * fiveTowerCoeff r j) = -r := by
  norm_num [fiveTowerCoeff, Fin.sum_univ_succ]
  linear_combination r ^ 3 * hr

def sixTowerCoeff (r ε : ℝ) (i : Fin 6) : ℝ :=
  if i.val = 0 then 1
  else if i.val = 1 then r
  else if i.val = 3 then -r
  else if i.val = 4 then -1
  else if i.val = 5 then ε
  else 0

/-- Padding the finite kernel and perturbing its new boundary creates a
linear correction. No quadratic remainder is missing: the new diagonal is zero. -/
theorem fiveTower_extension_signed_correction (c r ε : ℝ)
    (hr : 2 * r ^ 2 = 1) :
    c * ((∑ i : Fin 6, (sixTowerCoeff r ε i) ^ 2) -
      (∑ i : Fin 6, sixTowerCoeff r ε i *
        (∑ j : Fin 6, r ^ ((i.val - j.val) + (j.val - i.val)) *
          sixTowerCoeff r ε j))) = 2 * c * r * ε := by
  have hr2 : r ^ 2 = (1 / 2 : ℝ) := by linarith
  have hr3 : r ^ 3 = r / 2 := by
    calc
      r ^ 3 = r * r ^ 2 := by ring
      _ = r / 2 := by rw [hr2]; ring
  have hr4 : r ^ 4 = (1 / 4 : ℝ) := by
    calc
      r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ = 1 / 4 := by rw [hr2]; norm_num
  have hr5 : r ^ 5 = r / 4 := by
    calc
      r ^ 5 = r * r ^ 4 := by ring
      _ = r / 4 := by rw [hr4]; ring
  norm_num [sixTowerCoeff, Fin.sum_univ_succ]
  ring_nf
  simp only [hr2, hr3, hr4, hr5]
  ring

end RiemannResearch.Analysis.PrimeTowerQuadratic
