/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact finite inverse-square dual block at conductors four and nine

Source: user-provided optimizer-cancellation argument, 8 October 2026.
These kernel-computable rational equalities retain the full off-diagonal
entries. `rawDGram` is the reciprocal-coordinate Gram matrix; therefore
the screened resolvent uses `rawGram + rawDGram`, not either matrix alone.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.RH.ZetaTwoProbability

def dualFour : Fin 9 → ℝ := ![1, -4, -9, 16, 0, 0, 0, 0, 0]

def dualNine : Fin 9 → ℝ := ![0, 4, -9, 0, 0, 0, 0, -64, 81]

def rawInverseSquareInner (f g : Fin 9 → ℝ) : ℝ :=
  ∑ i : Fin 9, f i * g i / (((i.val + 1 : ℕ) : ℝ) ^ 2)

def rawReciprocalInner (f g : Fin 9 → ℝ) : ℝ :=
  ∑ i : Fin 9, f i * g i / (((i.val + 1 : ℕ) : ℝ) ^ 3)

def dualPair : Fin 2 → (Fin 9 → ℝ) := ![dualFour, dualNine]

def rawGram : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => rawInverseSquareInner (dualPair i) (dualPair j)

def rawDGram : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => rawReciprocalInner (dualPair i) (dualPair j)

theorem rawGram_eq : rawGram = !![30, 5; 5, 158] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rawGram, rawInverseSquareInner, dualPair, dualFour, dualNine,
      Fin.sum_univ_succ]

theorem rawDGram_eq : rawDGram = !![10, 1; 1, 22] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rawDGram, rawReciprocalInner, dualPair, dualFour, dualNine,
      Fin.sum_univ_succ]

theorem rawGram_det : Matrix.det rawGram = 4715 := by
  rw [rawGram_eq]
  norm_num [Matrix.det_fin_two]

theorem rawGram_add_DGram_det : Matrix.det (rawGram + rawDGram) = 7164 := by
  rw [rawGram_eq, rawDGram_eq]
  norm_num [Matrix.det_fin_two]

/-- The physical fractional-part atom evaluated at the nine positive
integers supporting the dual block. -/
def finiteResidueAtom (d : ℕ) (i : Fin 9) : ℝ :=
  (((i.val + 1) % d : ℕ) : ℝ) / d

def finiteDualResidual (c₂ c₃ c₅ c₆ c₇ : ℝ) : Fin 9 → ℝ :=
  fun i => 1 - c₂ * finiteResidueAtom 2 i - c₃ * finiteResidueAtom 3 i -
    c₅ * finiteResidueAtom 5 i - c₆ * finiteResidueAtom 6 i -
    c₇ * finiteResidueAtom 7 i

/-- Exact conductor-four reciprocal row, with the optimizer coefficients
retained as arbitrary real numbers. -/
theorem dualFour_reciprocal_row (c₂ c₃ c₅ c₆ c₇ : ℝ) :
    rawReciprocalInner dualFour (finiteDualResidual c₂ c₃ c₅ c₆ c₇) =
      (5 - 4 * c₂ - c₃) / 12 := by
  norm_num [rawReciprocalInner, dualFour, finiteDualResidual, finiteResidueAtom,
    Fin.sum_univ_succ] <;> ring

/-- Exact conductor-nine reciprocal row. In particular the signed conductor
two contribution is `+8*c₂`, and all five legal channels are retained. -/
theorem dualNine_reciprocal_row (c₂ c₃ c₅ c₆ c₇ : ℝ) :
    rawReciprocalInner dualNine (finiteDualResidual c₂ c₃ c₅ c₆ c₇) =
      (11 + 8 * c₂ - 18 * c₃ - c₅ - c₆ - c₇) / 72 := by
  norm_num [rawReciprocalInner, dualNine, finiteDualResidual, finiteResidueAtom,
    Fin.sum_univ_succ] <;> ring

/-- All conductors above the dual support contribute exactly zero to the
conductor-four reciprocal row. -/
theorem dualFour_reciprocal_large_conductor (d : ℕ) (hd : 10 ≤ d) :
    rawReciprocalInner dualFour (finiteResidueAtom d) = 0 := by
  have hm (k : ℕ) (hk : k ≤ 9) : k % d = k :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt hk (lt_of_lt_of_le (by decide : 9 < 10) hd))
  norm_num [rawReciprocalInner, dualFour, finiteResidueAtom, Fin.sum_univ_succ,
    hm 1 (by decide), hm 2 (by decide), hm 3 (by decide), hm 4 (by decide),
    hm 5 (by decide), hm 6 (by decide), hm 7 (by decide), hm 8 (by decide),
    hm 9 (by decide)] <;> ring

/-- All conductors above the dual support contribute exactly zero to the
conductor-nine reciprocal row. -/
theorem dualNine_reciprocal_large_conductor (d : ℕ) (hd : 10 ≤ d) :
    rawReciprocalInner dualNine (finiteResidueAtom d) = 0 := by
  have hm (k : ℕ) (hk : k ≤ 9) : k % d = k :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt hk (lt_of_lt_of_le (by decide : 9 < 10) hd))
  norm_num [rawReciprocalInner, dualNine, finiteResidueAtom, Fin.sum_univ_succ,
    hm 1 (by decide), hm 2 (by decide), hm 3 (by decide), hm 4 (by decide),
    hm 5 (by decide), hm 6 (by decide), hm 7 (by decide), hm 8 (by decide),
    hm 9 (by decide)] <;> ring

end RiemannResearch.RH.ZetaTwoProbability
end
