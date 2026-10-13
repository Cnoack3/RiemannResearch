import RiemannResearch.RH.ResidueSmallGram
import RiemannResearch.RH.ResidueGramDigamma
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.ResidueOrthonormalCoordinates
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact first CRT correction example

Source: user-provided CRT_Exact_Head_Tail_Proof_and_Status_2026-09-30(1).md,
the example M = 1, S = {3}. The arguments below use the complete Pareto
Gram entries, so no physical-tail truncation or uniform-residue surrogate
is introduced. The formulas use exact special-function Gram entries.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto.CRTExample
open CoefficientStabilization

def initialError : ThresholdHilbert := hilbertOne - (2 : ℝ) • residueAtom 0

def firstCorrection : ThresholdHilbert :=
  (2 / 3 : ℝ) • residueAtom 0 - residueAtom 1

private theorem target_inner_two :
    inner ℝ hilbertOne (residueAtom 0) = Real.log 2 / 2 := by
  rw [real_inner_comm]
  simpa using residueAtom_inner_one 0

private theorem target_inner_three :
    inner ℝ hilbertOne (residueAtom 1) = Real.log 3 / 3 := by
  rw [real_inner_comm]
  simpa using residueAtom_inner_one 1

private theorem pi_div_sqrt_three (c : ℝ) (hc : c ≠ 0) :
    Real.pi / (c * Real.sqrt 3) = Real.sqrt 3 * Real.pi / (3 * c) := by
  have hs : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hp0 : (Real.sqrt 3) ^ 2 * Real.pi = 3 * Real.pi := by rw [hs]
  have hp : c * (Real.sqrt 3) ^ 2 * Real.pi = 3 * c * Real.pi := by
    rw [hs]
    ring
  field_simp [hc, hs0]
  nlinarith

theorem initialError_norm_sq :
    ‖initialError‖ ^ 2 = 1 - Real.log 2 := by
  simp only [initialError, norm_sub_sq_real, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, inner_smul_right]
  rw [target_inner_two, hilbertOne_norm_sq, residueAtom_zero_norm_sq]
  ring

theorem firstCorrection_norm_sq :
    ‖firstCorrection‖ ^ 2 =
      (Real.sqrt 3 * Real.pi + 9 * Real.log (3 / 2 : ℝ)) / 81 := by
  have hlog : Real.log (3 / 2 : ℝ) = Real.log 3 - Real.log 2 :=
    Real.log_div (by norm_num) (by norm_num)
  calc
    ‖firstCorrection‖ ^ 2 =
        (Real.log 3 - Real.log 2) / 9 +
          Real.pi / (27 * Real.sqrt 3) := by
      simp only [firstCorrection, norm_sub_sq_real, norm_smul, mul_pow,
        Real.norm_eq_abs, sq_abs, real_inner_smul_left]
      rw [residueAtom_zero_norm_sq, residueAtom_one_norm_sq,
        residueAtom_inner_zero_one]
      have hs0 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
      field_simp [hs0]
      ring
    _ = _ := by
      rw [pi_div_sqrt_three 27 (by norm_num), hlog]
      ring

theorem initialError_inner_firstCorrection :
    inner ℝ initialError firstCorrection =
      (-2 * Real.sqrt 3 * Real.pi + 9 * Real.log (4 / 3 : ℝ)) / 54 := by
  have h00 : inner ℝ (residueAtom 0) (residueAtom 0) = Real.log 2 / 4 := by
    rw [real_inner_self_eq_norm_sq, residueAtom_zero_norm_sq]
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hlog : Real.log (4 / 3 : ℝ) = 2 * Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), hlog4]
  calc
    inner ℝ initialError firstCorrection =
        Real.log 2 / 3 - Real.log 3 / 6 -
          Real.pi / (9 * Real.sqrt 3) := by
      simp only [initialError, firstCorrection, inner_sub_left,
        inner_sub_right, real_inner_smul_left, inner_smul_right]
      rw [target_inner_two, target_inner_three, h00,
        residueAtom_inner_zero_one]
      have hs0 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
      field_simp [hs0]
      ring
    _ = _ := by
      rw [pi_div_sqrt_three 9 (by norm_num), hlog]
      ring

end RiemannResearch.RH.Pareto.CRTExample
