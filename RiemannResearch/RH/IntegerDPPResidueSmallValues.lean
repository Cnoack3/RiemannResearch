import RiemannResearch.RH.IntegerDPPResidueProbability
import RiemannResearch.RH.ResidueSmallGram
import RiemannResearch.RH.ParetoProgressionCalculus

/-!
# Exact first and second residue-class occupation probabilities

Source: user-provided exact Gram and DPP calculation, 21 September 2026.
These results specialize the actual probability, rather than defining a
separate algebraic proxy. Positivity of the complete arithmetic Gram
determinant justifies the second-rank denominator. No numerical approximation
or unresolved arithmetic hypothesis is used.
-/

noncomputable section
open scoped BigOperators Classical
namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization CoefficientStabilization.TailCapacity
open HistoricalTargets

theorem fullCapacity_one_exact : fullCapacity 1 = 1 / Real.log 2 := by
  have he : anchoredEvaluationCLM 1 (residueMode 0) =
      1 / Real.sqrt (Real.log 2) := by
    rw [residueMode_zero, map_smul, residueAtom_evaluation]
    norm_num
  rw [fullCapacity_eq_mode_evaluation_sum]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Finset.univ_eq_empty, Finset.sum_empty,
    add_zero, he, div_pow, one_pow, Real.sq_sqrt (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le]

theorem fullCapacity_two_entries :
    fullCapacity 2 =
      ((fullGram 2) 1 1 / 4 - (fullGram 2) 0 1 / 3 +
        (fullGram 2) 0 0 / 9) / (fullGram 2).det := by
  have hs : (fullGram 2) 1 0 = (fullGram 2) 0 1 := by
    exact real_inner_comm (residueAtom 0) (residueAtom 1)
  rw [fullCapacity_eq_inverseGram, Matrix.inv_def,
    Ring.inverse_eq_inv, Matrix.adjugate_fin_two]
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    reciprocalSource, Matrix.smul_apply, smul_eq_mul, hs]
  ring



theorem qN_one : qN 1 = 1 := by
  rw [qN_eq_fullCapacity, fullCapacity_one_exact]
  norm_num [residueModulus, progressionWeight_two_one, ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

theorem qN_two :
    qN 2 =
      let x := Real.log 2
      let y := Real.log 3
      let t := Real.pi / Real.sqrt 3
      2 * (2*x+t) * (3*y-3*x+t) /
        (12*t*(x+y) - 9*(2*x-y)^2 - 4*t^2) := by
  dsimp only
  have h00 : (fullGram 2) 0 0 = Real.log 2 / 4 := by
    change inner ℝ (residueAtom 0) (residueAtom 0) = _
    rw [real_inner_self_eq_norm_sq, residueAtom_zero_norm_sq]
  have h01 : (fullGram 2) 0 1 =
      Real.log 2 / 6 + Real.log 3 / 12 - Real.pi / (18 * Real.sqrt 3) :=
    residueAtom_inner_zero_one
  have h10 : (fullGram 2) 1 0 = (fullGram 2) 0 1 :=
    real_inner_comm (residueAtom 0) (residueAtom 1)
  have h11 : (fullGram 2) 1 1 =
      2 * Real.log 3 / 9 - Real.pi / (27 * Real.sqrt 3) := by
    change inner ℝ (residueAtom 1) (residueAtom 1) = _
    rw [real_inner_self_eq_norm_sq, residueAtom_one_norm_sq]
  let D := 12*(Real.pi / Real.sqrt 3)*(Real.log 2+Real.log 3) -
    9*(2*Real.log 2-Real.log 3)^2 - 4*(Real.pi / Real.sqrt 3)^2
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hd : (fullGram 2).det = D / 1296 := by
    rw [Matrix.det_fin_two, h10, h00, h01, h11]
    dsimp [D]
    field_simp
    ring
  have hD : D ≠ 0 := by
    intro h
    have hp := fullGram_det_pos 2
    rw [hd, h] at hp
    norm_num at hp
  rw [qN_eq_fullCapacity]
  norm_num only [residueModulus, Nat.lcm]
  rw [progressionWeight_six_one, fullCapacity_two_entries, hd, h00, h01, h11]
  change _ = 2 * (2*Real.log 2+Real.pi / Real.sqrt 3) *
    (3*Real.log 3-3*Real.log 2+Real.pi / Real.sqrt 3) / D
  field_simp
  ring

end RiemannResearch.RH.Pareto.IntegerDPP
