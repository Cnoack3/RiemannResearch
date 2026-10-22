/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QResidueConditional
import RiemannResearch.RH.QSquarefreeJumpApplications
import RiemannResearch.RH.ZetaTwoCRTReciprocalEnergy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Modulus-three conditioning does not preserve the legal squarefree closure

Source: user-directed CRT/profinite continuation, 20 October 2026.
The target is the actual complete-Q conditional image of the legal atom g_2.
Its four-site jump defect is strictly positive. Unlike the previously studied
parity image of g_6, this conditional image is unconditionally outside the
closed squarefree legal span. All progression masses include the infinite tail.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QModThreeConditionalObstruction
open ZetaTwoProbability ZetaTwoHilbert ArithmeticCumulative
open QResidueConditional QSquarefreeJumpDistance QDivisorLegality SquarefreeRadicalDifference

def massOne : ℝ := residuePowerWeight 0 3 1
def massTwo : ℝ := residuePowerWeight 0 3 2

theorem massOne_pos : 0 < massOne :=
  residuePowerWeight_pos 0 (by norm_num) (by norm_num)

theorem massTwo_pos : 0 < massTwo :=
  residuePowerWeight_pos 0 (by norm_num) (by norm_num)

theorem mass_sum : massOne + massTwo = 8 / 9 := by
  have h := residuePowerWeight_refine 1 3 1 (by decide) (by decide) (by decide)
  norm_num [Fin.sum_univ_succ] at h
  have h1 := residuePowerWeight_zeroClass 1
  have h3 := residuePowerWeight_zeroClass 3
  norm_num at h1 h3
  rw [h1, h3] at h
  change 1 = massOne + (massTwo + 1 / 9) at h
  linarith

theorem massTwo_le_quarter : massTwo ≤ 1 / 4 := by
  have h := residueSquareWeight_upper
    (L := (3 : ℝ)) (a := (2 : ℝ)) (by norm_num) (by norm_num)
  norm_num at h
  exact h

theorem massTwo_lt_massOne : massTwo < massOne := by
  linarith [mass_sum, massTwo_le_quarter]

/-- Scaling both progression anchor and period by two divides its mass by four. -/
theorem residueSquareWeight_double (L a : ℝ) :
    residuePowerWeight 0 (2 * L) (2 * a) = residuePowerWeight 0 L a / 4 := by
  unfold residuePowerWeight
  rw [← tsum_div_const]
  apply tsum_congr
  intro j
  simp only [Nat.zero_add]
  rw [show 2 * a + (j : ℝ) * (2 * L) = 2 * (a + (j : ℝ) * L) by ring,
    mul_pow]
  norm_num
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem weight_six_four : residuePowerWeight 0 6 4 = massTwo / 4 := by
  have h := residueSquareWeight_double 3 2
  norm_num at h
  exact h

theorem weight_six_two : residuePowerWeight 0 6 2 = massOne / 4 := by
  have h := residueSquareWeight_double 3 1
  norm_num at h
  exact h

theorem refine_one : residuePowerWeight 0 6 1 + massTwo / 4 = massOne := by
  have h := residuePowerWeight_refine 3 2 1 (by decide) (by decide) (by decide)
  norm_num [Fin.sum_univ_two] at h
  rw [weight_six_four] at h
  exact h.symm

theorem refine_two : massOne / 4 + residuePowerWeight 0 6 5 = massTwo := by
  have h := residuePowerWeight_refine 3 2 2 (by decide) (by decide) (by decide)
  norm_num [Fin.sum_univ_two] at h
  rw [weight_six_two] at h
  exact h.symm

theorem refine_zero : residuePowerWeight 0 6 3 = 1 / 12 := by
  have h := residuePowerWeight_refine 3 2 3 (by decide) (by decide) (by decide)
  norm_num [Fin.sum_univ_two] at h
  have h3 := residuePowerWeight_zeroClass 3
  have h6 := residuePowerWeight_zeroClass 6
  norm_num at h3 h6
  rw [h3, h6] at h
  linarith

theorem conditional_one : conditionalValue 3 1 (residueFraction 2) =
    1 / 2 - massTwo / (8 * massOne) := by
  have h := conditionalValue_new_residue 3 2 1 1
    (by decide) (by decide) (by decide) (by decide)
  norm_num [Fin.sum_univ_two, alpha, residueFraction] at h
  rw [h]
  change residuePowerWeight 0 6 1 / massOne * (1 / 2) = _
  have hA := ne_of_gt massOne_pos
  have hr := refine_one
  field_simp [hA]
  nlinarith

theorem conditional_two : conditionalValue 3 2 (residueFraction 2) =
    1 / 2 - massOne / (8 * massTwo) := by
  have h := conditionalValue_new_residue 3 2 1 2
    (by decide) (by decide) (by decide) (by decide)
  norm_num [Fin.sum_univ_two, alpha, residueFraction] at h
  rw [h]
  change residuePowerWeight 0 6 5 / massTwo * (1 / 2) = _
  have hB := ne_of_gt massTwo_pos
  have hr := refine_two
  field_simp [hB]
  nlinarith

theorem conditional_zero : conditionalValue 3 3 (residueFraction 2) = 3 / 8 := by
  have h := conditionalValue_new_residue 3 2 1 3
    (by decide) (by decide) (by decide) (by decide)
  norm_num [Fin.sum_univ_two, alpha, residueFraction] at h
  have h3 := residuePowerWeight_zeroClass 3
  norm_num at h3
  rw [h, refine_zero, h3]
  norm_num

/-- Reconstruct a three-class conditional function in the actual Q Hilbert space.
The squared atom is an ambient bounded vector, not a claimed legal atom. -/
def modThreeConditional (f : ℕ → ℝ) : QHilbert :=
  (conditionalValue 3 3 f) • qOne +
    ((3 / 2 : ℝ) * (4 * conditionalValue 3 1 f - conditionalValue 3 2 f -
      3 * conditionalValue 3 3 f)) • qResidue 3 +
    ((9 / 2 : ℝ) * (conditionalValue 3 2 f - 2 * conditionalValue 3 1 f +
      conditionalValue 3 3 f)) • qResidueSquare 3

theorem modThreeConditional_sequence (f : ℕ → ℝ) (n : ℕ) :
    qSequence (modThreeConditional f) n =
      conditionalValue 3 3 f * qOneSequence n +
      ((3 / 2 : ℝ) * (4 * conditionalValue 3 1 f - conditionalValue 3 2 f -
        3 * conditionalValue 3 3 f)) * residueFraction 3 n +
      ((9 / 2 : ℝ) * (conditionalValue 3 2 f - 2 * conditionalValue 3 1 f +
        conditionalValue 3 3 f)) * (residueFraction 3 n)^2 := by
  change qSequenceLinear (_ + _ + _) n = _
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change conditionalValue 3 3 f * qSequence qOne n +
    ((3 / 2 : ℝ) * (4 * conditionalValue 3 1 f - conditionalValue 3 2 f -
      3 * conditionalValue 3 3 f)) * qSequence (qResidue 3) n +
    ((9 / 2 : ℝ) * (conditionalValue 3 2 f - 2 * conditionalValue 3 1 f +
      conditionalValue 3 3 f)) * qSequence (qResidueSquare 3) n = _
  rw [qSequence_qOne, qSequence_qResidue, qResidueSquare_sequence]

theorem modThreeConditional_sequence_pos (f : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    qSequence (modThreeConditional f) n =
      if n % 3 = 0 then conditionalValue 3 3 f
      else if n % 3 = 1 then conditionalValue 3 1 f else conditionalValue 3 2 f := by
  rw [modThreeConditional_sequence]
  have hn0 := ne_of_gt hn
  have hm : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hm with hm | hm | hm
  all_goals simp [qOneSequence, hn0, residueFraction, hm] <;> ring

def modThreeTwo : QHilbert := modThreeConditional (residueFraction 2)

def defect : ℝ := (massOne - massTwo) * (massOne + 2 * massTwo) /
    (8 * massOne * massTwo)

theorem defect_pos : 0 < defect := by
  unfold defect
  exact div_pos
    (mul_pos (sub_pos.mpr massTwo_lt_massOne)
      (by have := massOne_pos; have := massTwo_pos; positivity))
    (by have := massOne_pos; have := massTwo_pos; positivity)

/-- A concrete rational separation follows from the exact total residue mass
and the previously established complete-weight upper bound. -/
theorem defect_ge_third : (1 / 3 : ℝ) ≤ defect := by
  have hratio : 0 ≤ 2 * massOne - 5 * massTwo := by
    linarith [mass_sum, massTwo_le_quarter]
  have hp : 0 ≤ (2 * massOne - 5 * massTwo) *
      ((3 / 2 : ℝ) * massOne + (5 / 4 : ℝ) * massTwo) :=
    mul_nonneg hratio (by have := massOne_pos; have := massTwo_pos; positivity)
  have hd : 0 < 8 * massOne * massTwo := by
    have := massOne_pos
    have := massTwo_pos
    positivity
  unfold defect
  apply (le_div_iff₀ hd).mpr
  nlinarith [sq_nonneg massTwo]

theorem modThreeTwo_jump : squareJumpFunctional 2 modThreeTwo = defect := by
  rw [squareJumpFunctional_apply 2 (by decide)]
  simp only [qDifference, modThreeTwo]
  change (qSequence (modThreeConditional (residueFraction 2)) 4 -
    qSequence (modThreeConditional (residueFraction 2)) 3) -
    (qSequence (modThreeConditional (residueFraction 2)) 2 -
      qSequence (modThreeConditional (residueFraction 2)) 1) = defect
  rw [modThreeConditional_sequence_pos _ 4 (by decide),
    modThreeConditional_sequence_pos _ 3 (by decide),
    modThreeConditional_sequence_pos _ 2 (by decide),
    modThreeConditional_sequence_pos _ 1 (by decide)]
  norm_num
  rw [conditional_one, conditional_two, conditional_zero]
  unfold defect
  field_simp [ne_of_gt massOne_pos, ne_of_gt massTwo_pos]
  <;> ring

/-- Exact positive separation with the complete orthogonal norm remainder. -/
theorem modThreeTwo_error_energy_exact (F : QHilbert)
    (hF : F ∈ qSquarefreeCRTSpan.topologicalClosure) :
    ‖modThreeTwo - F‖^2 = defect^2 / (30 * zetaTwo) +
      ‖modThreeTwo - F - (defect / (30 * zetaTwo)) • squareJumpWitness 2‖^2 := by
  have h := squarefree_error_energy_exact 2 (by decide) modThreeTwo F hF
  rw [modThreeTwo_jump] at h
  norm_num at h
  convert h using 1 <;> congr 2 <;> ring

theorem modThreeTwo_not_mem_closure :
    modThreeTwo ∉ qSquarefreeCRTSpan.topologicalClosure := by
  intro h
  have hz := squareJumpWitness_inner_eq_zero 2 (by decide) modThreeTwo h
  change squareJumpFunctional 2 modThreeTwo = 0 at hz
  rw [modThreeTwo_jump] at hz
  exact (ne_of_gt defect_pos) hz

theorem modThreeTwo_error_sq_lower_bound (F : QHilbert)
    (hF : F ∈ qSquarefreeCRTSpan.topologicalClosure) :
    1 / (270 * zetaTwo) ≤ ‖modThreeTwo - F‖^2 := by
  rw [modThreeTwo_error_energy_exact F hF]
  have hs : (1 / 9 : ℝ) ≤ defect^2 := by nlinarith [defect_ge_third]
  have hd : 0 < 30 * zetaTwo := by have := zetaTwo_pos; positivity
  have h := div_le_div_of_nonneg_right hs hd.le
  have he : (1 / 9 : ℝ) / (30 * zetaTwo) = 1 / (270 * zetaTwo) := by ring
  rw [he] at h
  exact h.trans (le_add_of_nonneg_right (sq_nonneg _))

/-- The input is legal, while its actual modulus-three conditional image is not. -/
theorem residue_two_legal_conditional_not :
    qResidue 2 ∈ qSquarefreeCRTSpan.topologicalClosure ∧
      modThreeConditional (qSequence (qResidue 2)) ∉ qSquarefreeCRTSpan.topologicalClosure := by
  constructor
  · apply qSquarefreeCRTSpan.le_topologicalClosure
    exact Submodule.subset_span ⟨⟨2, by decide, Nat.prime_two.squarefree⟩, rfl⟩
  · simpa only [qSequence_qResidue, modThreeTwo] using modThreeTwo_not_mem_closure

end RiemannResearch.RH.QModThreeConditionalObstruction
