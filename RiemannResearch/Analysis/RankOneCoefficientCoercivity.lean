/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteGramCoercivity
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rank-one coefficient coercivity and exact inverse-Gram deficits

Source: the leading-slope square retained in
SquarefreeShortHeadSchurResearch20261030.md, Proposition 1.
Keeping that square gives the coefficient metric I + 11^T and the explicit
dual subtraction (sum b)^2/(card + 1). The exact inverse deficit retains both
a coefficient square and the full coercivity slack before taking an estimate.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.RankOneCoefficientCoercivity
variable {ι : Type*} [Fintype ι]

def coefficientEnergy (a : ι → ℝ) : ℝ :=
  (∑ i, a i ^ 2) + (∑ i, a i) ^ 2

def coefficientPairing (a b : ι → ℝ) : ℝ :=
  (∑ i, a i * b i) + (∑ i, a i) * (∑ i, b i)

def centeredDual (x : ι → ℝ) (i : ι) : ℝ :=
  x i - (∑ j, x j) / ((Fintype.card ι : ℝ) + 1)

def dualEnergy (x : ι → ℝ) : ℝ :=
  (∑ i, x i ^ 2) - (∑ i, x i) ^ 2 / ((Fintype.card ι : ℝ) + 1)

theorem coefficientEnergy_nonneg (a : ι → ℝ) : 0 ≤ coefficientEnergy a :=
  add_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _)

theorem sum_centeredDual (x : ι → ℝ) :
    (∑ i, centeredDual x i) =
      (∑ i, x i) / ((Fintype.card ι : ℝ) + 1) := by
  have hk : (Fintype.card ι : ℝ) + 1 ≠ 0 := by positivity
  simp only [centeredDual, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp [hk]
  ring

theorem centeredDual_pairing (x a : ι → ℝ) :
    coefficientPairing (centeredDual x) a = ∑ i, x i * a i := by
  unfold coefficientPairing
  rw [sum_centeredDual]
  simp only [centeredDual, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem centeredDual_energy (x : ι → ℝ) :
    coefficientEnergy (centeredDual x) = dualEnergy x := by
  have hk : (Fintype.card ι : ℝ) + 1 ≠ 0 := by positivity
  unfold coefficientEnergy dualEnergy
  rw [sum_centeredDual]
  have he (i : ι) :
      centeredDual x i ^ 2 =
        x i ^ 2 - 2 * ((∑ j, x j) / ((Fintype.card ι : ℝ) + 1)) * x i +
          ((∑ j, x j) / ((Fintype.card ι : ℝ) + 1)) ^ 2 := by
    unfold centeredDual
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hk]
  ring

theorem dualEnergy_nonneg (x : ι → ℝ) : 0 ≤ dualEnergy x := by
  rw [← centeredDual_energy]
  exact coefficientEnergy_nonneg _

theorem dualEnergy_le_sum_sq (x : ι → ℝ) :
    dualEnergy x ≤ ∑ i, x i ^ 2 := by
  unfold dualEnergy
  exact sub_le_self _ (by positivity)

/-- Complete square expansion in the coefficient metric I+11ᵀ. -/
theorem coefficientEnergy_completion (x a : ι → ℝ) (C : ℝ) :
    coefficientEnergy (fun i => C * x i - a i) =
      C ^ 2 * coefficientEnergy x -
        2 * C * coefficientPairing x a + coefficientEnergy a := by
  have he (i : ι) : (C * x i - a i) ^ 2 =
      C ^ 2 * x i ^ 2 - 2 * C * (x i * a i) + a i ^ 2 := by ring
  simp only [coefficientEnergy, coefficientPairing, he,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Exact inverse-action deficit. The first term is the square-completion
remainder; the second is precisely the available coefficient-coercivity slack. -/
theorem inverse_action_deficit (x a : ι → ℝ) (C : ℝ) :
    C * (C * dualEnergy x - ∑ i, x i * a i) =
      coefficientEnergy (fun i => C * centeredDual x i - a i) +
        (C * (∑ i, x i * a i) - coefficientEnergy a) := by
  rw [coefficientEnergy_completion, centeredDual_energy, centeredDual_pairing]
  ring

/-- Retaining the leading slope square improves the inverse bound by the
explicit rank-one term (sum x)^2/(card+1). -/
theorem inverse_action_le (x a : ι → ℝ) (C : ℝ) (hC : 0 < C)
    (hbudget : coefficientEnergy a ≤ C * (∑ i, x i * a i)) :
    (∑ i, x i * a i) ≤ C * dualEnergy x := by
  have hdef := inverse_action_deficit x a C
  have hnonneg : 0 ≤ C * (C * dualEnergy x - ∑ i, x i * a i) := by
    rw [hdef]
    exact add_nonneg (coefficientEnergy_nonneg _) (sub_nonneg.mpr hbudget)
  by_contra hbad
  have hp := mul_pos hC (sub_pos.mpr (lt_of_not_ge hbad))
  nlinarith

end RiemannResearch.Analysis.RankOneCoefficientCoercivity

namespace RiemannResearch.Analysis.FiniteGramCoercivity
open FiniteHilbertGram FiniteGramCapacity RankOneCoefficientCoercivity

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem linearIndependent_of_rankOne_coercive (v : ι → E) (C : ℝ)
    (hc : ∀ a : ι → ℝ,
      coefficientEnergy a ≤ C * ‖Fintype.linearCombination ℝ v a‖ ^ 2) :
    LinearIndependent ℝ v := by
  apply linearIndependent_of_coercive v C
  intro a
  exact (le_add_of_nonneg_right (sq_nonneg (∑ i, a i))).trans (hc a)

/-- Exact Gram inverse deficit retaining both the centered coefficient square
and the original leading-slope coercivity slack. -/
theorem inverse_rankOne_deficit {v : ι → E}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) (C : ℝ) :
    C * (C * dualEnergy b - capacity hv b) =
      coefficientEnergy (fun i => C * centeredDual b i - inverseSource hv b i) +
        (C * ‖Fintype.linearCombination ℝ v (inverseSource hv b)‖ ^ 2 -
          coefficientEnergy (inverseSource hv b)) := by
  have hdot : (∑ i, b i * inverseSource hv b i) = capacity hv b := by
    unfold capacity
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [inverseSource_synthesis_energy]
  simpa only [hdot] using inverse_action_deficit b (inverseSource hv b) C

theorem capacity_le_of_rankOne_coercive {v : ι → E}
    (hv : LinearIndependent ℝ v) (C : ℝ) (hC : 0 < C)
    (hc : ∀ a : ι → ℝ,
      coefficientEnergy a ≤ C * ‖Fintype.linearCombination ℝ v a‖ ^ 2)
    (b : ι → ℝ) :
    capacity hv b ≤ C * dualEnergy b := by
  have hdot : (∑ i, b i * inverseSource hv b i) = capacity hv b := by
    unfold capacity
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hbudget := hc (inverseSource hv b)
  rw [inverseSource_synthesis_energy, ← hdot] at hbudget
  simpa only [hdot] using inverse_action_le b (inverseSource hv b) C hC hbudget

/-- The inverse of the complete actual Gram has the rank-one subtraction. -/
theorem inverseGram_rankOne_quadratic_le [DecidableEq ι] {v : ι → E}
    (hv : LinearIndependent ℝ v) (C : ℝ) (hC : 0 < C)
    (hc : ∀ a : ι → ℝ,
      coefficientEnergy a ≤ C * ‖Fintype.linearCombination ℝ v a‖ ^ 2)
    (b : ι → ℝ) :
    dotProduct b ((gramMatrix v)⁻¹.mulVec b) ≤
      C * ((∑ i, b i ^ 2) -
        (∑ i, b i) ^ 2 / ((Fintype.card ι : ℝ) + 1)) := by
  calc
    _ = capacity hv b := by
      rw [gramMatrix_inverseSource hv]
      unfold dotProduct capacity
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    _ ≤ _ := capacity_le_of_rankOne_coercive hv C hC hc b

end RiemannResearch.Analysis.FiniteGramCoercivity
