/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QCRTIndicatorClosure
import RiemannResearch.RH.SquarefreeMobiusProjection
import RiemannResearch.RH.MobiusDifferenceCLM
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.ParetoResidueDuality
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# A concrete failure of multiplicative closure for squarefree legal indicators

Source: the user's CRT indicator discussion, 25 October 2026.
The legal indicator of residues 2,4,5 modulo 6 and the legal odd indicator
have an intersection indicator outside the closed squarefree span.
The omitted conductor 25 coordinate certifies this, independently of RH.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTIndicatorProduct
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open QCRTIndicatorClosure SquarefreeMobiusProjection

def sixIntersectionSequence (n : ℕ) : ℝ := if n % 6 = 5 then 1 else 0

private theorem sixIntersection_square_summable :
    Summable (fun n => positiveQWeight n * (sixIntersectionSequence n)^2) := by
  apply boundedQ_square_summable sixIntersectionSequence 1 zero_le_one
  intro n
  by_cases hn : n % 6 = 5 <;> simp [sixIntersectionSequence, hn]

def sixIntersectionIndicator : QHilbert :=
  encodeQ sixIntersectionSequence sixIntersection_square_summable

@[simp] theorem sixIntersectionIndicator_sequence :
    qSequence sixIntersectionIndicator = sixIntersectionSequence :=
  qSequence_encodeQ _ _ (by norm_num [sixIntersectionSequence])

/-- The odd indicator is already the squarefree legal vector 2*g₂. -/
theorem oddIndicator_mem_closure :
    (2 : ℝ) • qResidue 2 ∈ ZetaTwoOptimizerStage.closure := by
  rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
  apply qSquarefreeCRTSpan.le_topologicalClosure
  apply qSquarefreeCRTSpan.smul_mem
  exact Submodule.subset_span ⟨⟨2, by decide, Nat.prime_two.squarefree⟩, rfl⟩

/-- The product is encoded in QHilbert and is exactly the residue-5 indicator. -/
theorem sixIntersectionIndicator_is_product (n : ℕ) :
    qSequence sixIntersectionIndicator n =
      qSequence sixCarryIndicator n * qSequence ((2 : ℝ) • qResidue 2) n := by
  have ho : qSequence ((2 : ℝ) • qResidue 2) n = 2 * residueFraction 2 n := by
    change qSequenceLinear ((2 : ℝ) • qResidue 2) n = _
    rw [map_smul]
    change 2 * qSequence (qResidue 2) n = _
    rw [qSequence_qResidue]
  rw [sixIntersectionIndicator_sequence, sixCarryIndicator_sequence, ho]
  unfold sixIntersectionSequence residueFraction
  have h2 : n % 2 = (n % 6) % 2 := by omega
  rw [h2]
  have hr : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨
      n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
  rcases hr with h | h | h | h | h | h <;> norm_num [h]

theorem sixIntersectionIndicator_coordinate25 :
    qCoefficientCLM 25 sixIntersectionIndicator = 1 := by
  change -Pareto.mobiusDifferenceCLM 25
    (ZetaTwoParetoTransfer.toPareto sixIntersectionIndicator) = 1
  rw [Pareto.mobiusDifferenceCLM_apply, ZetaTwoParetoTransfer.toPareto_sequence]
  have hd : (25 : ℕ).divisors = {1, 5, 25} := by decide
  have hm5 : ArithmeticFunction.moebius 5 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  norm_num [Pareto.mobiusDifference, hd, sixIntersectionIndicator_sequence,
    sixIntersectionSequence, hm5, ArithmeticFunction.moebius_apply_one]

/-- The omitted square conductor detects the intersection indicator. -/
theorem sixIntersectionIndicator_not_mem_closure :
    sixIntersectionIndicator ∉ ZetaTwoOptimizerStage.closure := by
  have h25 : ¬Squarefree (25 : ℕ) := by
    intro h
    have hp : Squarefree ((5 : ℕ)^2) := h
    have hh := (Nat.squarefree_pow_iff (by norm_num : (5 : ℕ) ≠ 1)
      (by norm_num : (2 : ℕ) ≠ 0)).mp hp
    norm_num at hh
  intro hmem
  have hz : qCoefficientCLM 25 sixIntersectionIndicator = 0 := by
    simpa using q_omitted_coordinate_zero 23 (by simpa using h25) hmem
  rw [sixIntersectionIndicator_coordinate25] at hz
  exact one_ne_zero hz

/-- Both factors in the product counterexample are genuine indicators. -/
theorem sixCarryIndicator_binary (n : ℕ) :
    qSequence sixCarryIndicator n = 0 ∨ qSequence sixCarryIndicator n = 1 := by
  simp only [sixCarryIndicator_sequence]
  split_ifs <;> simp

theorem oddIndicator_sequence (n : ℕ) :
    qSequence ((2 : ℝ) • qResidue 2) n = if n % 2 = 1 then 1 else 0 := by
  change qSequenceLinear ((2 : ℝ) • qResidue 2) n = _
  rw [map_smul]
  change 2 * qSequence (qResidue 2) n = _
  rw [qSequence_qResidue]
  unfold residueFraction
  have hr : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hr with h | h <;> norm_num [h]

theorem oddIndicator_binary (n : ℕ) :
    qSequence ((2 : ℝ) • qResidue 2) n = 0 ∨
      qSequence ((2 : ℝ) • qResidue 2) n = 1 := by
  simp only [oddIndicator_sequence]
  split_ifs <;> simp

/-- The union of the two support sets: all positive integers not divisible by 6. -/
def sixUnionIndicator : QHilbert :=
  sixCarryIndicator + (2 : ℝ) • qResidue 2 - sixIntersectionIndicator

theorem sixUnionIndicator_sequence (n : ℕ) :
    qSequence sixUnionIndicator n = if 6 ∣ n then 0 else 1 := by
  change qSequenceLinear
    ((sixCarryIndicator + (2 : ℝ) • qResidue 2) - sixIntersectionIndicator) n = _
  rw [map_sub, map_add]
  change qSequence sixCarryIndicator n + qSequence ((2 : ℝ) • qResidue 2) n -
    qSequence sixIntersectionIndicator n = _
  rw [sixCarryIndicator_sequence, oddIndicator_sequence,
    sixIntersectionIndicator_sequence]
  unfold sixIntersectionSequence
  simp only [Nat.dvd_iff_mod_eq_zero]
  have h2 : n % 2 = (n % 6) % 2 := by omega
  rw [h2]
  have hr : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨
      n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
  rcases hr with h | h | h | h | h | h <;> norm_num [h]

/-- Unchecked union of legal CRT indicators also leaves the squarefree closure. -/
theorem sixUnionIndicator_not_mem_closure :
    sixUnionIndicator ∉ ZetaTwoOptimizerStage.closure := by
  intro hu
  apply sixIntersectionIndicator_not_mem_closure
  have hlegal := ZetaTwoOptimizerStage.closure.sub_mem
    (ZetaTwoOptimizerStage.closure.add_mem sixCarryIndicator_mem_closure
      oddIndicator_mem_closure) hu
  have he : sixCarryIndicator + (2 : ℝ) • qResidue 2 - sixUnionIndicator =
      sixIntersectionIndicator := by
    unfold sixUnionIndicator
    abel
  rwa [he] at hlegal

/-- Actual legal bounded indicators can have an illegal pointwise product. -/
theorem exists_legal_factors_with_illegal_product :
    ∃ f g h : QHilbert,
      f ∈ ZetaTwoOptimizerStage.closure ∧
      g ∈ ZetaTwoOptimizerStage.closure ∧
      (∀ n, qSequence f n = 0 ∨ qSequence f n = 1) ∧
      (∀ n, qSequence g n = 0 ∨ qSequence g n = 1) ∧
      (∀ n, qSequence h n = qSequence f n * qSequence g n) ∧
      h ∉ ZetaTwoOptimizerStage.closure := by
  exact ⟨sixCarryIndicator, (2 : ℝ) • qResidue 2, sixIntersectionIndicator,
    sixCarryIndicator_mem_closure, oddIndicator_mem_closure,
    sixCarryIndicator_binary, oddIndicator_binary,
    sixIntersectionIndicator_is_product, sixIntersectionIndicator_not_mem_closure⟩

end RiemannResearch.RH.QCRTIndicatorProduct
