/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QCRTCarry
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Legal CRT indicators and the missing exhaustion condition

Source: the user's CRT and weak compactness discussion, 25 October 2026.
The concrete residue-class indicator is an elementary CRT computation. The
exhaustion theorem is conditional on actual legal binary-valued vectors whose
complementary mass tends to zero. No such exhausting family is constructed.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QCRTIndicatorClosure
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative

/-- The positive indicator supplied by the signed two-prime CRT carry. -/
def sixCarryIndicator : QHilbert := qResidue 6 - qResidue 2 + qResidue 3

theorem sixCarryIndicator_eq_neg_carry :
    sixCarryIndicator = -QCRTCarry.qCarry 2 3 1 (-1) := by
  have h := QCRTCarry.qCarry_eq_linear 2 3 1 (-1) 0
    (by norm_num) (by norm_num) (by norm_num)
  rw [h]
  simp only [Int.cast_one, Int.cast_neg, one_smul, neg_smul]
  unfold sixCarryIndicator
  change qResidue 6 - qResidue 2 + qResidue 3 =
    -(qResidue 2 + -qResidue 3 - qResidue 6)
  abel

/-- Exact physical support: residues 2, 4 and 5 modulo 6. -/
theorem sixCarryIndicator_sequence (n : ℕ) :
    qSequence sixCarryIndicator n =
      if n % 6 = 2 ∨ n % 6 = 4 ∨ n % 6 = 5 then 1 else 0 := by
  change qSequenceLinear ((qResidue 6 - qResidue 2) + qResidue 3) n = _
  rw [map_add, map_sub]
  change qSequence (qResidue 6) n - qSequence (qResidue 2) n +
    qSequence (qResidue 3) n = _
  simp only [qSequence_qResidue]
  unfold residueFraction
  have h2 : n % 2 = (n % 6) % 2 := by omega
  have h3 : n % 3 = (n % 6) % 3 := by omega
  rw [h2, h3]
  have hr : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨
      n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
  rcases hr with h | h | h | h | h | h <;> norm_num [h]

theorem sixCarryIndicator_mem_squarefreeSpan :
    sixCarryIndicator ∈ qSquarefreeCRTSpan := by
  have hs6 : Squarefree (6 : ℕ) := by
    change Squarefree (2 * 3 : ℕ)
    exact Nat.squarefree_mul_iff.mpr
      ⟨by decide, Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
  have h6 : qResidue 6 ∈ qSquarefreeCRTSpan :=
    Submodule.subset_span ⟨⟨6, by decide, hs6⟩, rfl⟩
  have h2 : qResidue 2 ∈ qSquarefreeCRTSpan :=
    Submodule.subset_span ⟨⟨2, by decide, Nat.prime_two.squarefree⟩, rfl⟩
  have h3 : qResidue 3 ∈ qSquarefreeCRTSpan :=
    Submodule.subset_span ⟨⟨3, by decide, Nat.prime_three.squarefree⟩, rfl⟩
  exact qSquarefreeCRTSpan.add_mem (qSquarefreeCRTSpan.sub_mem h6 h2) h3

theorem sixCarryIndicator_mem_closure :
    sixCarryIndicator ∈ ZetaTwoOptimizerStage.closure := by
  rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
  exact qSquarefreeCRTSpan.le_topologicalClosure sixCarryIndicator_mem_squarefreeSpan

/-- A legal indicator need not itself be the constant target. -/
theorem sixCarryIndicator_ne_one : sixCarryIndicator ≠ qOne := by
  intro h
  have hs := sixCarryIndicator_sequence 6
  rw [h, qSequence_qOne] at hs
  norm_num [qOneSequence] at hs

/-- The Q norm squared of a binary physical vector is its Q mass. -/
theorem binary_norm_sq_eq_mean (f : QHilbert)
    (hb : ∀ k : ℕ, 0 < k → qSequence f k = 0 ∨ qSequence f k = 1) :
    ‖f‖ ^ 2 = inner ℝ qOne f := by
  rw [qNorm_weighted_sq, qInner_weighted]
  apply tsum_congr
  intro k
  by_cases hk : k = 0
  · simp [hk]
  · rw [qSequence_qOne]
    rcases hb k (Nat.pos_of_ne_zero hk) with h | h <;>
      simp [qOneSequence, hk, h]

/-- The complete error of a legal indicator is exactly its missing mass. -/
theorem binary_error_eq_complement_mass (f : QHilbert)
    (hb : ∀ k : ℕ, 0 < k → qSequence f k = 0 ∨ qSequence f k = 1) :
    ‖qOne - f‖ ^ 2 = 1 - inner ℝ qOne f := by
  have hc : inner ℝ f qOne = inner ℝ qOne f := real_inner_comm _ _
  have hn := binary_norm_sq_eq_mean f hb
  rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_sub_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    qOne_norm_sq, hc, hn]
  ring

/-- Conditional exhaustion: binary legal vectors with vanishing missing Q mass
force target membership. Existence of the family and its mass limit is not asserted. -/
theorem one_mem_closure_of_binary_complement_tendsto_zero (F : ℕ → QHilbert)
    (hlegal : ∀ M, F M ∈ ZetaTwoOptimizerStage.closure)
    (hbinary : ∀ M k : ℕ, 0 < k → qSequence (F M) k = 0 ∨ qSequence (F M) k = 1)
    (hmass : Tendsto (fun M => 1 - inner ℝ qOne (F M)) atTop (𝓝 0)) :
    qOne ∈ ZetaTwoOptimizerStage.closure := by
  have herr : Tendsto (fun M => ‖qOne - F M‖ ^ 2) atTop (𝓝 0) := by
    convert hmass using 1
    ext M
    exact binary_error_eq_complement_mass (F M) (hbinary M)
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp herr
  have hnorm : Tendsto (fun M => ‖qOne - F M‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero]
      using hsqrt
  have hz : Tendsto (fun M => qOne - F M) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hlim : Tendsto F atTop (𝓝 qOne) := by
    have h : Tendsto (fun M => qOne - (qOne - F M)) atTop (𝓝 (qOne - 0)) :=
      tendsto_const_nhds.sub hz
    simpa using h
  have hclosed : IsClosed (ZetaTwoOptimizerStage.closure : Set QHilbert) :=
    (Submodule.span ℝ (Set.range ZetaTwoOptimizerStage.squarefreeAtom)).isClosed_topologicalClosure
  exact hclosed.mem_of_tendsto hlim (Eventually.of_forall hlegal)

theorem one_mem_closure_of_binary_mean_tendsto_one (F : ℕ → QHilbert)
    (hlegal : ∀ M, F M ∈ ZetaTwoOptimizerStage.closure)
    (hbinary : ∀ M k : ℕ, 0 < k → qSequence (F M) k = 0 ∨ qSequence (F M) k = 1)
    (hmass : Tendsto (fun M => inner ℝ qOne (F M)) atTop (𝓝 1)) :
    qOne ∈ ZetaTwoOptimizerStage.closure := by
  apply one_mem_closure_of_binary_complement_tendsto_zero F hlegal hbinary
  have h : Tendsto (fun M => (1 : ℝ) - inner ℝ qOne (F M)) atTop (𝓝 (1 - 1)) :=
    tendsto_const_nhds.sub hmass
  simpa using h

end RiemannResearch.RH.QCRTIndicatorClosure
