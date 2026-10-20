/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PrimePowerTwoTargetCriterion
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.QSquarefreePeriodicJump
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Rigidity of logarithmic transforms in the enlarged squarefree closure

Source: user-provided suggestion to use powers of the logarithmic targets,
20 October 2026. The power-invariant jump relation forces every function
of `Nat.log p` in the actual enlarged closure to be affine. In particular,
a geometric transform in this closure must be constant. This obstruction
does not prove membership or nonmembership of the logarithmic target itself.
-/

noncomputable section
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert ZetaTwoProbability SquarefreeRadicalDifference QSquarefreePeriodicJump

/-- Adding constants preserves the power-invariant jump relation away from zero. -/
theorem closureWithConstants_difference_pow (a k : ℕ) (ha : 2 ≤ a) (hk : k ≠ 0)
    (x : QHilbert) (hx : x ∈ closureWithConstants) :
    qDifference x (a ^ k) = qDifference x a := by
  have hpow : 2 ≤ a ^ k := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    have hpos : 1 ≤ a ^ j :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero j (by omega))
    rw [pow_succ]
    nlinarith
  let K : Submodule ℝ QHilbert :=
    { carrier := {y | qDifference y (a ^ k) = qDifference y a}
      zero_mem' := by simp only [Set.mem_ofPred_eq, qDifference_zero]
      add_mem' := by
        intro y z hy hz
        simp only [Set.mem_ofPred_eq, qDifference_add] at *
        rw [hy, hz]
      smul_mem' := by
        intro c y hy
        simp only [Set.mem_ofPred_eq, qDifference_smul] at *
        rw [hy] }
  have hclosed : IsClosed (K : Set QHilbert) :=
    isClosed_eq (continuous_qDifference (a ^ k)) (continuous_qDifference a)
  have hH : ZetaTwoOptimizerStage.closure ≤ K := by
    change (Submodule.span ℝ
      (Set.range ZetaTwoOptimizerStage.squarefreeAtom)).topologicalClosure ≤ K
    apply (Submodule.span ℝ
      (Set.range ZetaTwoOptimizerStage.squarefreeAtom)).topologicalClosure_minimal ?_ hclosed
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    unfold ZetaTwoOptimizerStage.squarefreeAtom
    split_ifs with hi
    · exact squarefree_closure_difference_pow a k (by omega) hk _
        (qSquarefreeCRTSpan.le_topologicalClosure
          (Submodule.subset_span ⟨⟨i + 2, by omega, hi⟩, rfl⟩))
    · exact K.zero_mem
  have hOne : qOne ∈ K := by
    change qDifference qOne (a ^ k) = qDifference qOne a
    rw [qDifference_qOne _ hpow, qDifference_qOne _ ha]
  exact ((ZetaTwoOptimizerStage.closure ⊔ Submodule.span ℝ {qOne}).topologicalClosure_minimal
    (sup_le hH ((Submodule.span_singleton_le_iff_mem qOne K).2 hOne)) hclosed) hx

/-- The site immediately preceding the next base power lies in the preceding log band. -/
theorem log_pred_pow_succ (p k : ℕ) (hp : 1 < p) :
    Nat.log p (p ^ (k + 1) - 1) = k := by
  have hpos : 0 < p ^ k := pow_pos (by omega) _
  have hpow : p ^ (k + 1) = p ^ k * p := pow_succ p k
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · rw [hpow]
    have : p ^ k + 1 ≤ p ^ k * p := by nlinarith
    omega
  · have : 0 < p ^ (k + 1) := pow_pos (by omega) _
    omega

/-- Every logarithmic transform in the actual enlarged closure is affine in its log value. -/
theorem log_transform_affine_of_mem_closureWithConstants
    (p : ℕ) (hp : 1 < p) (φ : ℕ → ℝ) (x : QHilbert)
    (hseq : ∀ n : ℕ, 0 < n → qSequence x n = φ (Nat.log p n))
    (hx : x ∈ closureWithConstants) (k : ℕ) :
    φ k = φ 0 + (k : ℝ) * (φ 1 - φ 0) := by
  have hstep (j : ℕ) : φ (j + 1) - φ j = φ 1 - φ 0 := by
    have h := closureWithConstants_difference_pow p (j + 1) (by omega) (by omega) x hx
    unfold qDifference at h
    have hpj : 0 < p ^ (j + 1) := pow_pos (by omega) _
    have hpj2 : 2 ≤ p ^ (j + 1) := by
      rw [pow_succ]
      have hpos : 0 < p ^ j := pow_pos (by omega) _
      nlinarith
    rw [hseq _ hpj, hseq _ (by omega), hseq _ (by omega),
      hseq _ (by omega), Nat.log_pow hp, log_pred_pow_succ p j hp] at h
    have hlogp : Nat.log p p = 1 := by simpa using Nat.log_pow hp 1
    have hlogpred : Nat.log p (p - 1) = 0 := by
      simpa using log_pred_pow_succ p 0 hp
    simpa only [hlogp, hlogpred] using h
  induction k with
  | zero => simp
  | succ k ih =>
      have h := hstep k
      rw [Nat.cast_succ]
      linarith

/-- A geometric transform can belong to the enlarged closure only when its base is one. -/
theorem geometric_log_transform_base_eq_one
    (p : ℕ) (hp : 1 < p) (r : ℝ) (x : QHilbert)
    (hseq : ∀ n : ℕ, 0 < n → qSequence x n = r ^ Nat.log p n)
    (hx : x ∈ closureWithConstants) : r = 1 := by
  have h := log_transform_affine_of_mem_closureWithConstants p hp
    (fun k => r ^ k) x hseq hx 2
  norm_num at h
  have hz : (r - 1) * (r - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with hz | hz <;> linarith

end RiemannResearch.RH.PrimePowerTarget
