/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeEvaluationBasis
import RiemannResearch.RH.QSquarefreeHeadPrediction
import RiemannResearch.RH.QSquarefreeTailResponse
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Lean.Elab.Tactic.Omega

/-!
# The ordered basis realizes the exact head/tail response split

Source: user-provided Head Boundary / Tail Response handoff, R2.
The basis coefficients keep their signs and use complete Hilbert norms.
This identifies the existing minimum-norm head extension, without claiming
that its physical reconstruction is uniformly bounded.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeResponseBasis
open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeSmoothedProjection
open QSquarefreeCorrectionKernel QSquarefreeTailResponse
open QSquarefreeEvaluationBasis QSquarefreeHeadPrediction
open InnerProductSpace

theorem orderedVector_mem_headKernelSpace (N H : ℕ) (i : Fin (N + 1))
    (hi : i.val < H) : orderedVector N i ∈ headKernelSpace N H := by
  change ‖innovation N i‖⁻¹ • innovation N i ∈ _
  apply Submodule.smul_mem
  have hs : Submodule.span ℝ (evaluationFamily N '' Set.Iic i) ≤
      headKernelSpace N H := by
    apply Submodule.span_le.mpr
    rintro x ⟨j, hj, rfl⟩
    have hjH : j.val < H := lt_of_le_of_lt (show j.val ≤ i.val from hj) hi
    exact kernel_mem_headKernelSpace N H ⟨j.val, hjH⟩
  exact hs (gramSchmidt_mem_span ℝ (evaluationFamily N) (le_refl i))

theorem orderedVector_mem_tailStage (N H : ℕ) (i : Fin (N + 1))
    (hi : H ≤ i.val) : orderedVector N i ∈ tailStage N H := by
  refine ⟨orderedVector_mem_stage N i, ?_⟩
  intro n hn
  exact orderedVector_onset N i n (lt_of_lt_of_le hn hi)

theorem low_coefficient_zero_of_tailStage (N H : ℕ) (f : QHilbert)
    (hf : f ∈ tailStage N H) (i : Fin (N + 1)) (hi : i.val < H) :
    inner ℝ f (orderedVector N i) = 0 := by
  have hu := orderedVector_mem_headKernelSpace N H i hi
  rw [headKernelSpace_eq] at hu
  exact Submodule.inner_right_of_mem_orthogonal hf hu.2

theorem high_coefficient_zero_of_headKernelSpace (N H : ℕ) (f : QHilbert)
    (hf : f ∈ headKernelSpace N H) (i : Fin (N + 1)) (hi : H ≤ i.val) :
    inner ℝ f (orderedVector N i) = 0 := by
  rw [headKernelSpace_eq] at hf
  rw [real_inner_comm]
  exact Submodule.inner_right_of_mem_orthogonal
    (orderedVector_mem_tailStage N H i hi) hf.2

theorem headResponse_coefficient (N H : ℕ) (i : Fin (N + 1)) :
    inner ℝ (headResponse N H) (orderedVector N i) =
      if i.val < H then inner ℝ (movingCorrection N) (orderedVector N i) else 0 := by
  by_cases hi : i.val < H
  · rw [if_pos hi, headResponse, inner_sub_left,
      low_coefficient_zero_of_tailStage N H _ (tailResponse_mem N H) i hi, sub_zero]
  · rw [if_neg hi]
    exact high_coefficient_zero_of_headKernelSpace N H _
      (headResponse_mem_headKernelSpace N H) i (by omega)

theorem tailResponse_coefficient (N H : ℕ) (i : Fin (N + 1)) :
    inner ℝ (tailResponse N H) (orderedVector N i) =
      if H ≤ i.val then inner ℝ (movingCorrection N) (orderedVector N i) else 0 := by
  by_cases hi : H ≤ i.val
  · rw [if_pos hi]
    have h := congrArg (fun f : QHilbert => inner ℝ f (orderedVector N i))
      (response_split N H)
    rw [inner_add_left,
      high_coefficient_zero_of_headKernelSpace N H _
        (headResponse_mem_headKernelSpace N H) i hi, zero_add] at h
    exact h.symm
  · rw [if_neg hi]
    exact low_coefficient_zero_of_tailStage N H _ (tailResponse_mem N H) i (by omega)

/-- The actual minimum-norm head extension is exactly the low-onset synthesis. -/
theorem headResponse_synthesis (N H : ℕ) :
    headResponse N H = ∑ i : Fin (N + 1),
      if i.val < H then
        inner ℝ (movingCorrection N) (orderedVector N i) • orderedVector N i
      else 0 := by
  conv_lhs => rw [stage_synthesis N _ (headResponse_mem_stage N H)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [headResponse_coefficient]
  split_ifs <;> simp

/-- The already controlled complete-tail response is the high-onset synthesis. -/
theorem tailResponse_synthesis (N H : ℕ) :
    tailResponse N H = ∑ i : Fin (N + 1),
      if H ≤ i.val then
        inner ℝ (movingCorrection N) (orderedVector N i) • orderedVector N i
      else 0 := by
  conv_lhs => rw [stage_synthesis N _ (tailResponse_mem N H).1]
  apply Finset.sum_congr rfl
  intro i hi
  rw [tailResponse_coefficient]
  split_ifs <;> simp

end RiemannResearch.RH.QSquarefreeResponseBasis
