/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeHeadBoundary
import RiemannResearch.RH.SquarefreeMobiusProjection
import RiemannResearch.RH.MobiusDifferenceCLM
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Linarith
import RiemannResearch.RH.QSquarefreeEvaluationBasis
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QSquarefreeSmoothedProjection
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

open ZetaTwoHilbert ZetaTwoOptimizerStage ZetaTwoParetoTransfer
open Pareto Pareto.CoefficientStabilization SquarefreeMobiusProjection
open QSquarefreeHeadBoundary QSquarefreeHeadPrediction
open QSquarefreeEvaluationBasis QSquarefreeTailResponse

/-- At a physical onset, the Möbius coefficient is minus the onset value. -/
private theorem coefficient_eq_neg_onset (f : QHilbert) (m : ℕ) (hm : 0 < m)
    (hf : ∀ n : ℕ, n < m → qSequence f n = 0) :
    qCoefficientCLM m f = -qSequence f m := by
  change -mobiusDifferenceCLM m (toPareto f) = _
  simp only [mobiusDifferenceCLM_apply, toPareto_sequence, mobiusDifference]
  congr 1
  rw [Finset.sum_eq_single m]
  · simp [Nat.div_self hm, hf (m - 1) (by omega)]
  · intro d hd hdm
    have hdle : d ≤ m := Nat.le_of_dvd hm (Nat.dvd_of_mem_divisors hd)
    have hdp : 0 < d := Nat.pos_of_mem_divisors hd
    rw [hf d (by omega), hf (d - 1) (by omega), sub_self, mul_zero]
  · intro hnot
    simp [Nat.mem_divisors, ne_of_gt hm] at hnot

/-- The actual ordered basis has no nonzero nonsquarefree physical pivot. -/
theorem orderedVector_eq_zero_of_nonsquarefree (N : ℕ) (i : Fin (N + 1))
    (hi : 1 < i.val + 1) (hs : ¬Squarefree (i.val + 1)) :
    orderedVector N i = 0 := by
  have he : (i.val + 1) - 2 + 2 = i.val + 1 := by omega
  have hc := omitted_coordinate_zero_of_mem_stage N (orderedVector N i)
    (orderedVector_mem_stage N i) ((i.val + 1) - 2) (by simpa only [he] using hs)
  rw [he, coefficient_eq_neg_onset _ _ (by omega)
    (orderedVector_physical_zero N i)] at hc
  have hp : qSequence (orderedVector N i) (i.val + 1) = 0 := neg_eq_zero.mp hc
  have ht : orderedVector N i ∈ tailStage N (i.val + 1) := by
    refine ⟨orderedVector_mem_stage N i, ?_⟩
    apply mem_headNull_of_physical_zero
    intro n hn
    rcases lt_or_eq_of_le hn with hlt | rfl
    · exact orderedVector_physical_zero N i n hlt
    · exact hp
  have hh := orderedVector_mem_headKernelSpace N (i.val + 1) i (by omega)
  rw [headKernelSpace_eq] at hh
  have hz := Submodule.inner_right_of_mem_orthogonal ht hh.2
  have hnorm : ‖orderedVector N i‖ ^ 2 = 0 := by
    simpa only [real_inner_self_eq_norm_sq] using hz
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (orderedVector N i)])

end RiemannResearch.RH.QSquarefreeResponseBasis
