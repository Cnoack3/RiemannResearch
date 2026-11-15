/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QMatchedFiniteProjection
import Mathlib.Tactic.Ring

/-!
# Actual full-head repair from the certified rational head matrices

Source: the reciprocal-head investigation, 7 November 2026, Section 5.
The finite certificates provide literal identities Ainv*A=I and A*H=D*A.
These identities imply that the computed physical repair is the unique stage
vector with its head, and therefore both constrained minima coincide with it.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QMatchedFiniteProjection
open ZetaTwoHilbert
open RiemannResearch.Analysis.FiniteHilbertGram

def physicalHeadMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ArithmeticCumulative.residueFraction (j.val + 2) (i.val + 1)

def reciprocalHeadDiagonal (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i => 1 / ((i.val : ℝ) + 2))

theorem physicalHead_synthesis (N : ℕ) (c : Fin N → ℝ) (i : Fin N) :
    qSequence (Fintype.linearCombination ℝ (qDictionary N) c) (i.val + 1) =
      (physicalHeadMatrix N).mulVec c i := by
  rw [qSequence_synthesis]
  unfold Matrix.mulVec dotProduct physicalHeadMatrix
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem reciprocalTarget_head_matrix (N : ℕ) (i : Fin N) :
    qSequence (reciprocalTarget N) (i.val + 1) =
      (reciprocalHeadDiagonal N).mulVec
        ((physicalHeadMatrix N).mulVec (displacementCoefficients N)) i := by
  rw [reciprocalTarget_physical]
  simp only [reciprocalHeadDiagonal, Matrix.mulVec_diagonal]
  rw [← physicalHead_synthesis N (displacementCoefficients N) i, qSequence_synthesis]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

theorem fullHead_coefficients_injective (N : ℕ)
    (Ainv : Matrix (Fin N) (Fin N) ℝ) (hinv : Ainv * physicalHeadMatrix N = 1)
    (c d : Fin N → ℝ)
    (hh : ∀ i : Fin N, qSequence (Fintype.linearCombination ℝ (qDictionary N) c) (i.val + 1) =
      qSequence (Fintype.linearCombination ℝ (qDictionary N) d) (i.val + 1)) : c = d := by
  have he : (physicalHeadMatrix N).mulVec c = (physicalHeadMatrix N).mulVec d := by
    funext i
    simpa only [physicalHead_synthesis] using hh i
  have h := congrArg (fun v => Ainv.mulVec v) he
  simpa only [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] using h

def fullHeadRepairCoefficients (N : ℕ) (H : Matrix (Fin N) (Fin N) ℝ) : Fin N → ℝ :=
  H.mulVec (displacementCoefficients N)

def fullHeadRepair (N : ℕ) (H : Matrix (Fin N) (Fin N) ℝ) : QHilbert :=
  Fintype.linearCombination ℝ (qDictionary N) (fullHeadRepairCoefficients N H)

theorem fullHeadRepair_head (N : ℕ) (H : Matrix (Fin N) (Fin N) ℝ)
    (hH : physicalHeadMatrix N * H = reciprocalHeadDiagonal N * physicalHeadMatrix N)
    (i : Fin N) : qSequence (fullHeadRepair N H) (i.val + 1) =
      qSequence (reciprocalTarget N) (i.val + 1) := by
  unfold fullHeadRepair fullHeadRepairCoefficients
  rw [physicalHead_synthesis, Matrix.mulVec_mulVec, hH, ← Matrix.mulVec_mulVec,
    ← reciprocalTarget_head_matrix]

theorem trial_synthesis (N : ℕ) (F : QHilbert) (hF : F ∈ qSpace N) :
    Fintype.linearCombination ℝ (qDictionary N) (inverseCoeff (qDictionary_independent N) F) = F := by
  rw [synthesis_inverseCoeff_eq_projection]
  exact (Submodule.starProjection_eq_self_iff).mpr hF

/-- The computed full-head repair is the unique actual stage-feasible vector. -/
theorem fullHeadRepair_unique (N : ℕ)
    (Ainv H : Matrix (Fin N) (Fin N) ℝ) (hinv : Ainv * physicalHeadMatrix N = 1)
    (hH : physicalHeadMatrix N * H = reciprocalHeadDiagonal N * physicalHeadMatrix N)
    (F : QHilbert) (hF : F ∈ qSpace N)
    (hh : ∀ i : Fin N, qSequence F (i.val + 1) = qSequence (reciprocalTarget N) (i.val + 1)) :
    F = fullHeadRepair N H := by
  have hc := fullHead_coefficients_injective N Ainv hinv
    (inverseCoeff (qDictionary_independent N) F) (fullHeadRepairCoefficients N H) (by
      intro i
      rw [trial_synthesis N F hF, hh i]
      exact (fullHeadRepair_head N H hH i).symm)
  rw [← trial_synthesis N F hF, hc]
  rfl

theorem fullHeadRepair_norm_completion (N : ℕ)
    (Ainv H : Matrix (Fin N) (Fin N) ℝ) (hinv : Ainv * physicalHeadMatrix N = 1)
    (hH : physicalHeadMatrix N * H = reciprocalHeadDiagonal N * physicalHeadMatrix N)
    (F : QHilbert) (hF : F ∈ qSpace N)
    (hh : ∀ i : Fin N, qSequence F (i.val + 1) = qSequence (reciprocalTarget N) (i.val + 1)) :
    ‖F‖ ^ 2 = ‖fullHeadRepair N H‖ ^ 2 + ‖F - fullHeadRepair N H‖ ^ 2 := by
  rw [fullHeadRepair_unique N Ainv H hinv hH F hF hh]
  simp

theorem fullHeadRepair_error_completion (N : ℕ)
    (Ainv H : Matrix (Fin N) (Fin N) ℝ) (hinv : Ainv * physicalHeadMatrix N = 1)
    (hH : physicalHeadMatrix N * H = reciprocalHeadDiagonal N * physicalHeadMatrix N)
    (F : QHilbert) (hF : F ∈ qSpace N)
    (hh : ∀ i : Fin N, qSequence F (i.val + 1) = qSequence (reciprocalTarget N) (i.val + 1)) :
    ‖reciprocalTarget N - F‖ ^ 2 = ‖reciprocalTarget N - fullHeadRepair N H‖ ^ 2 +
      ‖F - fullHeadRepair N H‖ ^ 2 := by
  rw [fullHeadRepair_unique N Ainv H hinv hH F hF hh]
  simp

end RiemannResearch.RH.QMatchedFiniteProjection
