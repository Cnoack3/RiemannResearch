/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteWeightedLegalProjection
import RiemannResearch.RH.SquarefreeWeightedPrimitives
import RiemannResearch.RH.QWeightedResidues
import Mathlib.Tactic.Ring
/-!
# Actual arithmetic weighted projection onto legal primitives

Source: the user's directed weighted-CRT continuation, 2 November 2026.
This application packages the existing IsLegalPrimitive predicate as a
submodule and specializes FiniteWeightedLegalProjection to the exact positive
residueWeight. A feasible reference primitive supplies the head values;
the construction allows dependent and nonsurjective observation maps, requiring
only that this reference itself be legal. No cofinal energy bound is asserted.
-/
noncomputable section
set_option maxHeartbeats 200000
namespace RiemannResearch.RH.WeightedLegalPrimitiveProjection
open ArithmeticCumulative Pareto SquarefreeWeightedPrimitives QWeightedResidues
open RiemannResearch.Analysis.FiniteWeightedRefinement
open RiemannResearch.Analysis.FiniteWeightedLegalProjection
def legalPrimitiveSpace (L : ℕ) : Submodule ℝ (Fin L → ℝ) where
  carrier := {R | IsLegalPrimitive L R}
  zero_mem' := by
    refine ⟨0, (divisorResidueSpan L).zero_mem, ?_, ?_⟩
    · simp [cumulative]
    · intro a
      simp [cumulative]
  add_mem' := by
    rintro R T ⟨g,hg,hz,hR⟩ ⟨k,hk,hz',hT⟩
    refine ⟨g+k,(divisorResidueSpan L).add_mem hg hk,?_,?_⟩
    · change cumulative (fun n => g n+k n) L = 0
      rw [cumulative_add,hz,hz',add_zero]
    · intro a
      change R a + T a = cumulative (fun n => g n+k n) a.val
      rw [cumulative_add,← hR a,← hT a]
  smul_mem' := by
    rintro c R ⟨g,hg,hz,hR⟩
    refine ⟨c • g,(divisorResidueSpan L).smul_mem c hg,?_,?_⟩
    · change cumulative (fun n => c*g n) L = 0
      rw [cumulative_mul,hz,mul_zero]
    · intro a
      change c*R a = cumulative (fun n => c*g n) a.val
      rw [cumulative_mul,← hR a]
def legalProjection (L : ℕ) (hL : 0 < L) (F : Fin L → ℝ) : Fin L → ℝ :=
  weightedProjection (residueWeight L) (residueWeight_pos L hL) (legalPrimitiveSpace L) F
theorem legalProjection_legal (L : ℕ) (hL : 0 < L) (F : Fin L → ℝ) :
    IsLegalPrimitive L (legalProjection L hL F) :=
  weightedProjection_mem (residueWeight L) (residueWeight_pos L hL)
    (legalPrimitiveSpace L) F
theorem legalProjection_completion (L : ℕ) (hL : 0 < L) (F R : Fin L → ℝ)
    (hR : IsLegalPrimitive L R) :
    energy (residueWeight L) (F-R) =
      energy (residueWeight L) (F-legalProjection L hL F) +
      energy (residueWeight L) (R-legalProjection L hL F) :=
  weightedProjection_completion (residueWeight L) (residueWeight_pos L hL)
    (legalPrimitiveSpace L) F R hR
def primitiveHeadMap (L H : ℕ) (hL : 0 < L) :
    (Fin L → ℝ) →ₗ[ℝ] (Fin H → ℝ) where
  toFun R i := R ⟨(i.val+1)%L,Nat.mod_lt _ hL⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
def constrainedLegalProjection (L H : ℕ) (hL : 0 < L) (R0 F : Fin L → ℝ) :
    Fin L → ℝ :=
  constrainedProjection (residueWeight L) (residueWeight_pos L hL)
    (legalPrimitiveSpace L) (primitiveHeadMap L H hL) R0 F
theorem constrainedLegalProjection_legal (L H : ℕ) (hL : 0 < L)
    (R0 F : Fin L → ℝ) (h0 : IsLegalPrimitive L R0) :
    IsLegalPrimitive L (constrainedLegalProjection L H hL R0 F) :=
  constrainedProjection_mem (residueWeight L) (residueWeight_pos L hL)
    (legalPrimitiveSpace L) (primitiveHeadMap L H hL) R0 F h0
theorem constrainedLegalProjection_head (L H : ℕ) (hL : 0 < L)
    (R0 F : Fin L → ℝ) :
    primitiveHeadMap L H hL (constrainedLegalProjection L H hL R0 F) =
      primitiveHeadMap L H hL R0 :=
  constrainedProjection_observation (residueWeight L) (residueWeight_pos L hL)
    (legalPrimitiveSpace L) (primitiveHeadMap L H hL) R0 F
theorem constrainedLegalProjection_completion (L H : ℕ) (hL : 0 < L)
    (R0 F R : Fin L → ℝ) (h0 : IsLegalPrimitive L R0)
    (hR : IsLegalPrimitive L R)
    (hhead : primitiveHeadMap L H hL R = primitiveHeadMap L H hL R0) :
    energy (residueWeight L) (F-R) =
      energy (residueWeight L) (F-constrainedLegalProjection L H hL R0 F) +
      energy (residueWeight L) (R-constrainedLegalProjection L H hL R0 F) :=
  constrainedProjection_completion (residueWeight L) (residueWeight_pos L hL)
    (legalPrimitiveSpace L) (primitiveHeadMap L H hL) R0 F R h0 hR hhead
end RiemannResearch.RH.WeightedLegalPrimitiveProjection
