/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTNestedCutoffs
import RiemannResearch.Analysis.ScreenedCollocation
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import RiemannResearch.Analysis.FiniteAccretiveCollocation
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Actual canonical difference tests for continuous synthesis maps

Source: `CanonicalPrimePowerUpdatesResearch20261107.md`, Section 3.
Every pairing retains the entire Q measure. Physical Gram screening is
independent of the generally nonsymmetric difference-test collocation.
-/

noncomputable section
namespace RiemannResearch.RH.QCRTContinuousSynthesis
open ZetaTwoHilbert QCRTFiniteCollocation QCRTNestedCutoffs QPhysicalDifference
open RiemannResearch.Analysis.FiniteAccretiveCollocation

/-- The actual difference-test Gram has trivial kernel for an independent
physical synthesis. This is the checked shift accretivity argument, not a
quantitative coercivity estimate. -/
theorem difference_synthesis_kernel
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (U : X →L[ℝ] QHilbert) (hU : Function.Injective U) (x : X)
    (hx : (differenceCLM.comp U).adjoint (U x) = 0) : x = 0 := by
  have hi := congrArg (fun z : X => inner ℝ z x) hx
  simp only [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.comp_apply, inner_zero_left] at hi
  have hz : U x = 0 := eq_zero_of_difference_inner shiftCLM
    physicalShift_norm_le differenceCLM_injective (U x) hi
  exact hU (by simpa only [map_zero] using hz)

theorem difference_collocation_injective
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (U : X →L[ℝ] QHilbert) (hU : Function.Injective U) :
    Function.Injective ((differenceCLM.comp U).adjoint.comp U) := by
  intro x y hxy
  have hz : ((differenceCLM.comp U).adjoint.comp U) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (difference_synthesis_kernel U hU (x - y) hz)

/-- Existence of the actual finite difference-collocation inverse follows
from injectivity; no inverse-norm or RH hypothesis is needed. -/
def differenceCollocationEquiv
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [FiniteDimensional ℝ X]
    (U : X →L[ℝ] QHilbert) (hU : Function.Injective U) : X ≃ₗ[ℝ] X :=
  LinearEquiv.ofInjectiveEndo
    (((differenceCLM.comp U).adjoint.comp U).toLinearMap)
    (difference_collocation_injective U hU)

/-- Full actual block injectivity. Both cross blocks remain distinct. -/
theorem difference_block_kernel_trivial
    {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (U : X →L[ℝ] QHilbert) (W : Y →L[ℝ] QHilbert)
    (hUW : Function.Injective (fun p : X × Y => U p.1 + W p.2))
    (x : X) (y : Y)
    (h₀ : (differenceCLM.comp U).adjoint (U x + W y) = 0)
    (h₁ : (differenceCLM.comp W).adjoint (U x + W y) = 0) :
    x = 0 ∧ y = 0 := by
  have hi₀ := congrArg (fun z : X => inner ℝ z x) h₀
  have hi₁ := congrArg (fun z : Y => inner ℝ z y) h₁
  simp only [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.comp_apply, inner_zero_left] at hi₀ hi₁
  have hi : inner ℝ (U x + W y) (differenceCLM (U x + W y)) = 0 := by
    rw [map_add, inner_add_right, hi₀, hi₁, add_zero]
  have hz : U x + W y = 0 := eq_zero_of_difference_inner shiftCLM
    physicalShift_norm_le differenceCLM_injective (U x + W y) hi
  have hp : (x, y) = (0, 0) := hUW (by simpa only [map_zero, add_zero] using hz)
  exact ⟨congrArg (fun z : X × Y => z.1) hp, congrArg (fun z : X × Y => z.2) hp⟩

/-- The actual canonical increment matches the full difference-test span,
not just its listed residue generators. -/
theorem canonical_increment_difference_trial_test (L M : ℕ)
    (hL : 2 ≤ L) (hM : 2 ≤ M) (v : QHilbert) (hv : v ∈ trialSpace M) :
    inner ℝ ((canonical M hM : QHilbert) - canonical L hL) (differenceCLM v) =
      inner ℝ (target M - canonical L hL) (differenceCLM v) := by
  rw [inner_sub_left, inner_sub_left,
    ← conditional_inner M (canonical M hM) _
      (difference_mem_cell M (by omega) v hv), canonical_conditional]

/-- Coordinate test equations for any actual legal synthesis family.
For physical screening, take this family to be the old synthesis or the
screened new synthesis. -/
theorem canonical_increment_synthesis_test
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M)
    (U : X →L[ℝ] QHilbert) (hU : ∀ x, U x ∈ trialSpace M) :
    (differenceCLM.comp U).adjoint
      ((canonical M hM : QHilbert) - canonical L hL) =
      (differenceCLM.comp U).adjoint (target M - canonical L hL) := by
  apply ext_inner_right ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left]
  exact canonical_increment_difference_trial_test L M hL hM (U x) (hU x)

/-- Screening retains legality in the larger trial space. -/
theorem screenedSynthesis_mem_trial
    {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (M : ℕ) (U : X →L[ℝ] QHilbert) (V : Y →L[ℝ] QHilbert)
    (I : X →L[ℝ] X) (hU : ∀ x, U x ∈ trialSpace M)
    (hV : ∀ y, V y ∈ trialSpace M) (y : Y) :
    ContinuousLinearMap.screenedSynthesis U V I y ∈ trialSpace M := by
  rw [ContinuousLinearMap.screenedSynthesis_apply]
  exact (trialSpace M).sub_mem (hV y) (hU _)

end RiemannResearch.RH.QCRTContinuousSynthesis
