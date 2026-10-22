/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoEquivalence
import Mathlib.Analysis.Normed.Operator.Basic
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Tactic.Ring

/-!
# Transport of Pareto operators and separating functionals to Q

Source: user-requested Pareto-to-Q transfer, 15 October 2026; the standard
similarity construction is applied to the checked sequence-preserving
continuous linear equivalence.

This transports every bounded linear operator, its algebraic identities,
real eigenvectors and continuous separating functionals. Similarity does
not assert self-adjointness in the Q metric. Orthogonal projection operators,
Gram entries and DPP kernels must use the actual Q inner product.
-/

noncomputable section
namespace RiemannResearch.RH.QParetoOperatorTransfer
open Pareto ZetaTwoProbability ZetaTwoHilbert ZetaTwoParetoTransfer QParetoEquivalence

/-- Conjugate an actual Pareto operator by the physical-sequence equivalence. -/
def transport (A : ThresholdHilbert →L[ℝ] ThresholdHilbert) : QHilbert →L[ℝ] QHilbert :=
  toQCLM.comp (A.comp toParetoCLM)

@[simp] theorem transport_apply (A : ThresholdHilbert →L[ℝ] ThresholdHilbert)
    (f : QHilbert) : transport A f = toQ (A (toPareto f)) := rfl

@[simp] theorem toPareto_transport (A : ThresholdHilbert →L[ℝ] ThresholdHilbert)
    (f : QHilbert) : toPareto (transport A f) = A (toPareto f) := by
  rw [transport_apply, toPareto_toQ]

theorem physical_transport (A : ThresholdHilbert →L[ℝ] ThresholdHilbert)
    (f : QHilbert) : qSequence (transport A f) = hilbertSequence (A (toPareto f)) := by
  rw [transport_apply, toQ_sequence]

@[simp] theorem transport_zero : transport 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  change toQLinear 0 = 0
  exact map_zero _

@[simp] theorem transport_one :
    transport (1 : ThresholdHilbert →L[ℝ] ThresholdHilbert) = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  exact toQ_toPareto f

theorem transport_add (A B : ThresholdHilbert →L[ℝ] ThresholdHilbert) :
    transport (A + B) = transport A + transport B := by
  apply ContinuousLinearMap.ext
  intro f
  change toQLinear (A (toPareto f) + B (toPareto f)) =
    toQLinear (A (toPareto f)) + toQLinear (B (toPareto f))
  exact map_add _ _ _

theorem transport_smul (c : ℝ) (A : ThresholdHilbert →L[ℝ] ThresholdHilbert) :
    transport (c • A) = c • transport A := by
  apply ContinuousLinearMap.ext
  intro f
  change toQLinear (c • A (toPareto f)) = c • toQLinear (A (toPareto f))
  exact map_smul _ _ _

theorem transport_mul (A B : ThresholdHilbert →L[ℝ] ThresholdHilbert) :
    transport (A * B) = transport A * transport B := by
  apply ContinuousLinearMap.ext
  intro f
  change toQ (A (B (toPareto f))) = toQ (A (toPareto (toQ (B (toPareto f)))))
  rw [toPareto_toQ]

theorem transport_pow (A : ThresholdHilbert →L[ℝ] ThresholdHilbert) (n : ℕ) :
    transport (A ^ n) = transport A ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, transport_mul, ih, pow_succ]

theorem transport_injective : Function.Injective transport := by
  intro A B h
  apply ContinuousLinearMap.ext
  intro f
  have hh := congrArg (fun T : QHilbert →L[ℝ] QHilbert => toPareto (T (toQ f))) h
  simpa only [toPareto_transport, toPareto_toQ] using hh

/-- Eigenvector identities transfer exactly, without a spectral model assumption. -/
theorem eigenvector_iff (A : ThresholdHilbert →L[ℝ] ThresholdHilbert)
    (f : QHilbert) (a : ℝ) :
    transport A f = a • f ↔ A (toPareto f) = a • toPareto f := by
  constructor
  · intro h
    have hh := congrArg toPareto h
    change toPareto (transport A f) = toParetoLinear (a • f) at hh
    rw [toPareto_transport, map_smul] at hh
    exact hh
  · intro h
    apply paretoEquiv.injective
    change toPareto (transport A f) = toParetoLinear (a • f)
    rw [toPareto_transport, map_smul]
    exact h

theorem transport_norm_le (A : ThresholdHilbert →L[ℝ] ThresholdHilbert) (f : QHilbert) :
    ‖transport A f‖ ≤
      Real.sqrt (2 / zetaTwo) * ‖A‖ * Real.sqrt zetaTwo * ‖f‖ := by
  calc
    _ ≤ Real.sqrt (2 / zetaTwo) * ‖A (toPareto f)‖ := toQ_norm_le _
    _ ≤ Real.sqrt (2 / zetaTwo) * (‖A‖ * ‖toPareto f‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm _) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (2 / zetaTwo) * (‖A‖ * (Real.sqrt zetaTwo * ‖f‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (toPareto_norm_le _) (norm_nonneg _))
        (Real.sqrt_nonneg _)
    _ = _ := by ring

section Functional
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every continuous Pareto-valued test or Mellin functional transfers to Q. -/
def functional (L : ThresholdHilbert →L[ℝ] E) : QHilbert →L[ℝ] E :=
  L.comp toParetoCLM

@[simp] theorem functional_apply (L : ThresholdHilbert →L[ℝ] E) (f : QHilbert) :
    functional L f = L (toPareto f) := rfl

theorem functional_norm_le (L : ThresholdHilbert →L[ℝ] E) (f : QHilbert) :
    ‖functional L f‖ ≤ ‖L‖ * Real.sqrt zetaTwo * ‖f‖ := by
  calc
    _ ≤ ‖L‖ * ‖toPareto f‖ := L.le_opNorm _
    _ ≤ ‖L‖ * (Real.sqrt zetaTwo * ‖f‖) :=
      mul_le_mul_of_nonneg_left (toPareto_norm_le _) (norm_nonneg _)
    _ = _ := by ring

/-- Annihilator identities survive for precisely the same vectors and tests. -/
theorem functional_annihilates_iff (L : ThresholdHilbert →L[ℝ] E)
    (S : Submodule ℝ QHilbert) :
    (∀ f ∈ S, functional L f = 0) ↔
      ∀ g ∈ S.map paretoEquiv.toLinearMap, L g = 0 := by
  constructor
  · intro h g hg
    obtain ⟨f, hf, rfl⟩ := hg
    exact h f hf
  · intro h f hf
    exact h _ ⟨f, hf, rfl⟩

end Functional
end RiemannResearch.RH.QParetoOperatorTransfer
