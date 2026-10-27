/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QHilbertConvergence
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Actual prime-resampling projections in the complete Q Hilbert space

Source: the user's prime-coordinate research agenda. The closed subspace
below consists of actual physical sequences invariant under multiplication
by p. Projection onto it will be identified with the complete geometric
conditional average along the p-power fiber, with no cutoff.
-/

noncomputable section
namespace RiemannResearch.RH.QPrimeResampling
open ZetaTwoHilbert

/-- Physical functions independent of the p-adic valuation coordinate. -/
def primeInvariant (p : ℕ) : Submodule ℝ QHilbert where
  carrier := {f | ∀ n : ℕ, qSequence f (p * n) = qSequence f n}
  zero_mem' := by intro n; change qSequenceLinear 0 (p * n) = qSequenceLinear 0 n; simp
  add_mem' := by
    intro f g hf hg n
    change qSequenceLinear (f + g) (p * n) = qSequenceLinear (f + g) n
    simp only [map_add, Pi.add_apply]
    exact congrArg₂ (· + ·) (hf n) (hg n)
  smul_mem' := by
    intro a f hf n
    change qSequenceLinear (a • f) (p * n) = qSequenceLinear (a • f) n
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    exact congrArg (a * ·) (hf n)

@[simp] theorem mem_primeInvariant (p : ℕ) (f : QHilbert) :
    f ∈ primeInvariant p ↔ ∀ n : ℕ, qSequence f (p * n) = qSequence f n := Iff.rfl

instance primeInvariant_isClosed (p : ℕ) : IsClosed (primeInvariant p : Set QHilbert) := by
  change IsClosed {f : QHilbert | ∀ n : ℕ, qSequence f (p * n) = qSequence f n}
  simp_rw [← qEvalCLM_apply]
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun n => isClosed_eq (qEvalCLM (p * n)).continuous (qEvalCLM n).continuous

instance primeInvariant_completeSpace (p : ℕ) : CompleteSpace (primeInvariant p) :=
  IsClosed.completeSpace_coe

/-- Orthogonal conditional averaging in the actual countable Q space. -/
def C (p : ℕ) : QHilbert →L[ℝ] QHilbert := (primeInvariant p).starProjection

@[simp] theorem C_mem (p : ℕ) (f : QHilbert) : C p f ∈ primeInvariant p :=
  (primeInvariant p).starProjection_apply_mem f

@[simp] theorem C_idem (p : ℕ) (f : QHilbert) : C p (C p f) = C p f :=
  Submodule.starProjection_eq_self_iff.mpr (C_mem p f)

theorem C_eq_self_iff (p : ℕ) (f : QHilbert) : C p f = f ↔ f ∈ primeInvariant p :=
  Submodule.starProjection_eq_self_iff

theorem C_selfAdjoint (p : ℕ) (f g : QHilbert) :
    inner ℝ (C p f) g = inner ℝ f (C p g) :=
  (primeInvariant p).inner_starProjection_left_eq_right f g

theorem C_norm_le (p : ℕ) (f : QHilbert) : ‖C p f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ‖(primeInvariant p).starProjection‖ * ‖f‖ :=
      (primeInvariant p).starProjection.le_opNorm f
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right
      (Submodule.starProjection_norm_le _) (norm_nonneg f)
    _ = _ := one_mul _

theorem C_residual_orthogonal (p : ℕ) (f g : QHilbert) (hg : g ∈ primeInvariant p) :
    inner ℝ (f - C p f) g = 0 :=
  (primeInvariant p).starProjection_inner_eq_zero f g hg

/-- Exact one-coordinate energy decomposition. -/
theorem C_energy_identity (p : ℕ) (f : QHilbert) :
    ‖f‖ ^ 2 = ‖C p f‖ ^ 2 + ‖f - C p f‖ ^ 2 := by
  simpa only [C, Submodule.starProjection_orthogonal_val] using
    Submodule.norm_sq_eq_add_norm_sq_starProjection f (primeInvariant p)

/-- The one-coordinate Dirichlet energy has an exact signed inner-product form. -/
theorem C_energy_eq (p : ℕ) (f : QHilbert) :
    ‖f - C p f‖ ^ 2 = inner ℝ f (f - C p f) := by
  have horth := C_residual_orthogonal p f (C p f) (C_mem p f)
  have horth' : inner ℝ (C p f) (f - C p f) = 0 :=
    (real_inner_comm _ _).trans horth
  calc
    _ = inner ℝ (f - C p f) (f - C p f) := (real_inner_self_eq_norm_sq _).symm
    _ = inner ℝ ((f - C p f) + C p f) (f - C p f) := by
      rw [inner_add_left, horth', add_zero]
    _ = _ := by rw [sub_add_cancel]


/-- A nonzero-prime resampling fixes the genuine constant vector. -/
theorem qOne_mem_primeInvariant (p : ℕ) (hp : p ≠ 0) : qOne ∈ primeInvariant p := by
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · simp [qSequence_qOne, qOneSequence, hn, mul_ne_zero hp hn]

@[simp] theorem C_qOne (p : ℕ) (hp : p ≠ 0) : C p qOne = qOne :=
  (C_eq_self_iff p qOne).mpr (qOne_mem_primeInvariant p hp)

theorem C_preserves_mean (p : ℕ) (hp : p ≠ 0) (f : QHilbert) :
    inner ℝ qOne (C p f) = inner ℝ qOne f := by
  rw [← C_selfAdjoint p qOne f, C_qOne p hp]

end RiemannResearch.RH.QPrimeResampling
