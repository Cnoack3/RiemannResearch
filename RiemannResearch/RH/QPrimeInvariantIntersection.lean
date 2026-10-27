/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimeResampling
import RiemannResearch.Analysis.PrimeIncrementEnvelope
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Linarith

/-!
# Common prime-resampling fixed vectors are exactly constants

Source: the prime-factor telescoping argument from the user-provided
PrimeResamplingResearch20261027.md. The argument is on actual physical integer
coordinates; no zero-one-law or tail-measurability assumption is needed.
-/

noncomputable section
namespace RiemannResearch.RH.QPrimeResampling
open ZetaTwoHilbert
open RiemannResearch.Analysis.PrimeIncrementEnvelope

def constantSpace : Submodule ℝ QHilbert := Submodule.span ℝ ({qOne} : Set QHilbert)

theorem prime_invariant_eq_constant (f : QHilbert)
    (hf : ∀ p : ℕ, p.Prime → f ∈ primeInvariant p) :
    f = qSequence f 1 • qOne := by
  have hcoords (n : ℕ) (hn : 0 < n) : qSequence f n = qSequence f 1 := by
    have h := sub_one_abs_le_of_prime_increments (qSequence f) 0 (by norm_num) 0
      (by intro p k hp hk; simp only [(mem_primeInvariant p f).mp (hf p hp) k,
          sub_self, abs_zero, zero_mul, le_refl]) n hn
    simp only [zero_mul] at h
    exact sub_eq_zero.mp (abs_nonpos_iff.mp h)
  apply qSequence_injective
  funext n
  change qSequence f n = qSequenceLinear (qSequence f 1 • qOne) n
  rw [map_smul]
  change qSequence f n = qSequence f 1 * qSequence qOne n
  rw [qSequence_qOne]
  by_cases hn : n = 0
  · subst n; simp [qOneSequence]
  · simp only [qOneSequence, if_neg hn, mul_one]
    exact hcoords n (Nat.pos_of_ne_zero hn)

theorem constant_mem_primeInvariant (c : ℝ) (p : ℕ) (hp : p.Prime) :
    c • qOne ∈ primeInvariant p := by
  intro n
  change qSequenceLinear (c • qOne) (p * n) = qSequenceLinear (c • qOne) n
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  change c * qSequence qOne (p * n) = c * qSequence qOne n
  rw [qSequence_qOne]
  simp only [qOneSequence, mul_eq_zero, hp.ne_zero, false_or]

theorem invariant_under_primes_iff_constant (f : QHilbert) :
    (∀ p : ℕ, p.Prime → f ∈ primeInvariant p) ↔ f ∈ constantSpace := by
  constructor
  · intro hf
    rw [prime_invariant_eq_constant f hf]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton qOne))
  · intro hf p hp
    rcases Submodule.mem_span_singleton.mp hf with ⟨c, rfl⟩
    exact constant_mem_primeInvariant c p hp

/-- The common invariant space of every prime coordinate is the one-dimensional
constant subspace in the actual complete Q Hilbert space. -/
theorem iInf_primeInvariant_eq_constantSpace :
    (⨅ p : ℕ, ⨅ (_ : p.Prime), primeInvariant p) = constantSpace := by
  ext f
  simp only [Submodule.mem_iInf]
  exact invariant_under_primes_iff_constant f

instance constantSpace_finiteDimensional : FiniteDimensional ℝ constantSpace :=
  FiniteDimensional.span_singleton ℝ qOne

/-- Orthogonal projection onto the common prime fixed space is its actual mean. -/
theorem constantSpace_projection (f : QHilbert) :
    constantSpace.starProjection f = inner ℝ qOne f • qOne := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton qOne))
  · intro g hg
    rcases Submodule.mem_span_singleton.mp hg with ⟨c, rfl⟩
    rw [real_inner_smul_right, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, qOne_norm_sq, mul_one, real_inner_comm f qOne,
      sub_self, mul_zero]

end RiemannResearch.RH.QPrimeResampling
