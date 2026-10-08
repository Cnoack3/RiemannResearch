/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ArithmeticPacketCore

/-!
# Actual arithmetic packet-core inertia and ordinary mean-one optimization

The matrix is the finite cotangent-difference arithmetic core, whose complete
physical Gram realization is proved in `ArithmeticPacketCore`. Positivity on
the totient kernel and a strictly negative prime direction imply nonsingularity.
The exact Lorentz decomposition exhibits a single negative scalar direction
and the positive totient kernel, without invoking an eigenvalue-count API.

All inverse and optimizer hypotheses are discharged at squarefree divisor
stages L>2. No asymptotic saturation or RH converse is supplied here.
Source: user-directed continuation of `CriticalZeroMeanOneAdvance20261008.md`.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ArithmeticCoreInertia
open RiemannResearch.RH.Pareto
open PhysicalPacketCore
open RiemannResearch.LinearAlgebra.MeanOneCoreInertia

theorem arithmeticCore_transpose (Q : ℕ) (s : Finset ℕ) (hQ : 0 < Q)
    (hs : ∀ q ∈ s, 1 < q) (hsQ : ∀ q ∈ s, q ∣ Q) :
    (arithmeticPacketCore Q s)ᵀ = arithmeticPacketCore Q s := by
  rw [arithmeticPacketCore_eq_derivedCore Q s hQ hs hsQ]
  exact derivedCore_transpose s

theorem arithmeticCore_positiveOnMeanKernel (Q : ℕ) (s : Finset ℕ) (hQ : 0 < Q)
    (hs : ∀ q ∈ s, 1 < q) (hsQ : ∀ q ∈ s, q ∣ Q) :
    PositiveOnMeanKernel (arithmeticPacketCore Q s) (ramanujanTotientVector s) := by
  rw [arithmeticPacketCore_eq_derivedCore Q s hQ hs hsQ]
  exact derivedCore_positiveOnMeanKernel s hs

theorem arithmeticCore_det_ne_zero (Q : ℕ) (s : Finset ℕ) (hQ : 0 < Q)
    (hs : ∀ q ∈ s, 1 < q) (hsQ : ∀ q ∈ s, q ∣ Q)
    (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    (arithmeticPacketCore Q s).det ≠ 0 := by
  rw [arithmeticPacketCore_eq_derivedCore Q s hQ hs hsQ]
  exact derivedCore_det_ne_zero s hs hodd

theorem arithmeticCore_mul_inverse (Q : ℕ) (s : Finset ℕ) (hQ : 0 < Q)
    (hs : ∀ q ∈ s, 1 < q) (hsQ : ∀ q ∈ s, q ∣ Q)
    (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    arithmeticPacketCore Q s * (arithmeticPacketCore Q s)⁻¹ = 1 := by
  rw [arithmeticPacketCore_eq_derivedCore Q s hQ hs hsQ]
  exact derivedCore_mul_inverse s hs hodd

/-- The charge uses the independently defined arithmetic cotangent matrix. -/
def arithmeticInverseCharge (Q : ℕ) (s : Finset ℕ) : ℝ :=
  ramanujanTotientVector s ⬝ᵥ
    ((arithmeticPacketCore Q s)⁻¹ *ᵥ ramanujanTotientVector s)

theorem arithmeticInverseCharge_eq_physical (Q : ℕ) (s : Finset ℕ) (hQ : 0 < Q)
    (hs : ∀ q ∈ s, 1 < q) (hsQ : ∀ q ∈ s, q ∣ Q) :
    arithmeticInverseCharge Q s = inverseCharge s := by
  unfold arithmeticInverseCharge inverseCharge
  rw [arithmeticPacketCore_eq_derivedCore Q s hQ hs hsQ]

theorem arithmeticInverseCharge_neg (Q : ℕ) (s : Finset ℕ) (hQ : 0 < Q)
    (hs : ∀ q ∈ s, 1 < q) (hsQ : ∀ q ∈ s, q ∣ Q)
    (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    arithmeticInverseCharge Q s < 0 := by
  rw [arithmeticInverseCharge_eq_physical Q s hQ hs hsQ]
  exact inverseCharge_neg s hs hodd

/-- Exact inertia decomposition: one negative scalar square and the positive kernel. -/
theorem arithmeticCore_lorentz_completion (Q : ℕ) (s : Finset ℕ) (hQ : 0 < Q)
    (hs : ∀ q ∈ s, 1 < q) (hsQ : ∀ q ∈ s, q ∣ Q)
    (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) (x : s → ℝ) :
    let C := arithmeticInverseCharge Q s
    let z := x - ((ramanujanTotientVector s ⬝ᵥ x) / C) •
      ((arithmeticPacketCore Q s)⁻¹ *ᵥ ramanujanTotientVector s)
    C < 0 ∧ ramanujanTotientVector s ⬝ᵥ z = 0 ∧
      x ⬝ᵥ (arithmeticPacketCore Q s *ᵥ x) =
        (ramanujanTotientVector s ⬝ᵥ x) ^ 2 / C +
          z ⬝ᵥ (arithmeticPacketCore Q s *ᵥ z) ∧
      (z ≠ 0 → 0 < z ⬝ᵥ (arithmeticPacketCore Q s *ᵥ z)) := by
  dsimp only
  have hC := arithmeticInverseCharge_neg Q s hQ hs hsQ hodd
  have hpos := arithmeticCore_positiveOnMeanKernel Q s hQ hs hsQ
  obtain ⟨hm, he⟩ := lorentz_completion (arithmeticPacketCore Q s)
    (arithmeticPacketCore Q s)⁻¹ (ramanujanTotientVector s) x
    (arithmeticCore_mul_inverse Q s hQ hs hsQ hodd)
    (arithmeticCore_transpose Q s hQ hs hsQ) (ne_of_lt hC)
  exact ⟨hC, hm, he, fun hz => hpos _ hm hz⟩

/-- The explicit ordinary mean-one coefficient vector. -/
def arithmeticConstrainedOptimizer (Q : ℕ) (s : Finset ℕ) : s → ℝ :=
  (2 / arithmeticInverseCharge Q s) •
    ((arithmeticPacketCore Q s)⁻¹ *ᵥ ramanujanTotientVector s)

theorem arithmeticConstrainedOptimizer_eq_physical (Q : ℕ) (s : Finset ℕ) (hQ : 0 < Q)
    (hs : ∀ q ∈ s, 1 < q) (hsQ : ∀ q ∈ s, q ∣ Q) :
    arithmeticConstrainedOptimizer Q s = constrainedOptimizer s := by
  unfold arithmeticConstrainedOptimizer constrainedOptimizer
  rw [arithmeticInverseCharge_eq_physical Q s hQ hs hsQ,
    arithmeticPacketCore_eq_derivedCore Q s hQ hs hsQ]

/-- The optimizer satisfies the actual finite ordinary-period mean constraint. -/
theorem arithmeticConstrainedOptimizer_period_mean (Q : ℕ) (s : Finset ℕ) (hQ : 0 < Q)
    (hs : ∀ q ∈ s, 1 < q) (hsQ : ∀ q ∈ s, q ∣ Q)
    (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    (∑ r : Fin Q, synthesis s (arithmeticConstrainedOptimizer Q s) r.val) / (Q : ℝ) = 1 := by
  rw [synthesis_period_mean Q s _ hQ hs hsQ,
    arithmeticConstrainedOptimizer_eq_physical Q s hQ hs hsQ,
    constrainedOptimizer_totient s hs hodd]
  norm_num

theorem arithmeticConstrainedOptimizer_error (Q : ℕ) (s : Finset ℕ) (hQ : 0 < Q)
    (hs : ∀ q ∈ s, 1 < q) (hsQ : ∀ q ∈ s, q ∣ Q)
    (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    paretoError (synthesis s (arithmeticConstrainedOptimizer Q s)) =
      1 + 4 * Real.pi / arithmeticInverseCharge Q s := by
  rw [arithmeticConstrainedOptimizer_eq_physical Q s hQ hs hsQ,
    arithmeticInverseCharge_eq_physical Q s hQ hs hsQ]
  exact constrainedOptimizer_error s hs hodd

/-- All signed correction terms remain in the actual ordinary mean-one completion. -/
theorem arithmeticConstrainedOptimizer_completion (Q : ℕ) (s : Finset ℕ) (hQ : 0 < Q)
    (hs : ∀ q ∈ s, 1 < q) (hsQ : ∀ q ∈ s, q ∣ Q)
    (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) (c : s → ℝ)
    (hmean : (∑ r : Fin Q, synthesis s c r.val) / (Q : ℝ) = 1) :
    paretoError (synthesis s c) = 1 + 4 * Real.pi / arithmeticInverseCharge Q s +
      Real.pi * ((c - arithmeticConstrainedOptimizer Q s) ⬝ᵥ
        (arithmeticPacketCore Q s *ᵥ (c - arithmeticConstrainedOptimizer Q s))) := by
  have hmean' := synthesis_period_mean Q s c hQ hs hsQ
  have hc : ramanujanTotientVector s ⬝ᵥ c = 2 := by
    rw [hmean] at hmean'
    linarith only [hmean']
  rw [arithmeticInverseCharge_eq_physical Q s hQ hs hsQ,
    arithmeticConstrainedOptimizer_eq_physical Q s hQ hs hsQ,
    arithmeticPacketCore_eq_derivedCore Q s hQ hs hsQ]
  exact constrainedOptimizer_completion s hs hodd c hc

/-- The actual period mean-one minimum and uniqueness, with no inverse premise. -/
theorem arithmeticConstrainedOptimizer_unique_minimum (Q : ℕ) (s : Finset ℕ) (hQ : 0 < Q)
    (hs : ∀ q ∈ s, 1 < q) (hsQ : ∀ q ∈ s, q ∣ Q)
    (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) (c : s → ℝ)
    (hmean : (∑ r : Fin Q, synthesis s c r.val) / (Q : ℝ) = 1) :
    1 + 4 * Real.pi / arithmeticInverseCharge Q s ≤ paretoError (synthesis s c) ∧
      (paretoError (synthesis s c) = 1 + 4 * Real.pi / arithmeticInverseCharge Q s ↔
        c = arithmeticConstrainedOptimizer Q s) := by
  have hmean' := synthesis_period_mean Q s c hQ hs hsQ
  have hc : ramanujanTotientVector s ⬝ᵥ c = 2 := by
    rw [hmean] at hmean'
    linarith only [hmean']
  rw [arithmeticInverseCharge_eq_physical Q s hQ hs hsQ,
    arithmeticConstrainedOptimizer_eq_physical Q s hQ hs hsQ]
  exact constrainedOptimizer_unique_minimum s hs hodd c hc

/-- At every physical squarefree stage, symmetry, nonsingularity and the strict endpoint bound are unconditional. -/
theorem squarefree_stage_inertia (L : ℕ) (hL : 2 < L) (hsq : Squarefree L) :
    (arithmeticPacketCore L (divisorPackets L))ᵀ = arithmeticPacketCore L (divisorPackets L) ∧
      PositiveOnMeanKernel (arithmeticPacketCore L (divisorPackets L))
        (ramanujanTotientVector (divisorPackets L)) ∧
      (arithmeticPacketCore L (divisorPackets L)).det ≠ 0 ∧
      arithmeticInverseCharge L (divisorPackets L) < -4 * Real.pi := by
  have hL0 : 0 < L := by omega
  have hs := divisorPackets_legal L
  have hsL := divisorPackets_period L
  have ho := divisorPackets_odd L hL hsq
  refine ⟨arithmeticCore_transpose L _ hL0 hs hsL,
    arithmeticCore_positiveOnMeanKernel L _ hL0 hs hsL,
    arithmeticCore_det_ne_zero L _ hL0 hs hsL ho, ?_⟩
  rw [arithmeticInverseCharge_eq_physical L _ hL0 hs hsL]
  exact inverseCharge_lt_neg_four_pi _ hs ho L hL0 hsL

/-- Complete squarefree-stage optimizer, exact minimum and actual ordinary mean one. -/
theorem squarefree_stage_optimizer (L : ℕ) (hL : 2 < L) (hsq : Squarefree L) :
    (∑ r : Fin L, synthesis (divisorPackets L)
      (arithmeticConstrainedOptimizer L (divisorPackets L)) r.val) / (L : ℝ) = 1 ∧
      paretoError (synthesis (divisorPackets L)
        (arithmeticConstrainedOptimizer L (divisorPackets L))) =
        1 + 4 * Real.pi / arithmeticInverseCharge L (divisorPackets L) ∧
      ∀ c : divisorPackets L → ℝ,
        (∑ r : Fin L, synthesis (divisorPackets L) c r.val) / (L : ℝ) = 1 →
          (1 + 4 * Real.pi / arithmeticInverseCharge L (divisorPackets L) ≤
            paretoError (synthesis (divisorPackets L) c) ∧
            (paretoError (synthesis (divisorPackets L) c) =
              1 + 4 * Real.pi / arithmeticInverseCharge L (divisorPackets L) ↔
                c = arithmeticConstrainedOptimizer L (divisorPackets L))) := by
  have hL0 : 0 < L := by omega
  have hs := divisorPackets_legal L
  have hsL := divisorPackets_period L
  have ho := divisorPackets_odd L hL hsq
  exact ⟨arithmeticConstrainedOptimizer_period_mean L _ hL0 hs hsL ho,
    arithmeticConstrainedOptimizer_error L _ hL0 hs hsL ho,
    fun c hc => arithmeticConstrainedOptimizer_unique_minimum L _ hL0 hs hsL ho c hc⟩

end RiemannResearch.RH.Pareto.ArithmeticCoreInertia
