/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ClippedEnergyExtension
import RiemannResearch.RH.QPrimeProjectionPoincare
import RiemannResearch.RH.QPrimeJumpEnergyIdentity
import RiemannResearch.RH.QPairVariance

/-!
# The actual complete countable prime-resampling Poincare inequality

Source: PrimeResamplingResearch20261027.md, Section 4. The exact actual-Q
Hilbert gap, the complete arithmetic-kernel identity, and finite-head
clipping give the gap-one comparison for every real physical sequence.
Neither a first moment nor a second moment is a hypothesis. Either
extended nonnegative energy may be infinite.
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RiemannResearch.RH.QPrimeResampling
open ZetaTwoHilbert PrimeResampling QPairVariance
open RiemannResearch.Analysis.CountableJumpEnergy
open RiemannResearch.Analysis.ClippedEnergyExtension

/-- Exact gap one on the actual Q Hilbert space, expressed as a complete
pair-energy comparison for the literal physical sequence. -/
theorem prime_poincare_qSequence (f : QHilbert) :
    pairVariance (qSequence f) ≤ dirichletEnergy (qSequence f) := by
  rw [pairVariance_qSequence, dirichletEnergy_qSequence_eq]
  exact prime_projection_poincare f

/-- Bounded physical sequences are encoded in the actual Q space; their
arbitrary value at the null state zero has no effect on either energy. -/
theorem prime_poincare_bounded (g : ℕ → ℝ)
    (hg : ∃ R : ℝ, 0 ≤ R ∧ ∀ n, |g n| ≤ R) :
    pairVariance g ≤ dirichletEnergy g := by
  obtain ⟨R, hR, hg⟩ := hg
  let g₀ : ℕ → ℝ := fun n => if n = 0 then 0 else g n
  have hg₀ : ∀ n, |g₀ n| ≤ R := by
    intro n
    dsimp [g₀]
    split_ifs
    · simpa using hR
    · exact hg n
  have hz : g₀ 0 = 0 := by simp [g₀]
  have hs := boundedQ_square_summable g₀ R hR hg₀
  have hgap := prime_poincare_qSequence (encodeQ g₀ hs)
  rw [qSequence_encodeQ g₀ hs hz] at hgap
  have hpos : ∀ n : ℕ, n ≠ 0 → g₀ n = g n := by
    intro n hn
    simp [g₀, hn]
  have hpair : pairVariance g₀ = pairVariance g :=
    countableJumpEnergy_congr_off_zero pairFlow
      (fun n => by simp [pairFlow, positiveQWeight])
      (fun n => by simp [pairFlow, positiveQWeight]) g₀ g hpos
  have hprime : dirichletEnergy g₀ = dirichletEnergy g :=
    countableJumpEnergy_congr_off_zero primeFlow
      primeFlow_zero_left primeFlow_zero_right g₀ g hpos
  rwa [hpair, hprime] at hgap

/-- Actual countable prime-resampling Poincare inequality with sharp constant
one, for every real sequence and with no integrability premise. -/
theorem prime_resampling_poincare (g : ℕ → ℝ) :
    pairVariance g ≤ dirichletEnergy g := by
  exact comparison_of_bounded pairFlow primeFlow prime_poincare_bounded g

end RiemannResearch.RH.QPrimeResampling
