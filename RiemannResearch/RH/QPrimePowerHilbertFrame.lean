/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QDivisorWaveletFactorization
import RiemannResearch.RH.QDivisorWaveletDensity
import RiemannResearch.RH.QDivisibilityDensity
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# The same-prime subfamily of the arithmetic Hilbert basis

Source: user-provided orthonormal-basis research direction, 20 October 2026.
These are actual Q-Hilbert vectors indexed by all powers of one prime.
Their ambient orthonormality does not assert legal squarefree membership.
-/
noncomputable section
namespace RiemannResearch.RH.QDivisorHilbert
open ZetaTwoHilbert QDivisibilityDensity

/-- Prime-power arithmetic wavelets are adjacent scaled divisibility tails. -/
theorem divisorWavelet_prime_pow_succ (p k : ℕ) (hp : p.Prime) :
    divisorWavelet (p ^ (k + 1)) =
      ((p : ℝ) ^ (k + 1)) ^ 2 • qDivisor (p ^ (k + 1)) -
        ((p : ℝ) ^ k) ^ 2 • qDivisor (p ^ k) := by
  apply qSequence_injective
  funext n
  cases n with
  | zero => simp
  | succ n =>
    rw [qSequence_divisorWavelet_succ, ← divisorWaveletAF_apply,
      divisorWaveletAF_prime_pow_succ p k (n + 1) hp]
    change _ = qSequenceLinear (_ - _) (n + 1)
    simp [map_sub, map_smul, qSequenceLinear, qSequence_qDivisor,
      scaledDivisorAF, positiveDivisor, Nat.cast_pow]

/-- All same-prime normalized modes, including the constant at index zero. -/
def primePowerFrame (p : ℕ) (hp : p.Prime) (k : ℕ) : QHilbert :=
  QDivisorHilbert.normalizedDivisorWavelet ⟨p ^ k, pow_pos hp.pos _⟩

theorem primePowerFrame_orthonormal (p : ℕ) (hp : p.Prime) :
    Orthonormal ℝ (primePowerFrame p hp) := by
  apply QDivisorHilbert.normalizedDivisorWavelet_orthonormal.comp
    (fun k => (⟨p ^ k, pow_pos hp.pos _⟩ : ℕ+))
  intro a b h
  exact Nat.pow_right_injective hp.two_le (congrArg Subtype.val h)

@[simp] theorem primePowerFrame_zero (p : ℕ) (hp : p.Prime) :
    primePowerFrame p hp 0 = qOne := by
  simp [primePowerFrame, QDivisorHilbert.normalizedDivisorWavelet,
    divisorWavelet_one, qJordanTwo]

end RiemannResearch.RH.QDivisorHilbert
