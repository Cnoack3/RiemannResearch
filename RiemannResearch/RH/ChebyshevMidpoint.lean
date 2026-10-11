import RiemannResearch.Analysis.SequenceMidpoint
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact midpoint and Pareto energy of the actual Chebyshev function

Source: user-provided handoff Sections 6 and 18 for the midpoint square
identity. The harmonic compensated identity is its direct finite Abel
specialization. No Riemann Hypothesis or asymptotic energy estimate is assumed.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ChebyshevMidpoint
open SequenceMidpoint

def jump (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt (n + 1)
def psiNat (n : ℕ) : ℝ := Chebyshev.psi (n : ℝ)
def psiMid (n : ℕ) : ℝ := psiNat n - ArithmeticFunction.vonMangoldt n / 2
def residual (n : ℕ) : ℝ := psiNat n - n
def centeredJump (n : ℕ) : ℝ := jump n - 1

theorem partialSum_jump (N : ℕ) : partialSum jump N = psiNat N := by
  unfold partialSum jump psiNat
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, ← Nat.range_succ_eq_Icc_zero]
  simpa using (Finset.sum_range_succ' ArithmeticFunction.vonMangoldt N).symm

@[simp] theorem psiNat_zero : psiNat 0 = 0 := by
  rw [← partialSum_jump]
  simp

theorem psiNat_succ (n : ℕ) : psiNat (n + 1) = psiNat n + jump n := by
  rw [← partialSum_jump, partialSum_succ, partialSum_jump]

theorem midpoint_jump (n : ℕ) : midpoint jump n = psiMid (n + 1) := by
  rw [SequenceMidpoint.midpoint, partialSum_jump]
  simp only [psiMid, psiNat_succ, jump]
  ring

theorem psiMid_difference (n : ℕ) :
    psiMid (n + 2) - psiMid (n + 1) =
      (ArithmeticFunction.vonMangoldt (n + 1) +
        ArithmeticFunction.vonMangoldt (n + 2)) / 2 := by
  simpa [midpoint_jump, jump, Nat.add_assoc] using midpoint_difference jump n

theorem mangoldt_midpoint_square (N : ℕ) :
    (∑ n ∈ Finset.range N,
      ArithmeticFunction.vonMangoldt (n + 1) * psiMid (n + 1)) = psiNat N ^ 2 / 2 := by
  simpa only [jump, midpoint_jump, partialSum_jump] using sum_jump_mul_midpoint jump N

theorem weighted_mangoldt_midpoint_square (w : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      ArithmeticFunction.vonMangoldt (n + 1) * psiMid (n + 1) * w n) =
      psiNat N ^ 2 / 2 * w N +
        ∑ n ∈ Finset.range N, psiNat (n + 1) ^ 2 / 2 * (w n - w (n + 1)) := by
  simpa only [jump, midpoint_jump, partialSum_jump] using weighted_jump_mul_midpoint jump w N

theorem partialSum_centeredJump (N : ℕ) : partialSum centeredJump N = residual N := by
  simp [partialSum, centeredJump, Finset.sum_sub_distrib, residual, ← partialSum_jump]

theorem midpoint_centeredJump (n : ℕ) :
    midpoint centeredJump n = psiMid (n + 1) - ((n : ℝ) + 1) + 1 / 2 := by
  rw [SequenceMidpoint.midpoint, partialSum_centeredJump]
  simp only [residual, centeredJump, psiMid, psiNat_succ, jump]
  ring

def paretoEnergy (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    residual (n + 1) ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))

def signedHarmonic (N : ℕ) : ℝ :=
  2 * ∑ n ∈ Finset.range N,
    (ArithmeticFunction.vonMangoldt (n + 1) - 1) *
      (psiMid (n + 1) - ((n : ℝ) + 1) + 1 / 2) / ((n : ℝ) + 1)

/-- Exact endpoint-plus-Pareto identity for the actual centered arithmetic data. -/
theorem signedHarmonic_eq_endpoint_add_energy (N : ℕ) :
    signedHarmonic N = residual N ^ 2 / ((N : ℝ) + 1) + paretoEnergy N := by
  simpa only [signedHarmonic, paretoEnergy, centeredJump, jump,
    midpoint_centeredJump, partialSum_centeredJump] using
    harmonic_midpoint_energy centeredJump N

theorem compensated_signedHarmonic_eq_energy (N : ℕ) :
    signedHarmonic N - residual N ^ 2 / ((N : ℝ) + 1) = paretoEnergy N := by
  rw [signedHarmonic_eq_endpoint_add_energy]
  ring

theorem paretoEnergy_nonneg (N : ℕ) : 0 ≤ paretoEnergy N := by
  apply Finset.sum_nonneg
  intro n hn
  positivity

end RiemannResearch.RH.ChebyshevMidpoint
