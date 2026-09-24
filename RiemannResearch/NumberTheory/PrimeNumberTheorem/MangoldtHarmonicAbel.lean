import RiemannResearch.NumberTheory.PrimeNumberTheorem.LogarithmicMobiusConvolution
import RiemannResearch.Analysis.ReciprocalAbel

/-! Exact specialization of the finite reciprocal Abel identity to the actual
Chebyshev remainder. Source: finite Abel summation and the definition of psi. -/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

theorem chebyshev_remainder_nat_eq_range (N : ℕ) :
    R (N : ℝ) = ∑ k ∈ Finset.range N, (ArithmeticFunction.vonMangoldt (k + 1) - 1) := by
  rw [R, Psi, Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  have he : Finset.Icc 0 N = Finset.range (N + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  rw [he, Finset.sum_range_succ', Finset.sum_sub_distrib]
  simp

theorem mangoldtHarmonicDefect_eq_reciprocal_abel (N : ℕ) :
    mangoldtHarmonicDefect N = R (N : ℝ) / ((N : ℝ) + 1) +
      ∑ k ∈ Finset.range N,
        R ((k : ℝ) + 1) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  have hzero : R ((0 : ℕ) : ℝ) = 0 := by
    rw [chebyshev_remainder_nat_eq_range]
    simp
  have hstep (n : ℕ) : R ((n + 1 : ℕ) : ℝ) =
      R (n : ℝ) + (ArithmeticFunction.vonMangoldt (n + 1) - 1) := by
    rw [chebyshev_remainder_nat_eq_range, chebyshev_remainder_nat_eq_range,
      Finset.sum_range_succ]
  have h := RiemannResearch.Analysis.reciprocal_partial_sum_abel
    (fun n => ArithmeticFunction.vonMangoldt n - 1) (fun n => R (n : ℝ))
    hzero hstep N
  have he : (Finset.range N).image (fun k => k + 1) = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨k, hk, rfl⟩
      omega
    · intro hn
      exact ⟨n - 1, by omega, by omega⟩
  unfold mangoldtHarmonicDefect
  rw [← he, Finset.sum_image]
  · simpa only [Nat.cast_add, Nat.cast_one] using h
  · intro a ha b hb hab
    dsimp only at hab
    omega

end RiemannResearch.NumberTheory.PrimeNumberTheorem
