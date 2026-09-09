import RiemannResearch.RH.ParetoAdjacentRepairCalculus
import RiemannResearch.RH.ParetoFiniteGram
import Mathlib.Tactic.Positivity

/-!
# Signed finite binary-dilation energy

Source: user-provided argument, Section 6 of
`ParetoCovarianceRepairReport_Advanced_2026-09-08.md`.
The exact signed identity precedes the sufficient absolute-coefficient bound.
All entries are complete infinite Pareto inner products.
-/

open scoped BigOperators

namespace Finset

/-- Count the integer levels below both indices. -/
theorem sum_range_common_level (a b L : ℕ) (ha : a ≤ L) (_hb : b ≤ L) :
    (∑ j ∈ range L, if j < a ∧ j < b then (1 : ℝ) else 0) = (min a b : ℕ) := by
  classical
  have hf : (range L).filter (fun j => j < a ∧ j < b) = range (min a b) := by
    ext j
    simp only [mem_filter, mem_range, lt_min_iff]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨lt_of_lt_of_le h.1 ha, h⟩
  rw [← sum_filter, hf]
  simp

/-- The minimum kernel is exactly the Gram kernel of integer tail indicators. -/
theorem sum_sq_cumulative_tail (s : Finset ℕ) (c : ℕ → ℝ) (L : ℕ)
    (hs : ∀ n ∈ s, n ≤ L) :
    (∑ j ∈ range L, (∑ n ∈ s, if j < n then c n else 0)^2) =
      ∑ m ∈ s, ∑ n ∈ s, c m * c n * (min m n : ℕ) := by
  classical
  calc
    _ = ∑ j ∈ range L, ∑ m ∈ s, ∑ n ∈ s,
        (if j < m then c m else 0) * (if j < n then c n else 0) := by
      simp only [pow_two, sum_mul, mul_sum]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro m _
      apply sum_congr rfl
      intro n _
      ring
    _ = ∑ m ∈ s, ∑ n ∈ s, ∑ j ∈ range L,
        (if j < m then c m else 0) * (if j < n then c n else 0) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro m _
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro m hm
      apply sum_congr rfl
      intro n hn
      calc
        _ = (c m * c n) *
            (∑ j ∈ range L, if j < m ∧ j < n then (1 : ℝ) else 0) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro j _
          by_cases hm' : j < m <;> by_cases hn' : j < n <;> simp [hm', hn']
        _ = _ := by rw [sum_range_common_level m n L (hs m hm) (hs n hn)]

end Finset

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Full signed energy for the genuine dilations. -/
theorem binaryDilation_combination_energy (s : Finset ℕ) (c : ℕ → ℝ) :
    paretoInner (fun k => ∑ n ∈ s, c n * binaryDilation n k)
      (fun k => ∑ n ∈ s, c n * binaryDilation n k) =
      ∑ m ∈ s, ∑ n ∈ s, c m * c n * binaryDilationKernel m n :=
  paretoInner_finsetCombination s c binaryDilation_abs_le

/-- The positive-kernel estimate is applied only after the signed Gram identity.
There is no claim that the difference of two kernels is positive semidefinite. -/
theorem binaryDilation_combination_energy_le (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ n ∈ s, 0 < n) :
    paretoInner (fun k => ∑ n ∈ s, c n * binaryDilation n k)
      (fun k => ∑ n ∈ s, c n * binaryDilation n k) ≤
      Real.log 2 * (∑ m ∈ s, ∑ n ∈ s, |c m| * |c n| * (min m n : ℕ)) := by
  rw [binaryDilation_combination_energy]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  apply Finset.sum_le_sum
  intro n hn
  have habs : c m * c n ≤ |c m| * |c n| := by
    simpa only [abs_mul] using le_abs_self (c m * c n)
  calc
    _ ≤ |c m| * |c n| * binaryDilationKernel m n :=
      mul_le_mul_of_nonneg_right habs (binaryDilationKernel_nonneg m n)
    _ ≤ |c m| * |c n| * ((min m n : ℕ) * Real.log 2) :=
      mul_le_mul_of_nonneg_left (binaryDilationKernel_le_min m n (hs m hm) (hs n hn))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring

/-- Actual full dilation energy is controlled by the squared cumulative tails
of the absolute coefficients, with the exact minimum-kernel factorization. -/
theorem binaryDilation_combination_energy_le_cumulative_tail
    (s : Finset ℕ) (c : ℕ → ℝ) (L : ℕ)
    (hs : ∀ n ∈ s, 0 < n) (hL : ∀ n ∈ s, n ≤ L) :
    paretoInner (fun k => ∑ n ∈ s, c n * binaryDilation n k)
      (fun k => ∑ n ∈ s, c n * binaryDilation n k) ≤
      Real.log 2 * (∑ j ∈ Finset.range L, (∑ n ∈ s, if j < n then |c n| else 0)^2) := by
  rw [Finset.sum_sq_cumulative_tail s (fun n => |c n|) L hL]
  exact binaryDilation_combination_energy_le s c hs

/-- The actual adjacent repair is uniformly bounded at each fixed conductor. -/
theorem adjacentBinaryRepair_abs_le (n k : ℕ) :
    |adjacentBinaryRepair n k| ≤ |(n : ℝ)⁻¹| * (((n + 1 : ℕ) : ℝ) + (n : ℝ)) := by
  rw [adjacentBinaryRepair_eq_difference]
  exact bounded_const_mul
    (bounded_sub (binaryDilation_abs_le (n + 1)) (binaryDilation_abs_le n)) _ k

/-- Exact complete covariance of an arbitrary finite adjacent coefficient vector. -/
theorem adjacentBinaryRepair_combination_energy (s : Finset ℕ) (c : ℕ → ℝ) :
    paretoInner (fun k => ∑ m ∈ s, c m * adjacentBinaryRepair m k)
      (fun k => ∑ m ∈ s, c m * adjacentBinaryRepair m k) =
      ∑ m ∈ s, ∑ n ∈ s, c m * c n *
        ((binaryDilationKernel (m + 1) (n + 1) - binaryDilationKernel (m + 1) n -
          binaryDilationKernel m (n + 1) + binaryDilationKernel m n) /
            ((m : ℝ) * (n : ℝ))) := by
  rw [paretoInner_finsetCombination s c adjacentBinaryRepair_abs_le]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  rw [adjacentBinaryRepair_covariance]

end
end RiemannResearch.RH.Pareto
