import RiemannResearch.Analysis.ChebyshevCellEnergy
import RiemannResearch.RH.ChebyshevMidpoint

/-!
# The exact continuous Chebyshev energy as a Pareto sum

The cell formula is applied to the actual right-continuous Chebyshev
function. Source: user-provided handoff Sections 18--19 for the Chebyshev energy,
and the exact unit-cell calculation in Analysis.ChebyshevCellEnergy.
Integer endpoints are excluded only in the almost-everywhere
comparison; their jumps are not erased from the arithmetic definitions.
No asymptotic estimate or Riemann Hypothesis is assumed.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators Interval

namespace RiemannResearch.RH.ChebyshevMidpoint

open RiemannResearch.ChebyshevCell

def continuousEnergy (N : ℕ) : ℝ :=
  ∫ x in (1 : ℝ)..(N : ℝ) + 1, (Chebyshev.psi x - x) ^ 2 / x ^ 2

def shiftedParetoEnergy (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    (psiNat (n + 1) - center ((n : ℝ) + 1)) ^ 2 /
      (((n : ℝ) + 1) * ((n : ℝ) + 2))

def deterministicDefect (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, defect ((n : ℝ) + 1)

theorem psi_eq_psiNat_on_cell (n : ℕ) {x : ℝ}
    (hx : x ∈ Ico (n : ℝ) ((n : ℝ) + 1)) :
    Chebyshev.psi x = psiNat n := by
  change Chebyshev.psi x = Chebyshev.psi (n : ℝ)
  rw [Chebyshev.psi_eq_psi_coe_floor, Nat.floor_eq_on_Ico n x hx]

theorem actual_cell_integrable (n : ℕ) (hn : 0 < n) :
    IntervalIntegrable (fun x : ℝ => (Chebyshev.psi x - x) ^ 2 / x ^ 2)
      volume (n : ℝ) ((n : ℝ) + 1) := by
  apply (intervalIntegrable_congr_uIoo ?_).2
    (integrable_energy (Nat.cast_pos.mpr hn) (psiNat n))
  intro x hx
  rw [uIoo_of_le (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)] at hx
  dsimp only
  rw [psi_eq_psiNat_on_cell n ⟨hx.1.le, hx.2⟩]

theorem actual_cell_eq_energy (n : ℕ) :
    (∫ x in (n : ℝ)..(n : ℝ) + 1,
      (Chebyshev.psi x - x) ^ 2 / x ^ 2) = energy (n : ℝ) (psiNat n) := by
  unfold energy
  apply intervalIntegral.integral_congr_Ioo_of_le
    (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)
  intro x hx
  dsimp only
  rw [psi_eq_psiNat_on_cell n ⟨hx.1.le, hx.2⟩]

theorem continuousEnergy_sum_cells (N : ℕ) :
    continuousEnergy N =
      ∑ n ∈ Finset.range N, energy ((n : ℝ) + 1) (psiNat (n + 1)) := by
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => (n : ℝ) + 1) (n := N)
    (f := fun x : ℝ => (Chebyshev.psi x - x) ^ 2 / x ^ 2)
    (fun n hn => by
      simpa only [Nat.cast_add, Nat.cast_one] using
        actual_cell_integrable (n + 1) (Nat.succ_pos n))
  calc
    continuousEnergy N = ∑ n ∈ Finset.range N,
        ∫ x in (n : ℝ) + 1..((n : ℝ) + 1) + 1,
          (Chebyshev.psi x - x) ^ 2 / x ^ 2 := by
      simpa only [continuousEnergy, Nat.cast_add, Nat.cast_one,
        Nat.cast_zero, zero_add] using h.symm
    _ = ∑ n ∈ Finset.range N, energy ((n : ℝ) + 1) (psiNat (n + 1)) := by
      apply Finset.sum_congr rfl
      intro n hn
      simpa only [Nat.cast_add, Nat.cast_one] using actual_cell_eq_energy (n + 1)

/-- Exact bridge from the continuous arithmetic energy to the Pareto weights. -/
theorem continuousEnergy_eq_shiftedPareto_add_defect (N : ℕ) :
    continuousEnergy N = shiftedParetoEnergy N + deterministicDefect N := by
  rw [continuousEnergy_sum_cells]
  unfold shiftedParetoEnergy deterministicDefect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  convert energy_complete_square (show 0 < (n : ℝ) + 1 by positivity)
    (psiNat (n + 1)) using 1
  ring

theorem deterministicDefect_nonneg (N : ℕ) : 0 ≤ deterministicDefect N := by
  apply Finset.sum_nonneg
  intro n hn
  exact defect_nonneg (by positivity)

theorem deterministicDefect_le_sum (N : ℕ) :
    deterministicDefect N ≤
      ∑ n ∈ Finset.range N, 1 / (12 * ((n : ℝ) + 1) ^ 2) := by
  apply Finset.sum_le_sum
  intro n hn
  exact defect_le (by positivity)

def paretoKernel (n : ℕ) : ℝ :=
  1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))

theorem paretoKernel_sum (N : ℕ) :
    (∑ n ∈ Finset.range N, paretoKernel n) = 1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [paretoKernel, Nat.cast_succ]
    have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
    have h3 : (N : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp [h1, h2, h3]
    ring

theorem paretoKernel_nonneg (n : ℕ) : 0 ≤ paretoKernel n := by
  unfold paretoKernel
  positivity

theorem paretoKernel_sum_le_one (N : ℕ) :
    (∑ n ∈ Finset.range N, paretoKernel n) ≤ 1 := by
  rw [paretoKernel_sum]
  have h : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
  linarith

private theorem inverse_square_le_kernel (n : ℕ) :
    1 / (12 * ((n : ℝ) + 1) ^ 2) ≤ (1 / 6) * paretoKernel n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : 6 * (((n : ℝ) + 1) * ((n : ℝ) + 2)) ≤
      12 * ((n : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg (n : ℝ)]
  calc
    1 / (12 * ((n : ℝ) + 1) ^ 2) ≤
        1 / (6 * (((n : ℝ) + 1) * ((n : ℝ) + 2))) :=
      one_div_le_one_div_of_le (by positivity) hd
    _ = (1 / 6) * paretoKernel n := by
      unfold paretoKernel
      field_simp

theorem deterministicDefect_le_explicit (N : ℕ) :
    deterministicDefect N ≤ (1 / 6) * (1 - 1 / ((N : ℝ) + 1)) := by
  calc
    deterministicDefect N ≤
        ∑ n ∈ Finset.range N, (1 / 6) * paretoKernel n := by
      apply Finset.sum_le_sum
      intro n hn
      exact (defect_le (show 0 < (n : ℝ) + 1 by positivity)).trans
        (inverse_square_le_kernel n)
    _ = (1 / 6) * (1 - 1 / ((N : ℝ) + 1)) := by
      rw [← Finset.mul_sum, paretoKernel_sum]

theorem deterministicDefect_le_one_sixth (N : ℕ) :
    deterministicDefect N ≤ 1 / 6 := by
  have h := deterministicDefect_le_explicit N
  have hp : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
  linarith

theorem center_shift_sq_le_one (n : ℕ) :
    (center ((n : ℝ) + 1) - ((n : ℝ) + 1)) ^ 2 ≤ 1 := by
  have hm := center_mem (show 0 < (n : ℝ) + 1 by positivity)
  have h0 : 0 ≤ center ((n : ℝ) + 1) - ((n : ℝ) + 1) := by
    linarith [hm.1]
  have h1 : 0 ≤ 1 - (center ((n : ℝ) + 1) - ((n : ℝ) + 1)) := by
    linarith [hm.2]
  nlinarith [mul_nonneg h0 h1]

private theorem square_shift_pair (P a b : ℝ) (h : (b - a) ^ 2 ≤ 1) :
    (P - a) ^ 2 ≤ 2 * (P - b) ^ 2 + 2 ∧
      (P - b) ^ 2 ≤ 2 * (P - a) ^ 2 + 2 := by
  constructor
  · nlinarith [sq_nonneg (P - b - (b - a))]
  · nlinarith [sq_nonneg (P - a + (b - a))]

private theorem weighted_square_sum_le
    (N : ℕ) (f g : ℕ → ℝ)
    (h : ∀ n < N, f n ≤ 2 * g n + 2) :
    (∑ n ∈ Finset.range N, f n * paretoKernel n) ≤
      2 * (∑ n ∈ Finset.range N, g n * paretoKernel n) + 2 := by
  calc
    (∑ n ∈ Finset.range N, f n * paretoKernel n) ≤
        ∑ n ∈ Finset.range N, (2 * g n + 2) * paretoKernel n := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right (h n (Finset.mem_range.mp hn))
        (paretoKernel_nonneg n)
    _ = 2 * (∑ n ∈ Finset.range N, g n * paretoKernel n) +
        2 * (∑ n ∈ Finset.range N, paretoKernel n) := by
      simp_rw [add_mul, mul_assoc]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (∑ n ∈ Finset.range N, g n * paretoKernel n) + 2 := by
      linarith [paretoKernel_sum_le_one N]

theorem paretoEnergy_le_twice_shifted_add_two (N : ℕ) :
    paretoEnergy N ≤ 2 * shiftedParetoEnergy N + 2 := by
  have h := weighted_square_sum_le N
    (fun n => (psiNat (n + 1) - ((n : ℝ) + 1)) ^ 2)
    (fun n => (psiNat (n + 1) - center ((n : ℝ) + 1)) ^ 2)
    (fun n hn => (square_shift_pair _ _ _ (center_shift_sq_le_one n)).1)
  simpa only [paretoEnergy, shiftedParetoEnergy, residual,
    Nat.cast_add, Nat.cast_one, paretoKernel, div_eq_mul_inv, one_mul] using h

theorem shiftedParetoEnergy_le_twice_pareto_add_two (N : ℕ) :
    shiftedParetoEnergy N ≤ 2 * paretoEnergy N + 2 := by
  have h := weighted_square_sum_le N
    (fun n => (psiNat (n + 1) - center ((n : ℝ) + 1)) ^ 2)
    (fun n => (psiNat (n + 1) - ((n : ℝ) + 1)) ^ 2)
    (fun n hn => (square_shift_pair _ _ _ (center_shift_sq_le_one n)).2)
  simpa only [paretoEnergy, shiftedParetoEnergy, residual,
    Nat.cast_add, Nat.cast_one, paretoKernel, div_eq_mul_inv, one_mul] using h

/-- Finite comparison in the direction needed to transfer a discrete upper bound. -/
theorem continuousEnergy_le_twice_pareto_add (N : ℕ) :
    continuousEnergy N ≤ 2 * paretoEnergy N + 13 / 6 := by
  rw [continuousEnergy_eq_shiftedPareto_add_defect]
  linarith [shiftedParetoEnergy_le_twice_pareto_add_two N,
    deterministicDefect_le_one_sixth N]

/-- Finite comparison in the opposite direction. -/
theorem paretoEnergy_le_twice_continuous_add (N : ℕ) :
    paretoEnergy N ≤ 2 * continuousEnergy N + 2 := by
  rw [continuousEnergy_eq_shiftedPareto_add_defect]
  linarith [paretoEnergy_le_twice_shifted_add_two N,
    deterministicDefect_nonneg N]



end RiemannResearch.RH.ChebyshevMidpoint
