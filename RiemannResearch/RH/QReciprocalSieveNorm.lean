import RiemannResearch.RH.QReciprocalFullDensity
import RiemannResearch.RH.NearbyDilationGram

/-!
# The complete Pareto norm of the reciprocal floor atom

This verifies the original estimate used for absolutely summable Möbius
inversion: the physical function F_m(n)=floor(n/m)/n vanishes for n<m and
lies between 0 and 1/m. The exact Pareto mass of the remaining full tail
is 1/m. Hence the square of its norm is at most 1/m^3.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QReciprocalSieveNorm
open ZetaTwoHilbert ZetaTwoParetoTransfer Pareto QReciprocalFullDensity

/-- A complete Pareto tail estimate for a bounded physical sequence vanishing before M. -/
theorem pareto_norm_sq_le_of_tail_bound
    (f : QHilbert) (M : ℕ) (hM : 0 < M) (C : ℝ) (hC : 0 ≤ C)
    (hz : ∀ n, n < M → qSequence f n = 0)
    (hb : ∀ n, M ≤ n → |qSequence f n| ≤ C) :
    ‖toPareto f‖^2 ≤ C^2 / (M : ℝ) := by
  have hs := hilbertSequence_square_summable (toPareto f)
  rw [toPareto_sequence] at hs
  have hprefix : (∑ n ∈ Finset.range M, positiveWeight n * (qSequence f n)^2) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [hz n (Finset.mem_range.mp hn)]
  have he := hs.sum_add_tsum_nat_add M
  rw [hprefix, zero_add] at he
  have htail := (summable_nat_add_iff M).mpr hs
  have hw := (summable_nat_add_iff M).mpr positiveWeight_summable
  calc
    ‖toPareto f‖^2 = ∑' n, positiveWeight (n+M) * (qSequence f (n+M))^2 := by
      rw [hilbert_norm_weighted_sq, toPareto_sequence]
      exact he.symm
    _ ≤ ∑' n, positiveWeight (n+M) * C^2 := by
      apply htail.tsum_le_tsum _ (hw.mul_right _)
      intro n
      apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg _)
      have h := hb (n+M) (by omega)
      simpa only [← pow_two, sq_abs] using
        mul_le_mul h h (abs_nonneg _) hC
    _ = C^2 / (M : ℝ) := by
      rw [hw.tsum_mul_right, positiveWeight_tail_tsum M hM]
      ring

theorem floorAtom_bounds (m : ℕ) (hm : 0 < m) (n : ℕ) :
    0 ≤ qSequence (floorAtom m) n ∧ qSequence (floorAtom m) n ≤ 1 / (m : ℝ) := by
  simpa [factorialSieve] using factorialSieve_bounds 0 m hm n

/-- The original absolute-convergence proof uses this complete, unconditional norm bound. -/
theorem floorAtom_pareto_norm_sq_le (m : ℕ) (hm : 0 < m) :
    ‖toPareto (floorAtom m)‖^2 ≤ 1 / (m : ℝ)^3 := by
  calc
    ‖toPareto (floorAtom m)‖^2 ≤ (1 / (m : ℝ))^2 / (m : ℝ) := by
      apply pareto_norm_sq_le_of_tail_bound _ m hm _ (by positivity)
      · intro n hn
        simp [floorAtom_sequence m hm n, Nat.div_eq_of_lt hn]
      · intro n hn
        rw [abs_of_nonneg (floorAtom_bounds m hm n).1]
        exact (floorAtom_bounds m hm n).2
    _ = 1 / (m : ℝ)^3 := by ring

theorem floorAtom_pareto_norm_le (m : ℕ) (hm : 0 < m) :
    ‖toPareto (floorAtom m)‖ ≤ 1 / ((m : ℝ) * Real.sqrt (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : (Real.sqrt (m : ℝ))^2 = m := Real.sq_sqrt hmR.le
  have hden : 0 ≤ 1 / ((m : ℝ) * Real.sqrt (m : ℝ)) := by positivity
  have hsq : (1 / ((m : ℝ) * Real.sqrt (m : ℝ)))^2 = 1 / (m : ℝ)^3 := by
    rw [div_pow, mul_pow, hs]
    ring
  have h := floorAtom_pareto_norm_sq_le m hm
  rw [← hsq] at h
  nlinarith [norm_nonneg (toPareto (floorAtom m))]


/-- The same complete norm estimate in the original exponent notation. -/
theorem floorAtom_pareto_norm_le_rpow (m : ℕ) (hm : 0 < m) :
    ‖toPareto (floorAtom m)‖ ≤ (m : ℝ)^(-(3/2 : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have he : (m : ℝ)^(-(3/2 : ℝ)) = 1 / ((m : ℝ) * Real.sqrt (m : ℝ)) := by
    rw [show -(3/2 : ℝ) = -(1 + 1/2 : ℝ) by norm_num,
      Real.rpow_neg hmR.le, Real.rpow_add hmR, Real.rpow_one, ← Real.sqrt_eq_rpow]
    simp only [one_div]
  rw [he]
  exact floorAtom_pareto_norm_le m hm

end RiemannResearch.RH.QReciprocalSieveNorm
