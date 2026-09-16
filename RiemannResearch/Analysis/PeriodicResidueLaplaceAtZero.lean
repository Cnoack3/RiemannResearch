import RiemannResearch.Analysis.PeriodicResidueLaplace
import RiemannResearch.Analysis.FiniteResidueCharge
import Mathlib.Tactic.FunProp

/-! Exact removable value and continuity of the finite periodic Laplace
average. Source: user-provided finite residue average, Section 9 of
`RH_Coupled_Residual_Corrections_2026-09-16.md`. No Taylor-order claim. -/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteResidueCharge

private theorem weightedGeometricSum_one (n : ℕ) :
    weightedGeometricSum 1 n = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp [weightedGeometricSum]
  | succ n ih =>
    change (∑ j ∈ Finset.range (n + 1), (j : ℝ) * (1 : ℝ) ^ j) = _
    rw [Finset.sum_range_succ]
    change weightedGeometricSum 1 n + (n : ℝ) * 1 ^ n = _
    rw [ih, Nat.cast_succ, one_pow, mul_one]
    ring

private theorem sum_residue_common_period (n L : ℕ) (hn : 0 < n) (hdiv : n ∣ L) :
    (∑ j ∈ Finset.range L, ((j % n : ℕ) : ℝ)) = ((n : ℝ) - 1) / 2 * L := by
  obtain ⟨k, hk⟩ := hdiv
  have h := periodicResidueSum_block_identity 1 n k
  rw [show k * n = L by simpa [Nat.mul_comm] using hk.symm] at h
  simp only [periodicResidueSum, geometricSum, one_pow, mul_one,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, weightedGeometricSum_one] at h
  apply mul_right_cancel₀ (show (n : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hn))
  calc
    (∑ j ∈ Finset.range L, ((j % n : ℕ) : ℝ)) * n =
        (n : ℝ) * ((n : ℝ) - 1) / 2 * L := h
    _ = _ := by ring

variable {ι : Type*} [Fintype ι]

theorem periodicLaplaceAverage_zero (b : ι → ℝ) (n : ι → ℕ)
    (L : ℕ) (hL : 0 < L) (hn : ∀ i, 0 < n i) (hdiv : ∀ i, n i ∣ L)
    (hzero : ∑ i, b i = 0) :
    periodicLaplaceAverage b n 0 L = constantTerm b (fun i => (n i : ℝ)) := by
  classical
  have hLc : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  unfold periodicLaplaceAverage constantTerm
  simp only [mul_zero, neg_zero, Real.exp_zero, mul_one, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_residue_common_period _ L (hn _) (hdiv _)]
  have hterm (i : ι) : b i * (((n i : ℝ) - 1) / 2 * L) =
      ((L : ℝ) / 2) * (b i * (n i : ℝ) - b i) := by ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, hzero, sub_zero]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  field_simp [hLc]

/-- The finite quotient is continuous at zero because its denominator there
is the positive period. The poles in the alternate formula are removable. -/
theorem continuousAt_periodicLaplaceAverage_zero (b : ι → ℝ) (n : ι → ℕ)
    (L : ℕ) (hL : 0 < L) :
    ContinuousAt (fun t => periodicLaplaceAverage b n t L) 0 := by
  unfold periodicLaplaceAverage
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · simp [Nat.ne_of_gt hL]

end RiemannResearch.Analysis.FiniteResidueCharge
