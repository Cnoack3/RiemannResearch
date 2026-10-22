import RiemannResearch.RH.ParetoGeometricEnergy
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The exact normalized Hankel matrix of the Pareto Gibbs kernel

Source: RH_Contracting_Evolution_and_Arithmetic_Repair_2026-09-08.md;
Kalvoda and Šťovíček, arXiv:1506.01064, equation (3), at (a,b,c)=(1,1,3).
The citation identifies the classical matrix family.  This module proves the
normalization, the full ground-state row sums, positivity, and the exact finite
section energy identity.  It does not assume or prove their spectral theorem.
All indices are shifted: n represents the physical positive integer n+1.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- Inverse square root of the physical Pareto mass. -/
def hankelScale (n : ℕ) : ℝ :=
  Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2))

/-- The symmetric matrix obtained by passing to unweighted l2 coordinates. -/
def normalizedGibbsHankel (n m : ℕ) : ℝ :=
  hankelScale n * geometricKernel n m * hankelScale m

/-- The normalized vector corresponding to the physical constant function. -/
def hankelGround (n : ℕ) : ℝ := 1 / hankelScale n

theorem hankelScale_pos (n : ℕ) : 0 < hankelScale n := by
  unfold hankelScale
  positivity

theorem hankelScale_ne_zero (n : ℕ) : hankelScale n ≠ 0 :=
  ne_of_gt (hankelScale_pos n)

theorem hankelScale_sq (n : ℕ) :
    hankelScale n ^ 2 = ((n : ℝ) + 1) * ((n : ℝ) + 2) := by
  exact Real.sq_sqrt (by positivity)

theorem paretoWeight_mul_hankelScale_sq (n : ℕ) :
    paretoWeight n * hankelScale n ^ 2 = 1 := by
  rw [hankelScale_sq]
  unfold paretoWeight
  have hn : ((n : ℝ) + 1) * ((n : ℝ) + 2) ≠ 0 := by positivity
  field_simp

theorem hankelGround_eq_sqrt_weight (n : ℕ) :
    hankelGround n = Real.sqrt (paretoWeight n) := by
  apply (sq_eq_sq₀ (by unfold hankelGround; exact div_nonneg zero_le_one (hankelScale_pos n).le)
    (Real.sqrt_nonneg (paretoWeight n))).mp
  rw [Real.sq_sqrt (paretoWeight_pos n).le]
  unfold hankelGround
  rw [div_pow, hankelScale_sq]
  simp [paretoWeight]

theorem hankelGround_sq (n : ℕ) : hankelGround n ^ 2 = paretoWeight n := by
  rw [hankelGround_eq_sqrt_weight, Real.sq_sqrt (paretoWeight_pos n).le]

/-- The physical constant is an actual unit vector, with its whole infinite norm. -/
theorem hankelGround_square_hasSum : HasSum (fun n => hankelGround n ^ 2) 1 := by
  simpa only [hankelGround_sq] using paretoWeight_hasSum

theorem hankelGround_square_tsum : (∑' n, hankelGround n ^ 2) = 1 :=
  hankelGround_square_hasSum.tsum_eq

theorem normalizedGibbsHankel_symm (n m : ℕ) :
    normalizedGibbsHankel n m = normalizedGibbsHankel m n := by
  unfold normalizedGibbsHankel
  rw [geometricKernel_symm]
  ring

theorem normalizedGibbsHankel_pos (n m : ℕ) : 0 < normalizedGibbsHankel n m :=
  mul_pos (mul_pos (hankelScale_pos n) (geometricKernel_pos n m)) (hankelScale_pos m)

/-- This is exactly the elementary specialization of 2B(1,1,3). -/
theorem normalizedGibbsHankel_explicit (n m : ℕ) :
    normalizedGibbsHankel n m =
      2 * Real.sqrt ((((n : ℝ) + 1) * ((n : ℝ) + 2)) *
        (((m : ℝ) + 1) * ((m : ℝ) + 2))) /
      (((n : ℝ) + m + 1) * ((n : ℝ) + m + 2) * ((n : ℝ) + m + 3)) := by
  rw [Real.sqrt_mul (by positivity)]
  unfold normalizedGibbsHankel hankelScale geometricKernel
  ring

theorem paretoWeight_eq_inv_hankelScale_sq (n : ℕ) :
    paretoWeight n = 1 / hankelScale n ^ 2 := by
  apply (eq_div_iff (pow_ne_zero 2 (hankelScale_ne_zero n))).2
  exact paretoWeight_mul_hankelScale_sq n

/-- Entrywise conjugation of the actual stochastic kernel by sqrt(w).
This is a proved coordinate identity, not an assumed unitary equivalence. -/
theorem normalizedGibbsHankel_conjugation (n m : ℕ) :
    Real.sqrt (paretoWeight n) * (geometricKernel n m / paretoWeight n) /
      Real.sqrt (paretoWeight m) = normalizedGibbsHankel n m := by
  rw [← hankelGround_eq_sqrt_weight, ← hankelGround_eq_sqrt_weight]
  unfold hankelGround normalizedGibbsHankel
  rw [paretoWeight_eq_inv_hankelScale_sq]
  field_simp [hankelScale_ne_zero]

theorem normalizedGibbsHankel_ground_term (n m : ℕ) :
    normalizedGibbsHankel n m * hankelGround m =
      hankelScale n * geometricKernel n m := by
  unfold normalizedGibbsHankel hankelGround
  field_simp [hankelScale_ne_zero]

theorem hankelScale_mul_weight (n : ℕ) :
    hankelScale n * paretoWeight n = hankelGround n := by
  unfold hankelGround
  apply (eq_div_iff (hankelScale_ne_zero n)).2
  nlinarith [paretoWeight_mul_hankelScale_sq n]

/-- The eigenvector identity is established by an infinite convergent row sum. -/
theorem normalizedGibbsHankel_ground_hasSum (n : ℕ) :
    HasSum (fun m => normalizedGibbsHankel n m * hankelGround m) (hankelGround n) := by
  simpa only [normalizedGibbsHankel_ground_term, hankelScale_mul_weight] using
    (geometricKernel_hasSum n).mul_left (hankelScale n)

theorem normalizedGibbsHankel_ground_tsum (n : ℕ) :
    (∑' m, normalizedGibbsHankel n m * hankelGround m) = hankelGround n :=
  (normalizedGibbsHankel_ground_hasSum n).tsum_eq

private theorem hankel_weighted_square (n : ℕ) (v : ℝ) :
    paretoWeight n * (hankelScale n * v) ^ 2 = v ^ 2 := by
  calc
    _ = (paretoWeight n * hankelScale n ^ 2) * v ^ 2 := by ring
    _ = _ := by rw [paretoWeight_mul_hankelScale_sq, one_mul]

private theorem hankel_cross (n m : ℕ) (v z : ℝ) :
    (hankelScale n * v) * (hankelScale m * z) * geometricKernel n m =
      v * z * normalizedGibbsHankel n m := by
  unfold normalizedGibbsHankel
  ring

/-- Every finite section is positive, inherited from the actual beta integral. -/
theorem normalizedGibbsHankel_positive_semidefinite (s : Finset ℕ) (v : ℕ → ℝ) :
    0 ≤ ∑ n ∈ s, ∑ m ∈ s, v n * v m * normalizedGibbsHankel n m := by
  simpa only [hankel_cross] using
    geometricKernel_positive_semidefinite s (fun n => hankelScale n * v n)

/-- Exact finite-section energy.  The tail of every row remains explicitly present. -/
theorem normalizedGibbsHankel_cutoff_energy (N : ℕ) (v : ℕ → ℝ) :
    (∑ n ∈ Finset.range N, v n ^ 2) -
      (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        v n * v m * normalizedGibbsHankel n m) =
      (1 / 2 : ℝ) * (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        geometricKernel n m * (hankelScale n * v n - hankelScale m * v m) ^ 2) +
      ∑ n ∈ Finset.range N, paretoWeight (n + N) * (hankelScale n * v n) ^ 2 := by
  simpa only [hankel_weighted_square, hankel_cross] using
    geometricKernel_cutoff_energy_identity N (fun n => hankelScale n * v n)

/-- Each finite quadratic form is bounded by the actual unweighted l2 norm. -/
theorem normalizedGibbsHankel_cutoff_gram_le (N : ℕ) (v : ℕ → ℝ) :
    (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      v n * v m * normalizedGibbsHankel n m) ≤ ∑ n ∈ Finset.range N, v n ^ 2 := by
  simpa only [hankel_weighted_square, hankel_cross] using
    geometricKernel_cutoff_gram_le N (fun n => hankelScale n * v n)

end
end RiemannResearch.RH.Pareto
