import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity

/-!
Source: user-supplied `Zeta_Zero_Harmonic_Analysis_20261011 (1)(1).md`, Section 5.
These finite deductions make no publication-priority claim.

# Exact finite balanced tuple phase sums

All tuple indices are ordered. Every repeated sample index and every
diagonal pair is retained. These identities hold for arbitrary finite
complex samples and have no zeta-zero distribution assumption.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.BalancedTuplePhase

variable {ι : Type*} [Fintype ι]

/-- A product along an ordered tuple, permitting repeated sample indices. -/
def tupleAmplitude (r : ℕ) (z : ι → ℂ) (t : Fin r → ι) : ℂ :=
  ∏ j : Fin r, z (t j)

/-- Sum over every ordered tuple, including all repetitions. -/
theorem tupleAmplitude_sum (r : ℕ) (z : ι → ℂ) :
    (∑ t : Fin r → ι, tupleAmplitude r z t) = (∑ i, z i) ^ r := by
  classical
  unfold tupleAmplitude
  rw [← Fintype.prod_sum (fun (_ : Fin r) (i : ι) => z i)]
  simp

/-- The raw balanced 2r-fold sum over all ordered tuple pairs. -/
def balancedTupleSum (r : ℕ) (z : ι → ℂ) : ℂ :=
  ∑ t : (Fin r → ι) × (Fin r → ι),
    tupleAmplitude r z t.1 * star (tupleAmplitude r z t.2)

/-- Exact balanced tuple factorization before replacing any term by a norm. -/
theorem balancedTupleSum_factorization (r : ℕ) (z : ι → ℂ) :
    balancedTupleSum r z =
      (∑ i, z i) ^ r * star ((∑ i, z i) ^ r) := by
  classical
  unfold balancedTupleSum
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, ← star_sum,
    tupleAmplitude_sum]

/-- Every balanced hierarchy level is an exact even power of one Fourier sum. -/
theorem balancedTupleSum_eq_norm_pow (r : ℕ) (z : ι → ℂ) :
    balancedTupleSum r z = ((‖∑ i, z i‖ ^ (2 * r) : ℝ) : ℂ) := by
  rw [balancedTupleSum_factorization]
  calc
    (∑ i, z i) ^ r * star ((∑ i, z i) ^ r) =
        ((‖(∑ i, z i) ^ r‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.sq_norm]
      exact Complex.mul_conj ((∑ i, z i) ^ r)
    _ = ((‖∑ i, z i‖ ^ (2 * r) : ℝ) : ℂ) := by
      rw [norm_pow, ← pow_mul, Nat.mul_comm r 2]

/-- Balanced Fourier coefficients are real without any limiting argument. -/
theorem balancedTupleSum_im (r : ℕ) (z : ι → ℂ) :
    (balancedTupleSum r z).im = 0 := by
  rw [balancedTupleSum_eq_norm_pow]
  rfl

/-- Balanced Fourier coefficients are nonnegative without a sampling theorem. -/
theorem balancedTupleSum_re_nonneg (r : ℕ) (z : ι → ℂ) :
    0 ≤ (balancedTupleSum r z).re := by
  rw [balancedTupleSum_eq_norm_pow]
  simp only [Complex.ofReal_re]
  positivity

/-- The normalized balanced sum, with the original finite sample count. -/
def balancedTupleMean (r : ℕ) (z : ι → ℂ) : ℂ :=
  balancedTupleSum r z / (Fintype.card ι : ℂ) ^ (2 * r)

/-- Exact normalized hierarchy; no nonemptiness assumption is needed for the
algebraic identity because division by zero uses Lean's field convention. -/
theorem balancedTupleMean_eq_norm_pow (r : ℕ) (z : ι → ℂ) :
    balancedTupleMean r z =
      ((‖∑ i, z i‖ / (Fintype.card ι : ℝ)) ^ (2 * r) : ℝ) := by
  unfold balancedTupleMean
  rw [balancedTupleSum_eq_norm_pow, div_pow]
  simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]

end RiemannResearch.Analysis.BalancedTuplePhase
