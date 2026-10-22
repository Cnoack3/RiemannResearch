import RiemannResearch.RH.IntegerDPPResidueProbability
import RiemannResearch.RH.ResidueGramDigamma
import Mathlib.NumberTheory.Chebyshev

/-!
# Finite symbolic formula for the actual residue-class probability

Source: user-provided request, September 2026, to express q_N and every
ingredient symbolically from the original definitions.

The modulus is the finite product of prime powers up to N+1. Every Pareto
progression weight is an exact rational-argument digamma difference divided
by that modulus. Periodic regrouping gives all full Gram entries explicitly.
Diagonal rescaling removes the conductor normalizations from the determinant
ratio, and the final theorem expands both determinants by the Leibniz formula.

The final expression uses only finite sums/products, natural remainders, and
specified Gamma logarithmic derivatives. Its denominator is proved positive
for every N. No recurrence, entry/loss sequence, limiting saturation premise,
or numerical approximation is used in the final formula.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization CoefficientStabilization.TailCapacity


private theorem residueModulus_dvd_of_conductors (N m : ℕ)
    (h : ∀ k < N, k + 2 ∣ m) : residueModulus N ∣ m := by
  revert h
  induction N with
  | zero => intro h; exact one_dvd m
  | succ N ih =>
    intro h
    exact Nat.lcm_dvd (ih (fun k hk => h k (by omega))) (h N (by omega))

theorem residueModulus_eq_lcmUpto (N : ℕ) :
    residueModulus N = (N + 1).lcmUpto := by
  change residueModulus N = (Finset.Icc 1 (N + 1)).lcm id
  apply Nat.dvd_antisymm
  · apply residueModulus_dvd_of_conductors
    intro k hk
    exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  · apply Finset.lcm_dvd
    intro k hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
    by_cases he : k = 1
    · simpa only [he, id_eq] using one_dvd (residueModulus N)
    have hk2 : 2 ≤ k := by omega
    simpa only [id_eq, Nat.sub_add_cancel hk2] using
      conductor_dvd_residueModulus N (k - 2) (by omega)

theorem residueModulus_eq_prime_product (N : ℕ) :
    residueModulus N = ∏ p ∈ (N + 1).primesLE, p ^ Nat.log p (N + 1) := by
  rw [residueModulus_eq_lcmUpto, Nat.lcmUpto_eq_prod_pow_log]

theorem residueModulus_factorization (N p : ℕ) (hp : Nat.Prime p) :
    (residueModulus N).factorization p = Nat.log p (N + 1) := by
  rw [residueModulus_eq_lcmUpto]
  exact Nat.factorization_lcmUpto _ hp

/-- Exact digamma difference at rational arguments. -/
def residueDigammaDifference (L r : ℕ) : ℝ :=
  (Complex.digamma ((((r : ℝ) + 1) / (L : ℝ) : ℝ) : ℂ)).re -
    (Complex.digamma (((r : ℝ) / (L : ℝ) : ℝ) : ℂ)).re

theorem residueDigammaDifference_eq_gamma_quotients (L r : ℕ) :
    residueDigammaDifference L r =
      (deriv Complex.Gamma ((((r : ℝ) + 1) / (L : ℝ) : ℝ) : ℂ) /
        Complex.Gamma ((((r : ℝ) + 1) / (L : ℝ) : ℝ) : ℂ)).re -
      (deriv Complex.Gamma (((r : ℝ) / (L : ℝ) : ℝ) : ℂ) /
        Complex.Gamma (((r : ℝ) / (L : ℝ) : ℝ) : ℂ)).re := rfl

/-- A finite matrix involving only natural remainders and fixed special values. -/
def remainderDigammaMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ∑ r : Fin (residueModulus N),
    (((r.val+1) % (i.val+2) : ℕ) : ℝ) *
    (((r.val+1) % (j.val+2) : ℕ) : ℝ) *
    residueDigammaDifference (residueModulus N) (r.val+1)

def conductorDiagonal (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i => ((i.val+2 : ℕ) : ℝ))

theorem progressionWeight_eq_residueDigammaDifference (L r : ℕ)
    (hL : 0 < L) (hr : 0 < r) (hrL : r ≤ L) :
    progressionWeight L r = residueDigammaDifference L r / (L : ℝ) := by
  rw [progressionWeight_eq_digamma L r hL hr hrL]
  unfold residueDigammaDifference
  ring

theorem fullGram_entry_eq_remainderDigamma (N : ℕ) (i j : Fin N) :
    fullGram N i j = remainderDigammaMatrix N i j /
      (((i.val+2 : ℕ) : ℝ) * ((j.val+2 : ℕ) : ℝ) * (residueModulus N : ℝ)) := by
  change inner ℝ (normalizedResidueHilbert (i.val+2) _)
    (normalizedResidueHilbert (j.val+2) _) = _
  rw [normalizedResidueHilbert_inner,
    periodic_paretoInner_mixed (residueModulus N) (residueModulus_pos N)
      (residue (i.val+2)) (residue (j.val+2))
      (fun k => residue_abs_le _ k (by omega))
      (fun k => residue_abs_le _ k (by omega))
      (residue_period_of_dvd (conductor_dvd_residueModulus N i.val i.isLt))
      (residue_period_of_dvd (conductor_dvd_residueModulus N j.val j.isLt))]
  unfold remainderDigammaMatrix
  rw [Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r hr
  rw [progressionWeight_eq_residueDigammaDifference _ _ (residueModulus_pos N)
    (by omega) (by omega)]
  simp only [residue, div_eq_mul_inv, mul_inv_rev]
  ring

theorem remainderDigammaMatrix_eq_scaled_gram (N : ℕ) :
    remainderDigammaMatrix N = (residueModulus N : ℝ) •
      (conductorDiagonal N * fullGram N * conductorDiagonal N) := by
  ext i j
  simp only [conductorDiagonal, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [fullGram_entry_eq_remainderDigamma]
  have hi : ((i.val+2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hj : ((j.val+2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hL : (residueModulus N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (residueModulus_pos N))
  field_simp

theorem conductorDiagonal_det_pos (N : ℕ) : 0 < (conductorDiagonal N).det := by
  rw [conductorDiagonal, Matrix.det_diagonal]
  exact Finset.prod_pos (fun i hi => by positivity)

theorem remainderDigammaMatrix_det (N : ℕ) :
    (remainderDigammaMatrix N).det =
      (residueModulus N : ℝ)^N * (conductorDiagonal N).det^2 * (fullGram N).det := by
  rw [remainderDigammaMatrix_eq_scaled_gram, Matrix.det_smul,
    Matrix.det_mul, Matrix.det_mul]
  simp only [Fintype.card_fin]
  ring

theorem remainderDigammaMatrix_det_pos (N : ℕ) :
    0 < (remainderDigammaMatrix N).det := by
  rw [remainderDigammaMatrix_det]
  exact mul_pos
    (mul_pos (pow_pos (by exact_mod_cast residueModulus_pos N) _)
      (sq_pos_of_pos (conductorDiagonal_det_pos N))) (fullGram_det_pos N)

def firstClassRemovedMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => remainderDigammaMatrix N i j - residueDigammaDifference (residueModulus N) 1

theorem firstClassRemovedMatrix_eq_scaled (N : ℕ) :
    firstClassRemovedMatrix N = (residueModulus N : ℝ) •
      (conductorDiagonal N *
        (fullGram N - progressionWeight (residueModulus N) 1 •
          Matrix.vecMulVec (reciprocalSource N) (reciprocalSource N)) *
        conductorDiagonal N) := by
  ext i j
  simp only [firstClassRemovedMatrix, conductorDiagonal, Matrix.smul_apply,
    smul_eq_mul, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.sub_apply,
    Matrix.vecMulVec_apply, reciprocalSource]
  rw [fullGram_entry_eq_remainderDigamma,
    progressionWeight_eq_residueDigammaDifference _ _ (residueModulus_pos N)
      (by omega) (residueModulus_pos N)]
  have hi : ((i.val+2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hj : ((j.val+2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hL : (residueModulus N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (residueModulus_pos N))
  field_simp

theorem qN_eq_symbolic_determinant_ratio (N : ℕ) :
    qN N = 1 - (firstClassRemovedMatrix N).det / (remainderDigammaMatrix N).det := by
  rw [qN_eq_determinant_ratio, firstClassRemovedMatrix_eq_scaled,
    remainderDigammaMatrix_eq_scaled_gram]
  simp only [Matrix.det_smul, Matrix.det_mul, Fintype.card_fin]
  have hL : (residueModulus N : ℝ)^N ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (ne_of_gt (residueModulus_pos N)))
  have hD : (conductorDiagonal N).det ≠ 0 := ne_of_gt (conductorDiagonal_det_pos N)
  have hG : (fullGram N).det ≠ 0 := ne_of_gt (fullGram_det_pos N)
  field_simp


/-- Leibniz expansion: all entries are the explicit finite remainder sums. -/
def residueDeterminantPolynomial (N : ℕ) (t : ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin N), Equiv.Perm.sign σ •
    ∏ i : Fin N, (remainderDigammaMatrix N (σ i) i - t)

theorem residueDeterminantPolynomial_eq_det (N : ℕ) (t : ℝ) :
    residueDeterminantPolynomial N t =
      Matrix.det (Matrix.of (fun i j : Fin N => remainderDigammaMatrix N i j - t)) := by
  exact (Matrix.det_apply
    (Matrix.of (fun i j : Fin N => remainderDigammaMatrix N i j - t))).symm

theorem residueDeterminantPolynomial_zero (N : ℕ) :
    residueDeterminantPolynomial N 0 = (remainderDigammaMatrix N).det := by
  rw [residueDeterminantPolynomial_eq_det]
  congr 1
  ext i j
  simp only [Matrix.of_apply, sub_zero]

theorem residueDeterminantPolynomial_zero_pos (N : ℕ) :
    0 < residueDeterminantPolynomial N 0 := by
  rw [residueDeterminantPolynomial_zero]
  exact remainderDigammaMatrix_det_pos N

/-- Closed finite symbolic formula; no capacities, modes, or recurrence terms remain. -/
theorem qN_eq_finite_symbolic_formula (N : ℕ) :
    qN N = 1 -
      residueDeterminantPolynomial N (residueDigammaDifference (residueModulus N) 1) /
      residueDeterminantPolynomial N 0 := by
  rw [qN_eq_symbolic_determinant_ratio, residueDeterminantPolynomial_zero,
    residueDeterminantPolynomial_eq_det]
  rfl


end RiemannResearch.RH.Pareto.IntegerDPP
