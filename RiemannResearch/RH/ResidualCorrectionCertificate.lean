import RiemannResearch.RH.ResidueGramCorrectionPairing

/-!
# Finite signed correction certificates from the missing dual Gram

Prepared from exact projection and coefficient-dual identities, 29 September
2026. This is a finite unconditional strengthening of correction certificates.
It makes no claim that the limiting correction or projection defect vanishes.
All signed cross terms are retained before applying Cauchy--Schwarz.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.GramMobiusCorrection

/-- Testing the optimal residual, rather than the potentially large natural
Möbius residual, gives exactly the same signed correction. -/
theorem correction_eq_neg_optimalResidual_pairing (n : ℕ) (i : Fin n) :
    correction n (i.val + 2) =
      -inner ℝ (hilbertOne - projection n) (dualResidual n i.val) := by
  have ho : inner ℝ (hilbertOne - projection n)
      ((finiteSpace n).starProjection (coefficientDual i.val)) = 0 :=
    Submodule.starProjection_inner_eq_zero hilbertOne _
      ((finiteSpace n).starProjection_apply_mem _)
  rw [dualResidual, inner_sub_right, ho, sub_zero, coefficientDual_inner]
  rw [correction_eq_residual_coordinate n (i.val + 2) (by omega)]
  simp only [coefficientCLM, neg_apply, neg_neg]

/-- Both complete projection defects enter. There is no growing inverse
operator norm or absolute coefficient mass in this finite certificate. -/
theorem correction_sq_le_energy_dual_defect (n : ℕ) (i : Fin n) :
    correction n (i.val + 2) ^ 2 ≤
      energy n * (‖coefficientDual i.val‖ ^ 2 - residueInverseEntry n i i) := by
  rw [correction_eq_neg_optimalResidual_pairing, neg_sq,
    ← residueInverseEntry_diagonal]
  change (inner ℝ (hilbertOne - projection n) (dualResidual n i.val)) ^ 2 ≤
    ‖hilbertOne - projection n‖ ^ 2 * ‖dualResidual n i.val‖ ^ 2
  simpa only [pow_two, real_inner_self_eq_norm_sq] using
    real_inner_mul_inner_self_le (hilbertOne - projection n) (dualResidual n i.val)

/-- The full signed residual dual combination. -/
def signedDualResidual (n : ℕ) (z : Fin n → ℝ) : ThresholdHilbert :=
  ∑ i, z i • dualResidual n i.val

theorem signedDualResidual_pairing (n : ℕ) (z : Fin n → ℝ) :
    inner ℝ (hilbertOne - projection n) (signedDualResidual n z) =
      -(∑ i, z i * correction n (i.val + 2)) := by
  unfold signedDualResidual
  rw [inner_sum]
  simp only [real_inner_smul_right]
  have hp (i : Fin n) :
      inner ℝ (hilbertOne - projection n) (dualResidual n i.val) =
        -correction n (i.val + 2) := by
    have h := correction_eq_neg_optimalResidual_pairing n i
    linarith
  simp only [hp, mul_neg, Finset.sum_neg_distrib]

/-- Exact signed quadratic form of the missing inverse-Gram block. -/
theorem signedDualResidual_norm_sq (n : ℕ) (z : Fin n → ℝ) :
    ‖signedDualResidual n z‖ ^ 2 =
      ∑ i, ∑ j, z i * z j *
        (inner ℝ (coefficientDual i.val) (coefficientDual j.val) -
          residueInverseEntry n i j) := by
  rw [← real_inner_self_eq_norm_sq]
  unfold signedDualResidual
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hg : inner ℝ (dualResidual n i.val) (dualResidual n j.val) =
      inner ℝ (coefficientDual i.val) (coefficientDual j.val) -
        residueInverseEntry n i j := residueInverseEntry_residual n i j
  rw [← hg]
  simp only [real_inner_comm]
  ring

/-- The covariance identity contains the full signed correction row and
every off-diagonal inverse-Gram residual. -/
theorem signed_correction_covariance_exact (n : ℕ) (z : Fin n → ℝ) (t : ℝ) :
    ‖t • (hilbertOne - projection n) + signedDualResidual n z‖ ^ 2 =
      t ^ 2 * energy n - 2 * t * (∑ i, z i * correction n (i.val + 2)) +
        ∑ i, ∑ j, z i * z j *
          (inner ℝ (coefficientDual i.val) (coefficientDual j.val) -
            residueInverseEntry n i j) := by
  rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs,
    real_inner_smul_left, signedDualResidual_pairing,
    signedDualResidual_norm_sq]
  change (|t| * ‖hilbertOne - projection n‖) ^ 2 +
      2 * (t * -(∑ i, z i * correction n (i.val + 2))) +
      (∑ i, ∑ j, z i * z j *
        (inner ℝ (coefficientDual i.val) (coefficientDual j.val) -
          residueInverseEntry n i j)) = _
  rw [mul_pow, sq_abs]
  change t ^ 2 * energy n + _ + _ = _
  ring

/-- Any signed contraction is certified by its own missing-dual energy;
there is no dimension factor and no loss of cancellation within the form. -/
theorem signed_correction_sq_le_energy_dual_form (n : ℕ) (z : Fin n → ℝ) :
    (∑ i, z i * correction n (i.val + 2)) ^ 2 ≤
      energy n *
        (∑ i, ∑ j, z i * z j *
          (inner ℝ (coefficientDual i.val) (coefficientDual j.val) -
            residueInverseEntry n i j)) := by
  have h := real_inner_mul_inner_self_le (hilbertOne - projection n)
    (signedDualResidual n z)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    signedDualResidual_pairing, signedDualResidual_norm_sq] at h
  change _ ≤ ‖hilbertOne - projection n‖ ^ 2 * _
  simpa only [← pow_two, neg_sq] using h

end RiemannResearch.RH.Pareto.CoefficientStabilization.GramMobiusCorrection
