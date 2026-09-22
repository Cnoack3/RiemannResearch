import RiemannResearch.RH.ResidueGramMobiusCorrection
import RiemannResearch.RH.ResidueGramDigamma

/-!
# Canonical full-Pareto projection and exact Schur recursion

Source: the user's Pareto projection and Schur formulas, 22 September 2026.
This module assembles the existing inverse-Gram and exact digamma results
with the full-norm variational and adjoining-generator identities.

Stage n spans g₂,...,g_(n+1). Thus manuscript cutoff N is stage N-1,
and its adjoining-generator Schur data have index N-2. No tail truncation
of the Pareto norm occurs. The decimal table is documented separately;
it is not asserted as an exact Lean equality.

The imported GramMobiusCorrection module supplies c=G⁻¹b and its Möbius
decomposition. These finite-stage identities assume no limiting saturation.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.ProjectionSchur
open RiemannResearch.Analysis.FiniteHilbertGram
open TailCapacity IntegerDPP GramMobiusCorrection

/-- The complete captured energy bᵀG⁻¹b. -/
def captured (n : ℕ) : ℝ := dotProduct (source n) (canonicalVector n)

theorem canonical_eq_inverseCoeff (n : ℕ) :
    canonicalVector n = inverseCoeff (finiteAtom_independent n) hilbertOne := by
  rw [canonicalVector, fullGram, gramMatrix_inverseSource]
  rfl

theorem error_eq_one_sub_captured (n : ℕ) :
    ‖hilbertOne - projection n‖ ^ 2 = 1 - captured n := by
  have h := residual_schur_value (finiteAtom_independent n) hilbertOne
  rw [synthesis_inverseCoeff_eq_projection, hilbertOne_norm_sq] at h
  change ‖hilbertOne - projection n‖ ^ 2 = _ at h
  simpa only [captured, dotProduct, canonical_eq_inverseCoeff, source, mul_comm] using h

/-- Completing the square in the entire infinite Pareto norm. -/
theorem canonical_completion (n : ℕ) (x : Fin n → ℝ) :
    ‖hilbertOne - ∑ i : Fin n, x i • residueAtom i.val‖ ^ 2 =
      1 - captured n +
        ‖∑ i : Fin n, (x i - canonicalVector n i) • residueAtom i.val‖ ^ 2 := by
  have h := residual_completion (finiteAtom_independent n) hilbertOne x
  rw [residual_schur_value] at h
  simpa only [Fintype.linearCombination_apply, Pi.sub_apply,
    ← canonical_eq_inverseCoeff, hilbertOne_norm_sq,
    captured, dotProduct, source, mul_comm] using h

theorem canonical_minimizes (n : ℕ) (x : Fin n → ℝ) :
    ‖hilbertOne - projection n‖ ^ 2 ≤
      ‖hilbertOne - ∑ i : Fin n, x i • residueAtom i.val‖ ^ 2 := by
  rw [error_eq_one_sub_captured, canonical_completion]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Equality with the optimal error forces equality of every coefficient. -/
theorem canonical_unique (n : ℕ) (x : Fin n → ℝ)
    (hx : ‖hilbertOne - ∑ i : Fin n, x i • residueAtom i.val‖ ^ 2 =
      ‖hilbertOne - projection n‖ ^ 2) :
    x = canonicalVector n := by
  rw [canonical_eq_inverseCoeff]
  apply residual_minimizer_unique (finiteAtom_independent n) hilbertOne x
  rw [error_eq_one_sub_captured] at hx
  simpa only [Fintype.linearCombination_apply, captured, dotProduct,
    canonical_eq_inverseCoeff, source, hilbertOne_norm_sq, mul_comm] using hx

theorem captured_eq_norm_sq (n : ℕ) : captured n = ‖projection n‖ ^ 2 := by
  symm
  have h := projection_inner_eq_inverseGram (finiteAtom_independent n) hilbertOne hilbertOne
  change inner ℝ (projection n) (projection n) = captured n at h
  simpa only [real_inner_self_eq_norm_sq] using h

theorem projection_succ_mode (n : ℕ) :
    projection (n + 1) = projection n + modeAlpha n • residueMode n := by
  rw [projection_eq_mode_sum, Fin.sum_univ_castSucc, projection_eq_mode_sum]
  rfl

theorem captured_succ_mode (n : ℕ) :
    captured (n + 1) = captured n + (modeAlpha n) ^ 2 := by
  have h0 := energy_eq_one_sub_mode_sum n
  have h1 := energy_eq_one_sub_mode_sum (n + 1)
  have e0 := error_eq_one_sub_captured n
  have e1 := error_eq_one_sub_captured (n + 1)
  change energy n = _ at e0
  change energy (n + 1) = _ at e1
  rw [Fin.sum_univ_castSucc] at h1
  simp only [Fin.val_castSucc, Fin.val_last] at h1
  linarith

theorem energy_one : energy 1 = 1 - Real.log 2 := by
  rw [energy_eq_one_sub_mode_sum]
  simp [modeAlpha_zero, Real.sq_sqrt (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))]

private theorem project_modes (n : ℕ) (x : ThresholdHilbert) :
    (finiteSpace n).starProjection x =
      ∑ i : Fin n, inner ℝ (residueMode i.val) x • residueMode i.val := by
  have hn : Orthonormal ℝ (fun i : Fin n => residueMode i.val) :=
    residueMode_orthonormal.comp (fun i : Fin n => i.val) Fin.val_injective
  simpa only [residueMode_finiteSpace] using projection_eq_orthonormal_sum hn x

/-- Cross-Gram column for adjoining conductor n+2 to the first n atoms. -/
def coupling (n : ℕ) : Fin n → ℝ :=
  cross (fun i : Fin n => residueAtom i.val) (residueAtom n)

/-- The inverse-Gram coefficients of the old-span projection of the new atom. -/
def eliminated (n : ℕ) : Fin n → ℝ := (fullGram n)⁻¹.mulVec (coupling n)

/-- The part of the new atom orthogonal to the old finite span. -/
def innovation (n : ℕ) : ThresholdHilbert :=
  residueAtom n - (finiteSpace n).starProjection (residueAtom n)

def schurSigma (n : ℕ) : ℝ := ‖innovation n‖ ^ 2

def schurEta (n : ℕ) : ℝ := inner ℝ (innovation n) hilbertOne

theorem innovation_eq_scale_mode (n : ℕ) :
    innovation n = residueModeScale n • residueMode n := by
  have hm : residueAtom n ∈ finiteSpace (n + 1) := by
    change residueAtom n ∈ synthesisSpan (fun i : Fin (n+1) => residueAtom i.val)
    exact Submodule.subset_span ⟨Fin.last n, rfl⟩
  have h := project_modes (n + 1) (residueAtom n)
  rw [Submodule.starProjection_eq_self_iff.mpr hm, Fin.sum_univ_castSucc] at h
  simp only [Fin.val_castSucc, Fin.val_last] at h
  rw [← project_modes n (residueAtom n)] at h
  have hl : inner ℝ (residueMode n) (residueAtom n) = residueModeScale n := by
    rw [real_inner_comm, residueAtom_inner_mode n n (le_refl n), if_pos rfl]
  rw [hl] at h
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

theorem sigma_eq_scale_sq (n : ℕ) : schurSigma n = (residueModeScale n)^2 := by
  rw [schurSigma, innovation_eq_scale_mode, norm_smul, Real.norm_eq_abs,
    abs_of_pos (residueModeScale_pos n), residueMode_orthonormal.1 n, mul_one]

theorem eta_eq_scale_alpha (n : ℕ) : schurEta n = residueModeScale n * modeAlpha n := by
  rw [schurEta, innovation_eq_scale_mode, real_inner_smul_left]
  rfl

theorem sigma_pos (n : ℕ) : 0 < schurSigma n := by
  rw [sigma_eq_scale_sq]
  exact sq_pos_of_pos (residueModeScale_pos n)

/-- The geometric innovation norm is the matrix Schur complement. -/
theorem sigma_eq_gram_schur (n : ℕ) :
    schurSigma n = ‖residueAtom n‖ ^ 2 - dotProduct (coupling n) (eliminated n) := by
  have hz : eliminated n = inverseCoeff (finiteAtom_independent n) (residueAtom n) := by
    rw [eliminated, fullGram, gramMatrix_inverseSource]
    rfl
  have h := residual_schur_value (finiteAtom_independent n) (residueAtom n)
  rw [synthesis_inverseCoeff_eq_projection] at h
  change schurSigma n = _ at h
  simpa only [hz, coupling, dotProduct, mul_comm] using h

/-- The innovation source equals beta minus the cross-Gram correction. -/
theorem eta_eq_gram_schur (n : ℕ) :
    schurEta n = Real.log ((n + 2 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) -
      dotProduct (coupling n) (canonicalVector n) := by
  rw [schurEta, innovation, inner_sub_left,
    (finiteSpace n).inner_starProjection_left_eq_right]
  change inner ℝ (residueAtom n) hilbertOne -
    inner ℝ (residueAtom n) (projection n) = _
  rw [residueAtom_inner_one, projection_eq_inverseGram_synthesis, inner_sum]
  simp only [real_inner_smul_right, dotProduct, coupling, cross, mul_comm, real_inner_comm]

theorem projection_schur_step (n : ℕ) :
    projection (n+1) = projection n + (schurEta n / schurSigma n) • innovation n := by
  rw [projection_succ_mode, innovation_eq_scale_mode, eta_eq_scale_alpha,
    sigma_eq_scale_sq, smul_smul]
  congr 2
  field_simp [ne_of_gt (residueModeScale_pos n)]

theorem innovation_old_coefficient (n : ℕ) (i : Fin n) :
    coefficientCLM (i.val + 2) (innovation n) = -eliminated n i := by
  rw [innovation, map_sub, coefficientCLM_biorthogonal,
    projection_coefficient_eq_inverseGram, if_neg (Nat.ne_of_lt i.isLt)]
  simp only [zero_sub, eliminated, coupling]

theorem innovation_new_coefficient (n : ℕ) :
    coefficientCLM (n + 2) (innovation n) = 1 := by
  rw [innovation_eq_scale_mode, map_smul]
  change residueModeScale n * modeCoefficient (n + 2) n = 1
  rw [mul_comm, modeCoefficient_mul_scale]

theorem coefficient_outside (n : ℕ) : coefficient n (n+2) = 0 := by
  unfold coefficient
  rw [projection_eq_inverseGram_synthesis, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_smul, coefficientCLM_biorthogonal, if_neg (by omega)]
  simp

theorem coefficient_schur_new (n : ℕ) :
    coefficient (n+1) (n+2) = schurEta n / schurSigma n := by
  unfold coefficient
  rw [projection_schur_step, map_add, map_smul, innovation_new_coefficient]
  change coefficient n (n+2) + (schurEta n / schurSigma n) * 1 = _
  rw [coefficient_outside, mul_one, zero_add]

theorem coefficient_schur_old (n : ℕ) (i : Fin n) :
    coefficient (n+1) (i.val+2) =
      coefficient n (i.val+2) - eliminated n i * (schurEta n / schurSigma n) := by
  unfold coefficient
  rw [projection_schur_step, map_add, map_smul, innovation_old_coefficient]
  simp only [smul_eq_mul]
  ring

theorem captured_schur_step (n : ℕ) :
    captured (n+1) = captured n + (schurEta n)^2 / schurSigma n := by
  rw [captured_succ_mode, eta_eq_scale_alpha, sigma_eq_scale_sq]
  congr 1
  field_simp [ne_of_gt (residueModeScale_pos n)]

theorem captured_one : captured 1 = Real.log 2 := by
  have h := error_eq_one_sub_captured 1
  change energy 1 = _ at h
  rw [energy_one] at h
  linarith

theorem canonicalVector_one : canonicalVector 1 0 = 2 := by
  have h := inverseCoeff_normal (finiteAtom_independent 1) hilbertOne (0 : Fin 1)
  rw [← canonical_eq_inverseCoeff, Fintype.linearCombination_apply] at h
  simp only [Fin.sum_univ_one, Fin.val_zero, real_inner_smul_right] at h
  rw [real_inner_self_eq_norm_sq, residueAtom_zero_norm_sq] at h
  change canonicalVector 1 0 * (Real.log 2 / 4) =
    inner ℝ (residueAtom 0) hilbertOne at h
  rw [residueAtom_inner_one] at h
  norm_num at h
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

theorem projection_one : projection 1 = (2 : ℝ) • residueAtom 0 := by
  rw [projection_eq_inverseGram_synthesis]
  simp only [Fin.sum_univ_one, Fin.val_zero, canonicalVector_one]

/-- Last coordinate of the next inverse-Gram minimizer. -/
theorem canonicalVector_schur_new (n : ℕ) :
    canonicalVector (n+1) (Fin.last n) = schurEta n / schurSigma n := by
  rw [canonicalVector_apply]
  exact coefficient_schur_new n

/-- Earlier coordinates of the next inverse-Gram minimizer. -/
theorem canonicalVector_schur_old (n : ℕ) (i : Fin n) :
    canonicalVector (n+1) i.castSucc =
      canonicalVector n i - eliminated n i * (schurEta n / schurSigma n) := by
  simp only [canonicalVector_apply, Fin.val_castSucc]
  exact coefficient_schur_old n i

end RiemannResearch.RH.Pareto.CoefficientStabilization.ProjectionSchur
