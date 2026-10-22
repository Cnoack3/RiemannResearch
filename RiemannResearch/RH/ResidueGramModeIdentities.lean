import RiemannResearch.RH.ResidueGramCofactors

/-!
# The exact Gram and first-site identities in orthonormal coordinates

Source: user-provided orthonormal/projection/Gram conversation,
20 September 2026. This module specializes the proved Hilbert projection
identities to the actual residue Gram matrix and logarithmic mean vector.
The infinite arithmetic saturation assertion remains unproved.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteGramCapacity
open TailCapacity IntegerDPP

/-- The exact cross vector for the constant target. -/
def logarithmicSource (n : ℕ) (i : Fin n) : ℝ :=
  Real.log ((i.val + 2 : ℕ) : ℝ) / ((i.val + 2 : ℕ) : ℝ)

theorem constant_cross_eq_logarithmicSource (n : ℕ) :
    cross (fun i : Fin n => residueAtom i.val) hilbertOne = logarithmicSource n := by
  funext i
  exact residueAtom_inner_one i.val

/-- The actual finite projection coefficients are G⁻¹m. -/
theorem coefficient_eq_inverseGram_logarithmicSource (n : ℕ) (i : Fin n) :
    coefficient n (i.val + 2) =
      ((fullGram n)⁻¹.mulVec (logarithmicSource n)) i := by
  simpa only [constant_cross_eq_logarithmicSource, coefficient, projection] using
    projection_coefficient_eq_inverseGram n hilbertOne i

/-- Exact Cramer's-rule form for the projection, with all cofactors retained. -/
theorem coefficient_eq_adjugate_logarithmicSource (n : ℕ) (i : Fin n) :
    coefficient n (i.val + 2) =
      (∑ k, (fullGram n).adjugate i k * logarithmicSource n k) /
        (fullGram n).det := by
  rw [coefficient_eq_inverseGram_logarithmicSource, Matrix.inv_def, Ring.inverse_eq_inv]
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul,
    mul_assoc, ← Finset.mul_sum]
  ring

theorem logarithmic_inverseGram_eq_mode_sum (n : ℕ) :
    dotProduct (logarithmicSource n) ((fullGram n)⁻¹.mulVec (logarithmicSource n)) =
      ∑ j : Fin n, (modeAlpha j.val)^2 := by
  have hg := projection_inner_eq_inverseGram (finiteAtom_independent n) hilbertOne hilbertOne
  rw [constant_cross_eq_logarithmicSource] at hg
  have hn : Orthonormal ℝ (fun j : Fin n => residueMode j.val) :=
    residueMode_orthonormal.comp (fun j : Fin n => j.val) Fin.val_injective
  have hm : ‖(finiteSpace n).starProjection hilbertOne‖ ^ 2 =
      ∑ j : Fin n, (modeAlpha j.val)^2 := by
    simpa only [residueMode_finiteSpace, modeAlpha] using
      projection_norm_sq_eq_orthonormal_sum hn hilbertOne
  rw [real_inner_self_eq_norm_sq] at hg
  exact hg.symm.trans hm

theorem projection_firstCoordinate_eq_inverseGram (n : ℕ) :
    anchoredEvaluationCLM 1 (projection n) =
      dotProduct (reciprocalSource n) ((fullGram n)⁻¹.mulVec (logarithmicSource n)) := by
  rw [projection_expansion, map_sum]
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, residueAtom_evaluation,
    coefficient_eq_inverseGram_logarithmicSource]
  change _ * reciprocalSource n i = reciprocalSource n i * _
  ring

theorem projection_firstCoordinate_eq_mode_sum (n : ℕ) :
    anchoredEvaluationCLM 1 (projection n) =
      ∑ j : Fin n, modeAlpha j.val * anchoredEvaluationCLM 1 (residueMode j.val) := by
  rw [projection_eq_mode_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

theorem fullCapacity_eq_inverseGram (n : ℕ) :
    fullCapacity n =
      dotProduct (reciprocalSource n) ((fullGram n)⁻¹.mulVec (reciprocalSource n)) := by
  rw [fullGram, gramMatrix_inverseSource (finiteAtom_independent n)]
  unfold fullCapacity capacity dotProduct
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- K_n is exactly the sum of squared first-site mode values. -/
theorem fullCapacity_eq_mode_evaluation_sum (n : ℕ) :
    fullCapacity n =
      ∑ j : Fin n, (anchoredEvaluationCLM 1 (residueMode j.val))^2 := by
  have hn : Orthonormal ℝ (fun j : Fin n => residueMode j.val) :=
    residueMode_orthonormal.comp (fun j : Fin n => j.val) Fin.val_injective
  have hp : pointError n = (1 / 2 : ℝ) -
      ∑ j : Fin n, (inner ℝ (residueMode j.val) (paretoPointHilbert 0))^2 := by
    simpa only [residueMode_finiteSpace, firstPoint_norm_sq, pointError,
      RiemannResearch.Analysis.ExhaustiveWalk.walkError] using
      projection_error_eq_orthonormal_sum hn (paretoPointHilbert 0)
  simp only [inner_firstPoint] at hp
  have hs : (∑ j : Fin n,
      ((1 / 2 : ℝ) * anchoredEvaluationCLM 1 (residueMode j.val))^2) =
      (1 / 4 : ℝ) * ∑ j : Fin n, (anchoredEvaluationCLM 1 (residueMode j.val))^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hs, pointError_eq_deficit] at hp
  linarith

theorem firstCoordinate_inverseGram_eq_mode_sum (n : ℕ) :
    dotProduct (reciprocalSource n) ((fullGram n)⁻¹.mulVec (logarithmicSource n)) =
      ∑ j : Fin n, modeAlpha j.val * anchoredEvaluationCLM 1 (residueMode j.val) := by
  rw [← projection_firstCoordinate_eq_inverseGram, projection_firstCoordinate_eq_mode_sum]

end RiemannResearch.RH.Pareto.CoefficientStabilization
