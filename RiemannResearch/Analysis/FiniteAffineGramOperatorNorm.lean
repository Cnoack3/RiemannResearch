/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteAffineGramConstraints
import RiemannResearch.Analysis.SupNormSignVertices
import RiemannResearch.Analysis.EuclideanEnergyOperatorNorm
import RiemannResearch.Analysis.PositiveGramMinimumEigenvalue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The finite sup-source interpolation norm is the exact sign-cube cost

Source: the reciprocal-head investigation, 7 November 2026, Section 4.
The source uses the actual finite Pi supremum norm. Its maximum is over all
sign vertices and retains every signed cross term of the inverse Gram form.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteAffineGramConstraints
open FiniteHilbertGram FiniteHilbertConstraints
variable {κ H : Type*} [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (S : Submodule ℝ H) [S.HasOrthogonalProjection]
  (e : κ → H) (he : LinearIndependent ℝ (projectedRows S e))

/-- The complete minimum interpolation map, on the genuine sup-norm source space. -/
def minimumInterpolationLinear : (κ → ℝ) →ₗ[ℝ] H :=
  S.subtype.comp ((Fintype.linearCombination ℝ (projectedRows S e)).comp
    (gramEquiv he).symm.toLinearMap)

def minimumInterpolationCLM : (κ → ℝ) →L[ℝ] H :=
  (minimumInterpolationLinear S e he).toContinuousLinearMap

@[simp] theorem minimumInterpolationCLM_apply (b : κ → ℝ) :
    minimumInterpolationCLM S e he b = minimumInterpolation S e he b := rfl

variable [DecidableEq κ]

theorem minimumInterpolationCLM_energy (b : κ → ℝ) :
    ‖minimumInterpolationCLM S e he b‖ ^ 2 =
      dotProduct b ((gramMatrix (projectedRows S e))⁻¹.mulVec b) := by
  rw [minimumInterpolationCLM_apply, minimumInterpolation_matrix_value]

/-- The squared actual sup-source operator norm is exactly the maximum sign
quadratic cost, expressed as an IsGreatest certificate. -/
theorem minimumInterpolationCLM_sup_norm_sq_max :
    IsGreatest
      (Set.range (fun b : κ → Bool =>
        dotProduct (ContinuousLinearMap.signVertex b)
          ((gramMatrix (projectedRows S e))⁻¹.mulVec
            (ContinuousLinearMap.signVertex b))))
      (‖minimumInterpolationCLM S e he‖ ^ 2) := by
  obtain ⟨b, hb⟩ := (minimumInterpolationCLM S e he).exists_signVertex_opNorm
  constructor
  · refine ⟨b, ?_⟩
    dsimp only
    rw [← minimumInterpolationCLM_energy S e he, hb]
  · rintro v ⟨b, rfl⟩
    dsimp only
    rw [← minimumInterpolationCLM_energy S e he]
    have hle : ‖minimumInterpolationCLM S e he (ContinuousLinearMap.signVertex b)‖ ≤
        ‖minimumInterpolationCLM S e he‖ := by
      calc
        _ ≤ ‖minimumInterpolationCLM S e he‖ * ‖ContinuousLinearMap.signVertex b‖ :=
          (minimumInterpolationCLM S e he).le_opNorm _
        _ ≤ ‖minimumInterpolationCLM S e he‖ * 1 :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.signVertex_norm_le_one b) (norm_nonneg _)
        _ = _ := mul_one _
    nlinarith [norm_nonneg (minimumInterpolationCLM S e he (ContinuousLinearMap.signVertex b)),
      norm_nonneg (minimumInterpolationCLM S e he)]

/-- The same physical minimum interpolation map with the Euclidean source norm. -/
def euclideanInterpolationCLM : EuclideanSpace ℝ κ →L[ℝ] H :=
  ((minimumInterpolationLinear S e he).comp
    (WithLp.linearEquiv 2 ℝ (κ → ℝ)).toLinearMap).toContinuousLinearMap

theorem euclideanInterpolationCLM_energy (b : EuclideanSpace ℝ κ) :
    ‖euclideanInterpolationCLM S e he b‖ ^ 2 =
      inner ℝ (Matrix.toEuclideanLin ((gramMatrix (projectedRows S e))⁻¹) b) b := by
  change ‖minimumInterpolation S e he b.ofLp‖ ^ 2 = _
  rw [minimumInterpolation_matrix_value, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.ofLp_toEuclideanLin_apply]
  simp only [star_trivial]

/-- The normalized Euclidean squared norm is the largest actual Rayleigh
eigenvalue of the inverse restricted-observation Gram matrix. -/
theorem euclideanInterpolationCLM_norm_sq [Nonempty κ] :
    ‖euclideanInterpolationCLM S e he‖ ^ 2 =
      Matrix.maximalRayleigh ((gramMatrix (projectedRows S e))⁻¹) := by
  apply ContinuousLinearMap.norm_sq_eq_maximalRayleigh_of_energy
  exact euclideanInterpolationCLM_energy S e he

/-- The paper's 2-to-H formula with the actual finite minimum eigenvalue of S. -/
theorem euclideanInterpolationCLM_norm_sq_leastEigenvalue [Nonempty κ] :
    ‖euclideanInterpolationCLM S e he‖ ^ 2 =
      1 / PositiveGramMinimumEigenvalue.leastEigenvalue
        (gramMatrix_posDef he) := by
  apply PositiveGramMinimumEigenvalue.norm_sq_eq_reciprocal_leastEigenvalue
  exact euclideanInterpolationCLM_energy S e he

end RiemannResearch.Analysis.FiniteAffineGramConstraints
