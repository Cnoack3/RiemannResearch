import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.Analysis.PositiveCompressionCertificate

/-!
# Complete inverse-Gram energy and inexact solve certificates

Every Gram entry is the complete Hilbert inner product. The exact remainder
is another inverse-Gram energy of the equation residual, so signed cross
terms and coefficient rounding errors are retained.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteHilbertGram
variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def dualEnergy {v : ι → H} (hv : LinearIndependent ℝ v) (z : ι → ℝ) : ℝ :=
  ∑ i, (gramEquiv hv).symm z i * z i

theorem projection_norm_sq_dual {v : ι → H} (hv : LinearIndependent ℝ v) (y : H) :
    ‖(synthesisSpan v).starProjection y‖ ^ 2 = dualEnergy hv (cross v y) := by
  rw [← synthesis_inverseCoeff_eq_projection hv y, gram_quadratic]
  apply Finset.sum_congr rfl
  intro i _
  change inverseCoeff hv y i *
    inner ℝ (v i) (Fintype.linearCombination ℝ v (inverseCoeff hv y)) = _
  rw [inverseCoeff_normal]
  rfl

/-- Exact squared forcing norm from any trial coefficients. -/
theorem inexact_dualEnergy {v : ι → H} (hv : LinearIndependent ℝ v)
    (y : H) (c : ι → ℝ) :
    dualEnergy hv (cross v y) =
      2 * (∑ i, c i * cross v y i) - (∑ i, c i * gram v c i) +
        dualEnergy hv (cross v y - gram v c) := by
  have h := PositiveCompressionCertificate.forcing_energy_exact
    (synthesisSpan v) (ContinuousLinearMap.id ℝ H) y
    (Fintype.linearCombination ℝ v c) (synthesis_mem v c)
  have he : (synthesisSpan v).starProjection y - Fintype.linearCombination ℝ v c =
      (synthesisSpan v).starProjection (y-Fintype.linearCombination ℝ v c) := by
    rw [map_sub, Submodule.starProjection_eq_self_iff.mpr (synthesis_mem v c)]
  have hz : cross v (y-Fintype.linearCombination ℝ v c) = cross v y - gram v c := by
    funext i
    exact inner_sub_right _ _ _
  simp only [ContinuousLinearMap.id_apply] at h
  rw [he, projection_norm_sq_dual hv, projection_norm_sq_dual hv, hz, gram_quadratic,
    real_inner_comm, inner_synthesis_left] at h
  exact h

/-- Upper endpoints may combine independently certified signed score and
equation-residual energy bounds. -/
theorem inexact_dualEnergy_upper {v : ι → H} (hv : LinearIndependent ℝ v)
    (y : H) (c : ι → ℝ) (S E : ℝ)
    (hS : 2 * (∑ i, c i * cross v y i) - (∑ i, c i * gram v c i) ≤ S)
    (hE : dualEnergy hv (cross v y - gram v c) ≤ E) :
    ‖(synthesisSpan v).starProjection y‖ ^ 2 ≤ S+E := by
  rw [projection_norm_sq_dual hv, inexact_dualEnergy hv y c]
  exact add_le_add hS hE

end RiemannResearch.Analysis.FiniteHilbertGram
