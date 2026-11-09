import RiemannResearch.Analysis.ProjectionDPPKernel
import RiemannResearch.Probability.DeterminantalExistence

/-!
# Finite observation laws of orthogonal projections

A finite orthonormal family gives a positive contraction by compressing an
orthogonal projection. The resulting DPP samples subsets of the observation
labels. A singleton vacancy is the squared distance of its unit observation
from the projected subspace.
-/

noncomputable section

open MeasureTheory

namespace RiemannResearch.Probability.DPP

open RiemannResearch.Analysis.ProjectionDPP

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype ι] [DecidableEq ι]
    (S : Submodule ℝ H) [S.HasOrthogonalProjection] (e : ι → H)

/-- The projection DPP observed on a finite orthonormal family. -/
def projectionObservationLaw
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0) : Measure (ι → Bool) :=
  (finiteBoolLaw (Matrix.of (kernel S e))
    (exactWeight_nonneg _ (principal_posSemidef S e id)
      (identity_sub_principal_posSemidef S e id he))).toMeasure

variable (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0)

instance projectionObservationLaw_probability :
    IsProbabilityMeasure (projectionObservationLaw S e he) := by
  unfold projectionObservationLaw
  infer_instance

theorem projectionObservationLaw_isDPP :
    IsDPP (projectionObservationLaw S e he) (fun x => {i | x i = true})
      (kernel S e) :=
  finiteBoolLaw_isDPP _ _

theorem projectionObservationLaw_vacancy (i : ι) :
    (projectionObservationLaw S e he).real {x | x i = false} =
      ‖e i - S.starProjection (e i)‖ ^ 2 := by
  have h := (projectionObservationLaw_isDPP S e he).vacancy i
  rw [← holeKernel_diagonal S e i, holeKernel_eq, he i i, if_pos rfl]
  simpa using h

end RiemannResearch.Probability.DPP
