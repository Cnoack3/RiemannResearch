import RiemannResearch.RH.ParetoDensityDilation
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Complete Pareto leakage on dilated legal vectors

Source: the user's dilation/B discussion, 14 November 2026.
This is an unconditional 1/m estimate for the actual orthogonal leakage.
It does not imply that leakage vanishes on the undilated legal closure.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.DilationDensityLeakage
open CoefficientStabilization
open RiemannResearch.RH.ParetoDensityDilation
open RiemannResearch.RH.ZetaTwoProbability

theorem normalized_mem_closedSpace (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) (hf : f ∈ closedSpace) :
    normalizedP m hm f ∈ closedSpace := by
  change (1 / Real.sqrt (m : ℝ)) • hilbertDilation m hm f ∈ closedSpace
  exact closedSpace.smul_mem _ (closedSpace_dilation hf m hm)

def leakage : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  closedSpaceᗮ.starProjection.comp densityP

theorem leakage_normalized_eq (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) (hf : f ∈ closedSpace) :
    leakage (normalizedP m hm f) =
      closedSpaceᗮ.starProjection
        (densityP (normalizedP m hm f) - (1 / zetaTwo) • normalizedP m hm f) := by
  have hz : closedSpaceᗮ.starProjection ((1 / zetaTwo) • normalizedP m hm f) = 0 := by
    rw [Submodule.starProjection_orthogonal_val,
      Submodule.starProjection_eq_self_iff.mpr
        (closedSpace.smul_mem _ (normalized_mem_closedSpace m hm f hf)), sub_self]
  rw [map_sub, hz, sub_zero]
  rfl

theorem leakage_normalized_norm_le (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) (hf : f ∈ closedSpace) :
    ‖leakage (normalizedP m hm f)‖ ≤
      (1 / (zetaTwo * (m : ℝ))) * ‖f‖ := by
  rw [leakage_normalized_eq m hm f hf]
  exact (closedSpaceᗮ.norm_starProjection_apply_le _).trans
    (density_normalized_error_norm_le m hm f)

#print axioms leakage_normalized_norm_le

end RiemannResearch.RH.Pareto.DilationDensityLeakage
