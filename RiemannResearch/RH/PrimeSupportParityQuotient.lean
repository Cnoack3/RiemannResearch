import RiemannResearch.RH.PrimeSupportCokernel
import RiemannResearch.RH.CenteredMeanQuotients
import RiemannResearch.RH.MixedConductorGlobalParseval

/-!
# Parity in the prime-support cokernel tower

The classes of the normalized parity packet minus the ambient constant have
squared norms equal to the squared centered snake boundary plus the omitted
mixed energy. Orthogonal projection in the mixed space realizes the minimum
over each ambient support stage. See S. Axler, *Measure, Integration & Real
Analysis*, Chapter 8, on best approximation in Hilbert space.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis

open CoefficientStabilization

/-- The class of the normalized conductor-two packet minus the ambient constant. -/
def parityQuotientClass (n : ℕ) : ThresholdHilbert ⧸ ambientSupport n :=
  (ambientSupport n).mkQ ((Real.log 2)⁻¹ • ramanujanPacketHilbert 2 - hilbertOne)

/-- The squared quotient distance includes the snake obstruction and the omitted mixed energy. -/
theorem parityQuotientClass_norm_sq (n : ℕ) :
    ‖parityQuotientClass n‖ ^ 2 = ‖CenteredMeanSnake.boundary‖ ^ 2 +
      ‖parityMixedProjection - (supportSpace n).starProjection parityMixedProjection‖ ^ 2 := by
  let g : ThresholdHilbert := (Real.log 2)⁻¹ • ramanujanPacketHilbert 2
  let m := parityMixedProjection
  let p := (supportSpace n).starProjection m
  let d := normalizedScreenedTwo - hilbertOne
  have hsplit : g - hilbertOne = d + (m : ThresholdHilbert) := by
    have hu := CenteredMeanSnake.normalizedScreenedTwo_eq_projected_packet
    rw [Submodule.starProjection_orthogonal_val, smul_sub] at hu
    change g - hilbertOne = (normalizedScreenedTwo - hilbertOne) + mixedClosure.starProjection g
    dsimp only [g]
    rw [map_smul, hu]
    abel
  have hnorm (w : mixedClosure) :
      ‖g - hilbertOne - (w : ThresholdHilbert)‖ ^ 2 =
        ‖CenteredMeanSnake.boundary‖ ^ 2 + ‖m - w‖ ^ 2 := by
    have ho : inner ℝ d ((m - w : mixedClosure) : ThresholdHilbert) = 0 :=
      (real_inner_comm _ _).trans
        (CenteredMeanSnake.screenedTwo_sub_one_mem_orthogonals.2 _ (m - w).property)
    rw [hsplit, add_sub_assoc]
    change ‖d + ((m - w : mixedClosure) : ThresholdHilbert)‖ ^ 2 = _
    rw [norm_add_sq_real, ho, CenteredMeanSnake.boundary_norm]
    change ‖d‖ ^ 2 + 2 * 0 + ‖m - w‖ ^ 2 = ‖d‖ ^ 2 + ‖m - w‖ ^ 2
    ring
  have hp : (p : ThresholdHilbert) ∈ ambientSupport n :=
    ⟨p, (supportSpace n).starProjection_apply_mem m, rfl⟩
  have hmin (w : mixedClosure) (hw : w ∈ supportSpace n) : ‖m - p‖ ≤ ‖m - w‖ := by
    change ‖m - (supportSpace n).starProjection m‖ ≤ ‖m - w‖
    rw [← (supportSpace n).infDist_eq_norm_sub_starProjection m]
    simpa only [dist_eq_norm] using Metric.infDist_le_dist_of_mem (x := m) hw
  have hdist : ‖parityQuotientClass n‖ = ‖g - hilbertOne - (p : ThresholdHilbert)‖ := by
    have hq : ‖parityQuotientClass n‖ =
        Metric.infDist (g - hilbertOne) (ambientSupport n : Set ThresholdHilbert) :=
      QuotientAddGroup.norm_mk (S := (ambientSupport n).toAddSubgroup) (g - hilbertOne)
    rw [hq]
    apply le_antisymm
    · simpa only [dist_eq_norm] using Metric.infDist_le_dist_of_mem (x := g - hilbertOne) hp
    · apply (Metric.le_infDist ⟨0, (ambientSupport n).zero_mem⟩).mpr
      rintro _ ⟨w, hw, rfl⟩
      rw [dist_eq_norm]
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      change ‖g - hilbertOne - (p : ThresholdHilbert)‖ ^ 2 ≤
        ‖g - hilbertOne - (w : ThresholdHilbert)‖ ^ 2
      rw [hnorm p, hnorm w]
      exact add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) (hmin w hw) 2)
  rw [hdist]
  exact hnorm p

/-- Along the support diagram the squared quotient norms converge to the squared boundary norm. -/
theorem tendsto_parityQuotientClass_norm_sq :
    Tendsto (fun n => ‖parityQuotientClass n‖ ^ 2) atTop
      (𝓝 (‖CenteredMeanSnake.boundary‖ ^ 2)) := by
  have hp := tendsto_sum_supportLayer_projection parityMixedProjection
  simp only [sum_supportLayer_projection] at hp
  have ht := ((tendsto_const_nhds (x := parityMixedProjection)).sub hp).norm.pow 2
  simpa only [parityQuotientClass_norm_sq, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    add_zero] using (tendsto_const_nhds (x := ‖CenteredMeanSnake.boundary‖ ^ 2)).add ht

end RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis
