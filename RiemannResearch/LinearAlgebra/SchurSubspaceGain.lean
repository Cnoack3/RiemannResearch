import RiemannResearch.LinearAlgebra.OrthogonalFarSupportBound
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Full subspace gain after reoptimizing the old space

Source: `RH_Exact_Signed_Schur_Remainder_2026-09-16.tex`, far-support lemma.
The new space is residualized by the actual old-space orthogonal projection.
The result bounds the complete optimized block gain, with arbitrary block size.
Applications still have to prove their support pairing and tail-capture bounds.
-/

noncomputable section
namespace RiemannResearch.LinearAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def schurResidualizedSubspace (K Q : Submodule ℝ H) [K.HasOrthogonalProjection] :
    Submodule ℝ H := Q.map (ContinuousLinearMap.id ℝ H - K.starProjection).toLinearMap

theorem schurResidualizedSubspace_gain_le
    (K Q : Submodule ℝ H) [K.HasOrthogonalProjection]
    [(schurResidualizedSubspace K Q).HasOrthogonalProjection]
    (r z : H) (τ : ℝ) (hτ : τ < 1) (hr : r ∈ Kᗮ)
    (hcapture : ∀ q ∈ Q, ‖K.starProjection q‖ ^ 2 ≤ τ * ‖q‖ ^ 2)
    (hsupport : ∀ q ∈ Q, inner ℝ r q = inner ℝ z q) :
    ‖r‖ ^ 2 - ‖r - (schurResidualizedSubspace K Q).starProjection r‖ ^ 2 ≤
      ‖z‖ ^ 2 / (1 - τ) := by
  let N := schurResidualizedSubspace K Q
  obtain ⟨q, hq, heq⟩ := N.starProjection_apply_mem r
  change q - K.starProjection q = N.starProjection r at heq
  have hp : inner ℝ (q - K.starProjection q) (K.starProjection q) = 0 := by
    rw [real_inner_comm]
    exact (K.mem_orthogonal _).mp (Submodule.sub_starProjection_mem_orthogonal q)
      _ (K.starProjection_apply_mem q)
  have hrp : inner ℝ r (K.starProjection q) = 0 := by
    rw [real_inner_comm]
    exact (K.mem_orthogonal r).mp hr _ (K.starProjection_apply_mem q)
  by_cases hq0 : q = 0
  · have hz0 : N.starProjection r = 0 := by simpa [hq0] using heq.symm
    change ‖r‖ ^ 2 - ‖r - N.starProjection r‖ ^ 2 ≤ _
    rw [hz0, sub_zero, sub_self]
    exact div_nonneg (sq_nonneg _) (sub_pos.mpr hτ).le
  have hn : inner ℝ r (N.starProjection r) = ‖N.starProjection r‖ ^ 2 := by
    have h := (N.mem_orthogonal _).mp (Submodule.sub_starProjection_mem_orthogonal r)
      _ (N.starProjection_apply_mem r)
    rw [real_inner_comm] at h
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at h
    linarith
  have hpos : 0 < ‖q - K.starProjection q‖ ^ 2 :=
    lt_of_lt_of_le (mul_pos (sub_pos.mpr hτ) (pow_pos (norm_pos_iff.mpr hq0) 2))
      (orthogonal_component_residual_lower q (K.starProjection q) τ hp (hcapture q hq))
  have he : schurRemove (q - K.starProjection q) r = r - N.starProjection r := by
    unfold schurRemove
    rw [heq, hn, div_self (ne_of_gt (heq ▸ hpos)), one_smul]
  have hb := orthogonal_component_energy_gain_le r q (K.starProjection q) z τ
    hq0 hτ hp hrp (hcapture q hq) (hsupport q hq)
  rw [he] at hb
  exact hb

end RiemannResearch.LinearAlgebra
