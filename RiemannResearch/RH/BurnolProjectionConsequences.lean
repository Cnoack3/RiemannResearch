import RiemannResearch.Analysis.NestedProjectionEnergy
import RiemannResearch.Analysis.InnerMultiplierProjection
import RiemannResearch.RH.BurnolZeroProductConvergence

/-!
# Consequences of an explicitly supplied Burnol projection identity

Source: Burnol, Theorem 1.2 and Lemma 2.4,
https://arxiv.org/abs/math/9910055. The hypothesis `hBurnol` below is the
squared projection identity. This module derives its Hilbert-space and RH
consequences but does not claim to supply the Hardy-space analytic theorem.
In particular, comparison with a smaller approximation space retains the
full difference between the two projected vectors.
-/

noncomputable section
namespace RiemannResearch.RH.Burnol
open RiemannResearch.Analysis.NestedProjectionEnergy

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
variable {U V : Submodule 𝕜 E}
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- The distance formula follows from Pythagoras and the supplied product identity. -/
theorem unit_residual_energy_of_product (e : E) (he : ‖e‖ = 1)
    (hBurnol : ‖V.starProjection e‖ ^ 2 = productSq) :
    ‖e - V.starProjection e‖ ^ 2 = 1 - productSq := by
  have h := norm_sq_eq_projection_add_residual V e
  rw [he, one_pow, hBurnol] at h
  linarith

/-- For the space with the product formula, unit-target membership is equivalent to RH. -/
theorem unit_mem_iff_rh_of_product (e : E) (he : ‖e‖ = 1)
    (hBurnol : ‖V.starProjection e‖ ^ 2 = productSq) :
    e ∈ V ↔ RiemannHypothesis := by
  rw [← productSq_eq_one_iff_rh, ← hBurnol]
  constructor
  · intro h
    rw [(Submodule.mem_iff_norm_starProjection V e).mp h, he]
    norm_num
  · intro h
    apply (Submodule.mem_iff_norm_starProjection V e).mpr
    rw [he]
    nlinarith [norm_nonneg (V.starProjection e)]

/-- The product controls the larger space; the smaller space has an exact extra error. -/
theorem smaller_residual_energy_of_product (hUV : U ≤ V) (e : E) (he : ‖e‖ = 1)
    (hBurnol : ‖V.starProjection e‖ ^ 2 = productSq) :
    ‖e - U.starProjection e‖ ^ 2 = 1 - productSq +
      ‖V.starProjection e - U.starProjection e‖ ^ 2 := by
  exact unit_residual_energy_eq_sub_add_gap hUV e he productSq hBurnol

/-- The exact remainder persists even after imposing RH. -/
theorem smaller_residual_energy_on_rh (hUV : U ≤ V) (e : E) (he : ‖e‖ = 1)
    (hBurnol : ‖V.starProjection e‖ ^ 2 = productSq) (hRH : RiemannHypothesis) :
    ‖e - U.starProjection e‖ ^ 2 = ‖V.starProjection e - U.starProjection e‖ ^ 2 := by
  rw [smaller_residual_energy_of_product hUV e he hBurnol, productSq_eq_one_of_rh hRH]
  ring

/-- Equality of projection vectors is the precise extra condition needed
for membership in a smaller space from this comparison alone. -/
theorem unit_mem_smaller_iff_rh_and_projection_eq (hUV : U ≤ V)
    (e : E) (he : ‖e‖ = 1) (hBurnol : ‖V.starProjection e‖ ^ 2 = productSq) :
    e ∈ U ↔ RiemannHypothesis ∧ V.starProjection e = U.starProjection e := by
  constructor
  · intro h
    have hv := hUV h
    refine ⟨(unit_mem_iff_rh_of_product e he hBurnol).mp hv, ?_⟩
    rw [(Submodule.starProjection_eq_self_iff).mpr hv,
      (Submodule.starProjection_eq_self_iff).mpr h]
  · rintro ⟨hRH, heq⟩
    have hv := (unit_mem_iff_rh_of_product e he hBurnol).mpr hRH
    apply (Submodule.starProjection_eq_self_iff).mp
    rw [← heq]
    exact (Submodule.starProjection_eq_self_iff).mpr hv

/-- Every actual right-hand zero obstructs approximation in each smaller space. -/
theorem singleZero_defect_le_smaller_residual (hUV : U ≤ V) (e : E) (he : ‖e‖ = 1)
    (hBurnol : ‖V.starProjection e‖ ^ 2 = productSq) (ρ : RightZero) :
    1 - weightedFactorSq ρ ≤ ‖e - U.starProjection e‖ ^ 2 := by
  rw [smaller_residual_energy_of_product hUV e he hBurnol]
  have h := singleZero_defect_le_product_defect ρ
  nlinarith [sq_nonneg ‖V.starProjection e - U.starProjection e‖]

/-- The isometric-multiplier computation can discharge the scalar norm
identity once the analytic reproducing relation and its coefficient are supplied. -/
theorem projection_product_of_multiplier (T : E →ₗᵢ[𝕜] E)
    [T.toLinearMap.range.HasOrthogonalProjection] (e : E) (he : ‖e‖ = 1)
    (c : 𝕜) (hc : ‖c‖ ^ 2 = productSq)
    (hreproduce : ∀ y : E, inner 𝕜 e (T y) = inner 𝕜 (c • e) y) :
    ‖T.toLinearMap.range.starProjection e‖ ^ 2 = productSq := by
  rw [RiemannResearch.Analysis.InnerMultiplierProjection.norm_sq_projection_eq_of_unit
    T e he c hreproduce, hc]

end RiemannResearch.RH.Burnol
