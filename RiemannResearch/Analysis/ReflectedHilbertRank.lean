import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Orthogonal reflection: Hilbert-space zero cross term and rank doubling

Source: user-provided reciprocal Mellin construction (2026-09-20).

These results discharge the zero-cross-term assumption in the abstract reflected
projection construction from the ordinary geometric condition `S ⟂ J(S)`.
The rank result only needs a linear equivalence; neither involutivity nor RH is
needed for it. An involutive unitary reciprocal reflection is a special case.
-/

noncomputable section

namespace RiemannResearch.Analysis.ReflectedHilbertRank

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]

/-- Ordinary subspace orthogonality implies the zero cross term `P J P = 0`
for the actual Hilbert orthogonal projection `P = S.starProjection`. -/
theorem starProjection_reflection_starProjection_eq_zero
    (S : Submodule 𝕜 E) [S.HasOrthogonalProjection]
    (J : E →L[𝕜] E)
    (horth : ∀ x ∈ S, ∀ y ∈ S, inner 𝕜 x (J y) = 0) :
    S.starProjection * J * S.starProjection = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change S.starProjection (J (S.starProjection x)) = 0
  rw [Submodule.starProjection_apply_eq_zero_iff]
  exact (S.mem_orthogonal _).mpr
    (fun w hw => horth w hw _ (S.starProjection_apply_mem x))

/-- The original and reflected subspaces intersect only at zero. -/
theorem inf_reflected_eq_bot
    (S : Submodule 𝕜 E) (J : E →ₗ[𝕜] E)
    (horth : ∀ x ∈ S, ∀ y ∈ S, inner 𝕜 x (J y) = 0) :
    S ⊓ S.map J = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  rcases Submodule.mem_map.mp hx.2 with ⟨y, hy, rfl⟩
  change J y = 0
  exact inner_self_eq_zero.mp (horth (J y) hx.1 y hy)

/-- A linear equivalence preserves the dimension of the reflected copy. -/
theorem finrank_reflected
    (S : Submodule 𝕜 E) (J : E ≃ₗ[𝕜] E) :
    Module.finrank 𝕜 (S.map J.toLinearMap) = Module.finrank 𝕜 S := by
  exact (J.submoduleMap S).finrank_eq.symm

/-- A finite-dimensional space and an orthogonal isomorphic reflected copy
have twice the original dimension. -/
theorem finrank_reflected_sup
    (S : Submodule 𝕜 E) [FiniteDimensional 𝕜 S]
    (J : E ≃ₗ[𝕜] E)
    (horth : ∀ x ∈ S, ∀ y ∈ S, inner 𝕜 x (J y) = 0) :
    Module.finrank 𝕜 ↥(S ⊔ S.map J.toLinearMap) =
      2 * Module.finrank 𝕜 S := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq S (S.map J.toLinearMap)
  rw [inf_reflected_eq_bot S J.toLinearMap horth] at h
  simpa [finrank_reflected, two_mul] using h

end RiemannResearch.Analysis.ReflectedHilbertRank
