import RiemannResearch.LinearAlgebra.WeightedFiniteQuotient
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Finite weighted conditional expectation as an actual Hilbert projection

Source: user-provided `RH_Controlled_Conductor_Schur_2026-09-10.md`, §3.
The Euclidean realization scales coordinate i by sqrt(w_i). This module
derives orthogonality from the full finite weighted quotient average.
-/

namespace RiemannResearch.LinearAlgebra.WeightedQuotientHilbert
open scoped BigOperators
open WeightedFiniteQuotient
noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The weighted finite space realized in an ordinary real Euclidean space. -/
def coordinates (w : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun x := WithLp.toLp 2 (fun i => Real.sqrt (w i) * x i)
  map_add' x y := by
    ext i
    simp [mul_add]
  map_smul' c x := by
    ext i
    simp
    ring

theorem coordinates_apply (w x : ι → ℝ) (i : ι) :
    coordinates w x i = Real.sqrt (w i) * x i := rfl

theorem coordinates_inner (w x y : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    inner ℝ (coordinates w x) (coordinates w y) = ∑ i, w i * x i * y i := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [RCLike.inner_apply']
  dsimp [coordinates]
  simp only [starRingEnd_apply, star_trivial]
  ring_nf
  rw [Real.sq_sqrt (hw i)] <;> ring

/-- Weighted repetition of coarse data. -/
def repetition (q : ι → κ) (w : ι → ℝ) : (κ → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun g := coordinates w (g ∘ q)
  map_add' g h := by
    have he : (g+h) ∘ q = g ∘ q + h ∘ q := rfl
    rw [he, map_add]
  map_smul' c g := by
    have he : (c • g) ∘ q = c • (g ∘ q) := rfl
    rw [he, map_smul]
    rfl

/-- The entire coarse function space, larger than the old legal packet span. -/
def coarseSpace (q : ι → κ) (w : ι → ℝ) : Submodule ℝ (EuclideanSpace ℝ ι) :=
  LinearMap.range (repetition q w)

theorem conditional_vector_mem (q : ι → κ) (w x : ι → ℝ) :
    coordinates w ((average q w x) ∘ q) ∈ coarseSpace q w :=
  ⟨average q w x, rfl⟩

/-- Actual weighted averaging proves orthogonality to every coarse vector. -/
theorem conditional_residual_orthogonal (q : ι → κ) (w x : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hW : ∀ b, pushforward q w b ≠ 0)
    (v : EuclideanSpace ℝ ι) (hv : v ∈ coarseSpace q w) :
    inner ℝ (coordinates w x - coordinates w ((average q w x) ∘ q)) v = 0 := by
  obtain ⟨g,rfl⟩ := hv
  change inner ℝ (coordinates w x - coordinates w ((average q w x) ∘ q))
    (coordinates w (g ∘ q)) = 0
  rw [← map_sub, coordinates_inner w _ _ hw]
  exact residual_orthogonal q w x g hW

/-- The exact weighted average is the actual orthogonal projection. -/
theorem conditional_vector_eq_projection (q : ι → κ) (w x : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hW : ∀ b, pushforward q w b ≠ 0) :
    coordinates w ((average q w x) ∘ q) =
      (coarseSpace q w).starProjection (coordinates w x) := by
  have hfix : (coarseSpace q w).starProjection
      (coordinates w ((average q w x) ∘ q)) = coordinates w ((average q w x) ∘ q) := by
    rw [Submodule.starProjection_eq_self_iff]
    exact conditional_vector_mem q w x
  have hz : (coarseSpace q w).starProjection
      (coordinates w x - coordinates w ((average q w x) ∘ q)) = 0 := by
    apply (Submodule.starProjection_apply_eq_zero_iff (coarseSpace q w)).2
    apply ((coarseSpace q w).mem_orthogonal _).2
    intro v hv
    rw [real_inner_comm]
    exact conditional_residual_orthogonal q w x hw hW v hv
  rw [map_sub, hfix, sub_eq_zero] at hz
  exact hz.symm

end
end RiemannResearch.LinearAlgebra.WeightedQuotientHilbert
