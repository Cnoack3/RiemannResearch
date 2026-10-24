import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import RiemannResearch.Analysis.FiniteHilbertGram
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact Gram increments for nested orthogonal projections

Source: user-requested fourth Ramanujan dual continuation, 23 October 2026.
The full bilinear identity strengthens the scalar nested-energy identity:
the difference of projected Gram forms is itself an actual Gram form.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.NestedProjectionGram

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem projected_pairing (K L : Submodule ℝ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (hKL : K ≤ L)
    (x y : H) :
    inner ℝ (L.starProjection x) (K.starProjection y) =
      inner ℝ (K.starProjection x) (K.starProjection y) := by
  have hk : inner ℝ (x - K.starProjection x) (K.starProjection y) = 0 := by
    rw [real_inner_comm]
    exact (K.mem_orthogonal _).mp (Submodule.sub_starProjection_mem_orthogonal x) _
      (K.starProjection_apply_mem y)
  have hl : inner ℝ (x - L.starProjection x) (K.starProjection y) = 0 := by
    rw [real_inner_comm]
    exact (L.mem_orthogonal _).mp (Submodule.sub_starProjection_mem_orthogonal x) _
      (hKL (K.starProjection_apply_mem y))
  rw [inner_sub_left] at hk hl
  linarith

/-- The complete signed bilinear increment, with both projection-error factors. -/
theorem gram_increment_exact (K L : Submodule ℝ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (hKL : K ≤ L)
    (x y : H) :
    inner ℝ (L.starProjection x) (L.starProjection y) =
      inner ℝ (K.starProjection x) (K.starProjection y) +
        inner ℝ (L.starProjection x - K.starProjection x)
          (L.starProjection y - K.starProjection y) := by
  have hxy := projected_pairing K L hKL x y
  have hyx : inner ℝ (K.starProjection x) (L.starProjection y) =
      inner ℝ (K.starProjection x) (K.starProjection y) := by
    rw [real_inner_comm, projected_pairing K L hKL y x, real_inner_comm]
  rw [inner_sub_left, inner_sub_right, inner_sub_right, hxy, hyx]
  ring

theorem norm_increment_exact (K L : Submodule ℝ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (hKL : K ≤ L) (x : H) :
    ‖L.starProjection x‖ ^ 2 = ‖K.starProjection x‖ ^ 2 +
      ‖L.starProjection x - K.starProjection x‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using gram_increment_exact K L hKL x x

variable {ι : Type*} [Fintype ι]

/-- Finite simultaneous observations retain their entire Gram remainder. -/
theorem synthesis_increment_exact (K L : Submodule ℝ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (hKL : K ≤ L)
    (v : ι → H) (c : ι → ℝ) :
    ‖Fintype.linearCombination ℝ (fun i => L.starProjection (v i)) c‖ ^ 2 =
      ‖Fintype.linearCombination ℝ (fun i => K.starProjection (v i)) c‖ ^ 2 +
        ‖Fintype.linearCombination ℝ
          (fun i => L.starProjection (v i) - K.starProjection (v i)) c‖ ^ 2 := by
  have h := norm_increment_exact K L hKL (Fintype.linearCombination ℝ v c)
  simpa only [Fintype.linearCombination_apply, map_sum, map_smul,
    Finset.sum_sub_distrib, smul_sub] using h

end RiemannResearch.Analysis.NestedProjectionGram
