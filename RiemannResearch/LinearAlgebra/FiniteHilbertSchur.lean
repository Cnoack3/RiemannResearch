import RiemannResearch.LinearAlgebra.OrthogonalSchurRepair
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Signed finite Schur identities in a real Hilbert space

Source: `RH_Exact_Signed_Schur_Remainder_2026-09-16.tex`, exact block gain.
The normal equations below use the complete signed Gram matrix. The inverse
formula requires an actual linear equivalence representing that matrix.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.LinearAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {ι : Type*} [Fintype ι]

def finiteSchurCombination (z : ι → H) (c : ι → ℝ) : H := ∑ i, c i • z i

def finiteSchurResidual (h : H) (z : ι → H) (c : ι → ℝ) : H :=
  h - finiteSchurCombination z c

theorem finiteSchurResidual_orthogonal (h : H) (z : ι → H) (c : ι → ℝ)
    (hc : ∀ i, inner ℝ (z i) (finiteSchurCombination z c) = inner ℝ (z i) h)
    (i : ι) : inner ℝ (z i) (finiteSchurResidual h z c) = 0 := by
  simp [finiteSchurResidual, inner_sub_right, hc i]

/-- Exact signed quadratic subtraction, without entrywise absolute values. -/
theorem finiteSchurResidual_norm_sq (h : H) (z : ι → H) (c : ι → ℝ)
    (hc : ∀ i, inner ℝ (z i) (finiteSchurCombination z c) = inner ℝ (z i) h) :
    ‖finiteSchurResidual h z c‖ ^ 2 =
      ‖h‖ ^ 2 - ∑ i, c i * inner ℝ (z i) h := by
  have hi : inner ℝ (finiteSchurCombination z c) h =
      ∑ i, c i * inner ℝ (z i) h := by
    simp [finiteSchurCombination, sum_inner, real_inner_smul_left]
  have hn : ‖finiteSchurCombination z c‖ ^ 2 =
      ∑ i, c i * inner ℝ (z i) h := by
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => arg 2; unfold finiteSchurCombination
    simp only [sum_inner, real_inner_smul_left, hc]
  have he := norm_add_smul_sq_exact h (finiteSchurCombination z c) (-1)
  simp only [neg_one_smul, ← sub_eq_add_neg] at he
  rw [real_inner_comm (finiteSchurCombination z c) h, hi, hn] at he
  change ‖h - finiteSchurCombination z c‖ ^ 2 = _
  linarith

/-- Completion of the square proves that the normal-equation residual is
an optimizer over every coefficient choice. -/
theorem finiteSchurResidual_completion (h : H) (z : ι → H) (c d : ι → ℝ)
    (hd : ∀ i, inner ℝ (z i) (finiteSchurCombination z d) = inner ℝ (z i) h) :
    ‖finiteSchurResidual h z c‖ ^ 2 = ‖finiteSchurResidual h z d‖ ^ 2 +
      ‖finiteSchurCombination z c - finiteSchurCombination z d‖ ^ 2 := by
  have ho (i : ι) : inner ℝ (finiteSchurResidual h z d) (z i) = 0 := by
    rw [real_inner_comm]
    exact finiteSchurResidual_orthogonal h z d hd i
  have hv : inner ℝ (finiteSchurResidual h z d)
      (finiteSchurCombination z c - finiteSchurCombination z d) = 0 := by
    simp [finiteSchurCombination, inner_sub_right, inner_sum, real_inner_smul_right, ho]
  have he : finiteSchurResidual h z c = finiteSchurResidual h z d -
      (finiteSchurCombination z c - finiteSchurCombination z d) := by
    unfold finiteSchurResidual
    abel
  rw [he, norm_sub_sq_real, hv]
  ring

/-- This is the exact block gain `bᵀ S⁻¹ b`, with `e` the full residualized
Gram map, not its diagonal or an unsigned majorant. -/
theorem finiteSchurResidual_inverse_gain (h : H) (z : ι → H)
    (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (he : ∀ c i, e c i = ∑ j, inner ℝ (z i) (z j) * c j) :
    ‖h‖ ^ 2 - ‖finiteSchurResidual h z (e.symm (fun i => inner ℝ (z i) h))‖ ^ 2 =
      ∑ i, e.symm (fun j => inner ℝ (z j) h) i * inner ℝ (z i) h := by
  have hc (i : ι) :
      inner ℝ (z i) (finiteSchurCombination z (e.symm (fun j => inner ℝ (z j) h))) =
        inner ℝ (z i) h := by
    have hh := congrFun (e.apply_symm_apply (fun j => inner ℝ (z j) h)) i
    rw [he] at hh
    simpa [finiteSchurCombination, inner_sum, real_inner_smul_right, mul_comm] using hh
  rw [finiteSchurResidual_norm_sq h z _ hc]
  ring

/-- Orthogonal residualization preserves the full Gram correction term. -/
theorem inner_residualized_eq_schur (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    (x y : H) :
    inner ℝ (x - K.starProjection x) (y - K.starProjection y) =
      inner ℝ x y - inner ℝ (K.starProjection x) (K.starProjection y) := by
  have hxy := (K.mem_orthogonal (y - K.starProjection y)).mp
    (Submodule.sub_starProjection_mem_orthogonal y) _ (K.starProjection_apply_mem x)
  have hyx := (K.mem_orthogonal (x - K.starProjection x)).mp
    (Submodule.sub_starProjection_mem_orthogonal x) _ (K.starProjection_apply_mem y)
  rw [real_inner_comm (x - K.starProjection x) (K.starProjection y)] at hyx
  simp only [inner_sub_left, inner_sub_right] at *
  linarith

end RiemannResearch.LinearAlgebra
