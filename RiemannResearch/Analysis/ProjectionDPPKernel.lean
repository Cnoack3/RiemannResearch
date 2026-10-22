import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Projection kernels and complementary Gram kernels

Source: user-provided DPP handoff, Sections 1 and 5; the terminology follows
Hough--Krishnapur--Peres--Virag, arXiv:math/0503110. These are deterministic
Hilbert-space facts. The arithmetic consumer is RH/IntegerDPPReduction.
-/

noncomputable section
namespace RiemannResearch.Analysis.ProjectionDPP
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (S : Submodule ℝ H) [S.HasOrthogonalProjection] (e : ι → H)

def kernel (i j : ι) : ℝ := inner ℝ (S.starProjection (e i)) (S.starProjection (e j))

def holeKernel (i j : ι) : ℝ :=
  inner ℝ (e i - S.starProjection (e i)) (e j - S.starProjection (e j))

theorem kernel_symmetric (i j : ι) : kernel S e i j = kernel S e j i :=
  real_inner_comm _ _

theorem kernel_diagonal (i : ι) : kernel S e i i = ‖S.starProjection (e i)‖ ^ 2 :=
  real_inner_self_eq_norm_sq _

theorem holeKernel_diagonal (i : ι) :
    holeKernel S e i i = ‖e i - S.starProjection (e i)‖ ^ 2 :=
  real_inner_self_eq_norm_sq _

theorem holeKernel_eq (i j : ι) :
    holeKernel S e i j = inner ℝ (e i) (e j) - kernel S e i j := by
  have h₁ : inner ℝ (S.starProjection (e i)) (e j - S.starProjection (e j)) = 0 :=
    (S.mem_orthogonal _).mp (Submodule.sub_starProjection_mem_orthogonal (e j)) _
      (S.starProjection_apply_mem (e i))
  have h₂ : inner ℝ (e i - S.starProjection (e i)) (S.starProjection (e j)) = 0 := by
    rw [real_inner_comm]
    exact (S.mem_orthogonal _).mp (Submodule.sub_starProjection_mem_orthogonal (e i)) _
      (S.starProjection_apply_mem (e j))
  dsimp [holeKernel, kernel]
  simp only [inner_sub_left, inner_sub_right] at h₁ h₂ ⊢
  linarith

theorem diagonal_bounds (i : ι) (hi : ‖e i‖ ^ 2 = 1) :
    0 ≤ kernel S e i i ∧ kernel S e i i ≤ 1 := by
  have hp : 0 ≤ kernel S e i i := by rw [kernel_diagonal]; positivity
  have hq : 0 ≤ holeKernel S e i i := by rw [holeKernel_diagonal]; positivity
  rw [holeKernel_eq, real_inner_self_eq_norm_sq, hi] at hq
  exact ⟨hp, by linarith⟩

theorem diagonal_one_iff (i : ι) (hi : ‖e i‖ ^ 2 = 1) :
    kernel S e i i = 1 ↔ e i ∈ S := by
  have he : 1 - kernel S e i i = ‖e i - S.starProjection (e i)‖ ^ 2 := by
    rw [← holeKernel_diagonal, holeKernel_eq, real_inner_self_eq_norm_sq, hi]
  constructor
  · intro h
    have hz : ‖e i - S.starProjection (e i)‖ ^ 2 = 0 := by rw [← he, h]; ring
    have hp := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
    exact Submodule.starProjection_eq_self_iff.mp hp.symm
  · intro h
    rw [kernel_diagonal, Submodule.starProjection_eq_self_iff.mpr h, hi]

theorem principal_posSemidef {κ : Type*} [Finite κ] (a : κ → ι) :
    (Matrix.of (fun i j => kernel S e (a i) (a j))).PosSemidef :=
  Matrix.posSemidef_gram ℝ (fun i => S.starProjection (e (a i)))

theorem hole_principal_posSemidef {κ : Type*} [Finite κ] (a : κ → ι) :
    (Matrix.of (fun i j => holeKernel S e (a i) (a j))).PosSemidef :=
  Matrix.posSemidef_gram ℝ (fun i => e (a i) - S.starProjection (e (a i)))

theorem principal_det_nonneg {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ → ι) :
    0 ≤ Matrix.det (Matrix.of (fun i j => kernel S e (a i) (a j))) :=
  (principal_posSemidef S e a).det_nonneg

theorem identity_sub_principal_posSemidef {κ : Type*} [Fintype κ] [DecidableEq κ]
    (a : κ → ι) (ha : ∀ i j, inner ℝ (e (a i)) (e (a j)) = if i = j then 1 else 0) :
    (1 - Matrix.of (fun i j => kernel S e (a i) (a j))).PosSemidef := by
  have he : (1 - Matrix.of (fun i j => kernel S e (a i) (a j))) =
      Matrix.of (fun i j => holeKernel S e (a i) (a j)) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, holeKernel_eq, ha]
  rw [he]
  exact hole_principal_posSemidef S e a

end RiemannResearch.Analysis.ProjectionDPP

namespace RiemannResearch.Analysis.ProjectionDPP
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (S T : Submodule ℝ H) [S.HasOrthogonalProjection] [T.HasOrthogonalProjection]
    (hST : S ≤ T) (e : ι → H)

include hST

theorem nested_kernel_difference (i j : ι) :
    kernel T e i j - kernel S e i j =
      inner ℝ (T.starProjection (e i) - S.starProjection (e i))
        (T.starProjection (e j) - S.starProjection (e j)) := by
  have h₁ : inner ℝ (S.starProjection (e j))
      (e i - T.starProjection (e i)) = 0 :=
    (T.mem_orthogonal _).mp (Submodule.sub_starProjection_mem_orthogonal (e i)) _
      (hST (S.starProjection_apply_mem (e j)))
  have h₂ : inner ℝ (S.starProjection (e j))
      (e i - S.starProjection (e i)) = 0 :=
    (S.mem_orthogonal _).mp (Submodule.sub_starProjection_mem_orthogonal (e i)) _
      (S.starProjection_apply_mem (e j))
  have h₃ : inner ℝ (S.starProjection (e i))
      (e j - T.starProjection (e j)) = 0 :=
    (T.mem_orthogonal _).mp (Submodule.sub_starProjection_mem_orthogonal (e j)) _
      (hST (S.starProjection_apply_mem (e i)))
  have h₄ : inner ℝ (S.starProjection (e i))
      (e j - S.starProjection (e j)) = 0 :=
    (S.mem_orthogonal _).mp (Submodule.sub_starProjection_mem_orthogonal (e j)) _
      (S.starProjection_apply_mem (e i))
  simp only [inner_sub_right] at h₁ h₂ h₃ h₄
  have hc₁ := real_inner_comm (S.starProjection (e j)) (T.starProjection (e i))
  have hc₂ := real_inner_comm (S.starProjection (e j)) (S.starProjection (e i))
  simp only [kernel, inner_sub_left, inner_sub_right]
  linarith

theorem nested_principal_difference_posSemidef {κ : Type*} [Finite κ] (a : κ → ι) :
    (Matrix.of (fun i j => kernel T e (a i) (a j) - kernel S e (a i) (a j))).PosSemidef := by
  simp_rw [nested_kernel_difference S T hST e]
  exact Matrix.posSemidef_gram ℝ _
end RiemannResearch.Analysis.ProjectionDPP
