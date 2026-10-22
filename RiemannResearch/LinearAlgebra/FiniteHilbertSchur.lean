import Mathlib.Analysis.InnerProductSpace.PiL2
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




/-!
Source: user-provided argument,
`RH_Controlled_Conductor_Schur_2026-09-10.md`, Sections 4 and 5.5.
The following results cover singular designs and the full signed covariance update.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.LinearAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {ι : Type*} [Fintype ι]

/-- Normal equations always have a solution for a finite packet family,
including redundant and singular families. No inverse hypothesis is used. -/
theorem finiteSchur_exists_normal (x : H) (z : ι → H) :
    ∃ b : ι → ℝ, ∀ i,
      inner ℝ (z i) (finiteSchurCombination z b) = inner ℝ (z i) x := by
  let W : Submodule ℝ H := Submodule.span ℝ (Set.range z)
  have : FiniteDimensional ℝ W :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range z)
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (W.starProjection_apply_mem x)
  refine ⟨b, ?_⟩
  intro i
  have hz : z i ∈ W := Submodule.subset_span ⟨i, rfl⟩
  have ho := (W.mem_orthogonal _).mp
    (Submodule.sub_starProjection_mem_orthogonal x) (z i) hz
  have hc : finiteSchurCombination z b = W.starProjection x := hb
  rw [hc]
  rw [inner_sub_right] at ho
  exact (sub_eq_zero.mp ho).symm

/-- The exact minimum and full quadratic remainder are attained even in
singular designs. This is the inverse-free content of the Schur gain. -/
theorem finiteSchur_exists_exact_minimum (x : H) (z : ι → H) :
    ∃ b : ι → ℝ,
      (∀ i, inner ℝ (z i) (finiteSchurCombination z b) = inner ℝ (z i) x) ∧
      ∀ c : ι → ℝ, ‖finiteSchurResidual x z c‖ ^ 2 =
        ‖x‖ ^ 2 - ∑ i, b i * inner ℝ (z i) x +
          ‖finiteSchurCombination z c - finiteSchurCombination z b‖ ^ 2 := by
  obtain ⟨b, hb⟩ := finiteSchur_exists_normal x z
  refine ⟨b, hb, ?_⟩
  intro c
  rw [finiteSchurResidual_completion x z c b hb, finiteSchurResidual_norm_sq x z b hb]

/-- Full bilinear residual covariance. Once the first residual is normal,
the second control coefficients can be arbitrary. -/
theorem finiteSchurResidual_inner (x y : H) (z : ι → H) (b c : ι → ℝ)
    (hb : ∀ i, inner ℝ (z i) (finiteSchurCombination z b) = inner ℝ (z i) x) :
    inner ℝ (finiteSchurResidual x z b) (finiteSchurResidual y z c) =
      inner ℝ x y - ∑ i, b i * inner ℝ (z i) y := by
  have hi (i : ι) : inner ℝ (finiteSchurResidual x z b) (z i) = 0 := by
    rw [real_inner_comm]
    exact finiteSchurResidual_orthogonal x z b hb i
  have hc : inner ℝ (finiteSchurResidual x z b) (finiteSchurCombination z c) = 0 := by
    simp [finiteSchurCombination, inner_sum, real_inner_smul_right, hi]
  change inner ℝ (finiteSchurResidual x z b) (y - finiteSchurCombination z c) = _
  rw [inner_sub_right, hc, sub_zero]
  simp [finiteSchurResidual, finiteSchurCombination, inner_sub_left,
    sum_inner, real_inner_smul_left]

/-- The exact inverse of the full Gram action supplies the normal equations. -/
theorem finiteSchur_inverse_normal (x : H) (z : ι → H)
    (G : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (hG : ∀ b i, G b i = ∑ j, inner ℝ (z i) (z j) * b j) (i : ι) :
    inner ℝ (z i) (finiteSchurCombination z (G.symm (fun j => inner ℝ (z j) x))) =
      inner ℝ (z i) x := by
  have h := congrFun (G.apply_symm_apply (fun j => inner ℝ (z j) x)) i
  rw [hG] at h
  simpa [finiteSchurCombination, inner_sum, real_inner_smul_right, mul_comm] using h

/-- Full matrix covariance Schur update, simultaneously for every pair of
signal directions. This is the entrywise identity Σnew = Σold - BᵀK⁻¹B. -/
theorem finiteSchurResidual_inverse_covariance (x y : H) (z : ι → H)
    (G : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (hG : ∀ b i, G b i = ∑ j, inner ℝ (z i) (z j) * b j) :
    inner ℝ (finiteSchurResidual x z (G.symm (fun i => inner ℝ (z i) x)))
      (finiteSchurResidual y z (G.symm (fun i => inner ℝ (z i) y))) =
      inner ℝ x y - ∑ i, G.symm (fun j => inner ℝ (z j) x) i * inner ℝ (z i) y := by
  exact finiteSchurResidual_inner x y z _ _ (finiteSchur_inverse_normal x z G hG)

/-- Even a singular packet design has zero optimized gain exactly when
every actual marked score vanishes. Independence alone does not give gain. -/
theorem finiteSchurResidual_gain_zero_iff (x : H) (z : ι → H) (b : ι → ℝ)
    (hb : ∀ i, inner ℝ (z i) (finiteSchurCombination z b) = inner ℝ (z i) x) :
    ‖x‖ ^ 2 - ‖finiteSchurResidual x z b‖ ^ 2 = 0 ↔
      ∀ i, inner ℝ (z i) x = 0 := by
  have hn : ‖finiteSchurCombination z b‖ ^ 2 = ∑ i, b i * inner ℝ (z i) x := by
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => arg 2; unfold finiteSchurCombination
    simp only [sum_inner, real_inner_smul_left, hb]
  have he := finiteSchurResidual_norm_sq x z b hb
  constructor
  · intro hzero
    have hnorm : ‖finiteSchurCombination z b‖ = 0 := by nlinarith
    have hz : finiteSchurCombination z b = 0 := norm_eq_zero.mp hnorm
    intro i
    simpa only [hz, inner_zero_right] using (hb i).symm
  · intro hscore
    simp only [hscore, mul_zero, Finset.sum_const_zero, sub_zero] at he
    linarith

end RiemannResearch.LinearAlgebra
