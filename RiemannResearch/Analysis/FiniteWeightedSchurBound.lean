/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.FiniteQuadraticCoshCorrection

/-!
# Finite weighted Schur bound in Euclidean operator norm

A symmetric nonnegative entry majorant and a positive row weight control
the actual complex matrix in its Hilbert-space operator norm.
-/

noncomputable section
open Complex
open scoped BigOperators
namespace RiemannResearch.Analysis.ActualZeroPhaseMoments

theorem euclideanCLM_norm_le_weightedSchur {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (k : Fin d → Fin d → ℝ) (w : Fin d → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ i, 0 < w i) (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j = k j i)
    (hA : ∀ i j, ‖A i j‖ ≤ k i j) (hrow : ∀ i, ∑ j, k i j*w j ≤ M*w i) :
    ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A‖ ≤ M := by
  let b := fun i j : Fin d => k i j*w j/w i
  have hb (i j) : 0 ≤ b i j := div_nonneg (mul_nonneg (hk _ _) (hw _).le) (hw _).le
  have htotal (i) : ∑ j, b i j ≤ M := by
    dsimp [b]
    rw [← Finset.sum_div]
    exact (div_le_iff₀ (hw i)).mpr (hrow i)
  have hpair (i j) : Real.sqrt (b i j)*Real.sqrt (b j i) = k i j := by
    rw [← Real.sqrt_mul (hb i j)]
    have he : b i j*b j i = (k i j)^2 := by
      dsimp [b]; rw [hsym j i]; field_simp [(hw i).ne',(hw j).ne']
    rw [he,Real.sqrt_sq (hk i j)]
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro v
  let Av := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A v
  have hpoint (i : Fin d) : ‖Av i‖^2 ≤ M*∑ j, b j i*‖v j‖^2 := by
    have he : Av i = ∑ j, A i j*v j := congrFun (Matrix.ofLp_toEuclideanCLM A v) i
    have hsum := _root_.norm_sum_le (Finset.univ : Finset (Fin d)) (fun j => A i j*v j)
    simp only [norm_mul] at hsum
    have hmaj : ‖Av i‖ ≤ ∑ j, Real.sqrt (b i j)*(Real.sqrt (b j i)*‖v j‖) := by
      rw [he]
      apply hsum.trans
      apply Finset.sum_le_sum
      intro j _
      rw [← mul_assoc,hpair]
      exact mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _)
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => Real.sqrt (b i j))
      (fun j => Real.sqrt (b j i)*‖v j‖)
    simp_rw [mul_pow,Real.sq_sqrt (hb _ _)] at hcs
    exact ((pow_le_pow_left₀ (norm_nonneg _) hmaj 2).trans hcs).trans
      (mul_le_mul_of_nonneg_right (htotal i) (Finset.sum_nonneg fun j _ => mul_nonneg (hb _ _) (sq_nonneg _)))
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  have h : ‖Av‖^2 ≤ M*(M*‖v‖^2) := by
    rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
    apply hsum.trans
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ hM
    rw [Finset.sum_comm,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (htotal j) (sq_nonneg _)
  nlinarith only [h,norm_nonneg Av,mul_nonneg hM (norm_nonneg v)]

end RiemannResearch.Analysis.ActualZeroPhaseMoments
