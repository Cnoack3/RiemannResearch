/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Orthogonal pairing energy and finite-energy perturbations

Source: the standard Bessel inequality as formalized by Mathlib's
Orthonormal.inner_products_summable and Orthonormal.tsum_inner_products_le
supports the proof strategy. The concrete consumer is the signed
factorial cross-Gram row problem in the Pareto RH program.
-/

noncomputable section
namespace RiemannResearch.Analysis.OrthogonalPairingEnergy
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem normalized_orthonormal (v : ι → H)
    (ho : Pairwise (fun i j => inner ℝ (v i) (v j) = 0))
    (hv : ∀ i, v i ≠ 0) :
    Orthonormal ℝ (fun i => (‖v i‖ : ℝ)⁻¹ • v i) := by
  constructor
  · intro i
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hv i))
  · intro i j hij
    simp [real_inner_smul_left, inner_smul_right, ho hij]

theorem pairing_energy_summable (v : ι → H)
    (ho : Pairwise (fun i j => inner ℝ (v i) (v j) = 0))
    (hv : ∀ i, v i ≠ 0) (x : H) :
    Summable (fun i => (inner ℝ (v i) x)^2 / ‖v i‖^2) := by
  have hs := (normalized_orthonormal v ho hv).inner_products_summable x
  convert hs using 1
  ext i
  simp only [real_inner_smul_left, Real.norm_eq_abs, sq_abs, mul_pow]
  ring

theorem pairing_energy_tsum_le (v : ι → H)
    (ho : Pairwise (fun i j => inner ℝ (v i) (v j) = 0))
    (hv : ∀ i, v i ≠ 0) (x : H) :
    (∑' i, (inner ℝ (v i) x)^2 / ‖v i‖^2) ≤ ‖x‖^2 := by
  convert (normalized_orthonormal v ho hv).tsum_inner_products_le x using 1
  congr 1
  ext i
  simp only [real_inner_smul_left, Real.norm_eq_abs, sq_abs, mul_pow]
  ring

/-- Adding a square-summable signed sequence preserves weighted square
summability. The weights need only be nonnegative. -/
theorem weighted_square_add_summable_iff (a b w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hb : Summable (fun i => (b i)^2 / w i)) :
    Summable (fun i => (a i + b i)^2 / w i) ↔
      Summable (fun i => (a i)^2 / w i) := by
  constructor
  · intro hab
    apply Summable.of_nonneg_of_le
      (fun i => div_nonneg (sq_nonneg _) (hw i)) _ ((hab.mul_left 2).add (hb.mul_left 2))
    intro i
    have h : (a i)^2 ≤ 2 * (a i + b i)^2 + 2 * (b i)^2 := by
      nlinarith [sq_nonneg (a i + 2 * b i)]
    calc
      _ ≤ (2 * (a i + b i)^2 + 2 * (b i)^2) / w i :=
        div_le_div_of_nonneg_right h (hw i)
      _ = _ := by ring
  · intro ha
    apply Summable.of_nonneg_of_le
      (fun i => div_nonneg (sq_nonneg _) (hw i)) _ ((ha.mul_left 2).add (hb.mul_left 2))
    intro i
    have h : (a i + b i)^2 ≤ 2 * (a i)^2 + 2 * (b i)^2 := by
      nlinarith [sq_nonneg (a i - b i)]
    calc
      _ ≤ (2 * (a i)^2 + 2 * (b i)^2) / w i :=
        div_le_div_of_nonneg_right h (hw i)
      _ = _ := by ring
end RiemannResearch.Analysis.OrthogonalPairingEnergy
