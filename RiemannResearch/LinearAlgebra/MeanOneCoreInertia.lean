/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.RankTwoResidualMean
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# One negative direction and exact mean-one optimization

Source: elementary finite quadratic-form argument for the user's actual
Pareto packet application. Positivity on the mean-zero hyperplane and one
negative witness imply a nonsingular core and an exact Lorentz decomposition.
No arithmetic Gram identity or limiting saturation is assumed implicitly.
-/

noncomputable section
open Matrix
namespace RiemannResearch.LinearAlgebra.MeanOneCoreInertia
open RankTwoResidualMean

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def PositiveOnMeanKernel (F : Matrix ι ι ℝ) (phi : ι → ℝ) : Prop :=
  ∀ x : ι → ℝ, phi ⬝ᵥ x = 0 → x ≠ 0 → 0 < x ⬝ᵥ (F *ᵥ x)

omit [DecidableEq ι] in
theorem quadratic_sub (F : Matrix ι ι ℝ) (hF : Fᵀ = F)
    (x w : ι → ℝ) (t : ℝ) :
    (x - t • w) ⬝ᵥ (F *ᵥ (x - t • w)) =
      x ⬝ᵥ (F *ᵥ x) - 2 * t * (x ⬝ᵥ (F *ᵥ w)) +
        t ^ 2 * (w ⬝ᵥ (F *ᵥ w)) := by
  have hpair : w ⬝ᵥ (F *ᵥ x) = x ⬝ᵥ (F *ᵥ w) := by
    simpa only [hF] using Matrix.dotProduct_transpose_mulVec F w x
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
    dotProduct_sub, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [hpair]
  ring

omit [DecidableEq ι] in
theorem kernel_trivial (F : Matrix ι ι ℝ) (phi : ι → ℝ)
    (hF : Fᵀ = F) (hpos : PositiveOnMeanKernel F phi)
    (w : ι → ℝ) (hw : w ⬝ᵥ (F *ᵥ w) < 0)
    (x : ι → ℝ) (hx : F *ᵥ x = 0) : x = 0 := by
  by_contra hne
  by_cases hm : phi ⬝ᵥ x = 0
  · have hp := hpos x hm hne
    simp [hx] at hp
  · let z := w - ((phi ⬝ᵥ w) / (phi ⬝ᵥ x)) • x
    have hzmean : phi ⬝ᵥ z = 0 := by
      dsimp [z]
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hm]
      ring
    have hzquad : z ⬝ᵥ (F *ᵥ z) = w ⬝ᵥ (F *ᵥ w) := by
      dsimp only [z]
      rw [quadratic_sub F hF, hx]
      simp
    have hz : z ≠ 0 := by
      intro he
      rw [he] at hzquad
      simp at hzquad
      linarith
    have hp := hpos z hzmean hz
    rw [hzquad] at hp
    linarith

theorem det_ne_zero (F : Matrix ι ι ℝ) (phi : ι → ℝ)
    (hF : Fᵀ = F) (hpos : PositiveOnMeanKernel F phi)
    (w : ι → ℝ) (hw : w ⬝ᵥ (F *ᵥ w) < 0) : F.det ≠ 0 := by
  intro hd
  obtain ⟨x, hx, hFx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  exact hx (kernel_trivial F phi hF hpos w hw x hFx)

theorem inverse_charge_neg (F R : Matrix ι ι ℝ) (phi : ι → ℝ)
    (hFR : F * R = 1) (hF : Fᵀ = F)
    (hpos : PositiveOnMeanKernel F phi)
    (v : ι → ℝ) (hv : v ⬝ᵥ (F *ᵥ v) < 0) :
    phi ⬝ᵥ (R *ᵥ phi) < 0 := by
  let w := R *ᵥ phi
  let C := phi ⬝ᵥ w
  have hFw : F *ᵥ w = phi := by
    dsimp only [w]
    rw [Matrix.mulVec_mulVec, hFR, Matrix.one_mulVec]
  have hCw : w ⬝ᵥ (F *ᵥ w) = C := by
    rw [hFw, dotProduct_comm]
  have hphi : phi ≠ 0 := by
    intro he
    have hvne : v ≠ 0 := by intro hh; simp [hh] at hv
    have hp := hpos v (by simp [he]) hvne
    linarith
  have hw : w ≠ 0 := by
    intro he
    apply hphi
    simpa [he] using hFw.symm
  change C < 0
  by_contra hc
  have hc0 : 0 ≤ C := le_of_not_gt hc
  by_cases hzero : C = 0
  · have hp := hpos w hzero hw
    rw [hCw, hzero] at hp
    linarith
  · have hcpos : 0 < C := lt_of_le_of_ne hc0 (Ne.symm hzero)
    let z := v - ((phi ⬝ᵥ v) / C) • w
    have hzmean : phi ⬝ᵥ z = 0 := by
      dsimp only [z]
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
      change phi ⬝ᵥ v - ((phi ⬝ᵥ v) / C) * C = 0
      rw [div_mul_cancel₀ _ hzero, sub_self]
    have hzquad : z ⬝ᵥ (F *ᵥ z) =
        v ⬝ᵥ (F *ᵥ v) - (phi ⬝ᵥ v) ^ 2 / C := by
      dsimp only [z]
      rw [quadratic_sub F hF, hCw, hFw, dotProduct_comm v phi]
      field_simp [hzero]
      ring
    have hzneg : z ⬝ᵥ (F *ᵥ z) < 0 := by
      rw [hzquad]
      have hn := div_nonneg (sq_nonneg (phi ⬝ᵥ v)) hcpos.le
      linarith
    have hz : z ≠ 0 := by intro he; simp [he] at hzneg
    have hp := hpos z hzmean hz
    linarith

theorem lorentz_completion (F R : Matrix ι ι ℝ) (phi x : ι → ℝ)
    (hFR : F * R = 1) (hF : Fᵀ = F)
    (hC : phi ⬝ᵥ (R *ᵥ phi) ≠ 0) :
    let C := phi ⬝ᵥ (R *ᵥ phi)
    let z := x - ((phi ⬝ᵥ x) / C) • (R *ᵥ phi)
    phi ⬝ᵥ z = 0 ∧
      x ⬝ᵥ (F *ᵥ x) = (phi ⬝ᵥ x) ^ 2 / C + z ⬝ᵥ (F *ᵥ z) := by
  dsimp only
  have hFw : F *ᵥ (R *ᵥ phi) = phi := by
    rw [Matrix.mulVec_mulVec, hFR, Matrix.one_mulVec]
  constructor
  · rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hC]
    ring
  · rw [quadratic_sub F hF, hFw, dotProduct_comm x phi,
      dotProduct_comm (R *ᵥ phi) phi]
    field_simp [hC]
    ring

theorem constrained_unique_minimum (p : ℝ) (F R Xi : Matrix ι ι ℝ)
    (phi L y : ι → ℝ) (hp : 0 < p)
    (hFR : F * R = 1) (hF : Fᵀ = F)
    (hXi : Xi = RankTwoWoodbury.rankTwoMatrix p F L phi)
    (hC : phi ⬝ᵥ (R *ᵥ phi) ≠ 0)
    (hpos : PositiveOnMeanKernel F phi) (hy : phi ⬝ᵥ y = 2) :
    let C := phi ⬝ᵥ (R *ᵥ phi)
    let c0 := (2 / C) • (R *ᵥ phi)
    (1 + 4 * p / C ≤ 1 - 2 * (L ⬝ᵥ y) + y ⬝ᵥ (Xi *ᵥ y)) ∧
      (1 - 2 * (L ⬝ᵥ y) + y ⬝ᵥ (Xi *ᵥ y) = 1 + 4 * p / C ↔ y = c0) := by
  dsimp only
  obtain ⟨hm, he⟩ := constrained_mean_completion p F R Xi phi L y hFR hF hXi hC hy
  have hzmean : phi ⬝ᵥ (y - (2 / (phi ⬝ᵥ (R *ᵥ phi))) • (R *ᵥ phi)) = 0 := by
    rw [dotProduct_sub, hy, hm, sub_self]
  by_cases hz : y = (2 / (phi ⬝ᵥ (R *ᵥ phi))) • (R *ᵥ phi)
  · rw [hz, sub_self] at he
    simp only [Matrix.mulVec_zero, dotProduct_zero, mul_zero, add_zero] at he
    have heY : 1 - 2 * (L ⬝ᵥ y) + y ⬝ᵥ (Xi *ᵥ y) =
        1 + 4 * p / (phi ⬝ᵥ (R *ᵥ phi)) := by simpa only [hz] using he
    exact ⟨heY.ge, by rw [heY]; simp only [hz]⟩
  · have hq := hpos _ hzmean (sub_ne_zero.mpr hz)
    have hstrict : 1 + 4 * p / (phi ⬝ᵥ (R *ᵥ phi)) <
        1 - 2 * (L ⬝ᵥ y) + y ⬝ᵥ (Xi *ᵥ y) := by
      rw [he]
      exact lt_add_of_pos_right _ (mul_pos hp hq)
    exact ⟨hstrict.le, by simp [ne_of_gt hstrict, hz]⟩

end RiemannResearch.LinearAlgebra.MeanOneCoreInertia
