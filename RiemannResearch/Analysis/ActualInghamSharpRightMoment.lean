/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualInghamMobiusCoefficients
import RiemannResearch.Analysis.InghamCoefficientMeanSquare
import RiemannResearch.Analysis.DirichletCoefficientTailAbel

/-!
# The coefficient estimates for the sharp right-line moment

The signed least-common-multiple form evaluates both the diagonal and the
weighted error of the actual mean square. A uniform linear prefix estimate
for the squared divisor coefficients gives an additional saving on long
intervals. The arithmetic prefix estimate is (1.5) of R. de la Bretèche,
F. Dress and G. Tenenbaum, *Remarques sur une somme liée à la fonction de
Möbius*, Mathematika 66 (2020), 416–421, doi:10.1112/mtk.12021.
The moving-line endpoint is used in Chourasiya–Simonič, arXiv:2507.15184,
Lemma 6. All intervals here may be translated.
-/
noncomputable section
open MeasureTheory Complex Filter
open scoped BigOperators
namespace RiemannResearch.Analysis.InghamMollifier
open DirichletMeanSquare

private theorem divisor_weight (X n : ℕ) (p : ℝ) :
    coefficientSquareWeight (fun k => (truncatedMobiusDivisorSum X k : ℂ)) p n =
      (truncatedMobiusDivisorSum X n)^2 * (n : ℝ)^(-p) := by
  simp [coefficientSquareWeight, Complex.norm_real, Real.norm_eq_abs, sq_abs]

private theorem divisor_abs_summable (X : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun k : ℕ => ‖(truncatedMobiusDivisorSum X (k+X+1) : ℂ)‖ *
      ((k+X+1 : ℕ) : ℝ)^(-σ)) := by
  apply ((summable_tail_rpow hσ X).mul_left (X : ℝ)).of_nonneg_of_le
  · intro k
    positivity
  · intro k
    exact mul_le_mul_of_nonneg_right (norm_truncatedMobiusDivisorSum_le X _) (by positivity)

private theorem divisor_weight_summable (X : ℕ) {τ : ℝ} (hτ : 1 < τ) :
    Summable (fun k : ℕ => coefficientSquareWeight
      (fun n => (truncatedMobiusDivisorSum X n : ℂ)) τ (k+X+1)) := by
  simpa only [divisor_weight] using summable_truncatedMobiusDivisorSum_tail_energy X hτ

set_option maxHeartbeats 1600000 in
/-- The signed diagonal and its full two-sided precision, both as finite lcm forms. -/
theorem abs_actual_right_error_moment_sub_lcm_diagonal_le {σ : ℝ} (hσ : 1 < σ)
    {X : ℕ} (hX : 1 ≤ X) {H T : ℝ} (hHT : H ≤ T) :
    |(∫ t in H..T, ‖riemannZeta ((σ : ℂ) + I*t) *
      mollifier X ((σ : ℂ) + I*t) - 1‖ ^ 2) -
      (T-H) * (‖riemannZeta ((2*σ : ℝ) : ℂ)‖ * truncatedMobiusLCMForm X (2*σ) - 1)| ≤
      52 * (‖riemannZeta ((2*σ-1 : ℝ) : ℂ)‖ * truncatedMobiusLCMForm X (2*σ-1) - 1) := by
  have hd : 1 < 2*σ := by linarith
  have hw : 1 < 2*σ-1 := by linarith
  have hh := abs_dirichletTail_mean_square_sub_diagonal_le
    (a := fun n => (truncatedMobiusDivisorSum X n : ℂ)) (σ := σ) (X := X) (H := H) (T := T)
    (divisor_abs_summable X hσ)
    (divisor_weight_summable X hd) (divisor_weight_summable X hw) hHT
  simpa only [mollifier_error_eq_divisor_dirichletTail hσ hX, divisor_weight,
    truncatedMobiusDivisorSum_tail_energy_eq_lcm hX hd,
    truncatedMobiusDivisorSum_tail_energy_eq_lcm hX hw] using hh

set_option maxHeartbeats 1600000 in
/-- Tail support controls both parts from one finite signed arithmetic form. -/
theorem actual_right_error_moment_le_lcm {σ : ℝ} (hσ : 1 < σ)
    {X : ℕ} (hX : 1 ≤ X) {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T, ‖riemannZeta ((σ : ℂ) + I*t) *
      mollifier X ((σ : ℂ) + I*t) - 1‖ ^ 2) ≤ ((T-H)/X + 52) *
      (‖riemannZeta ((2*σ-1 : ℝ) : ℂ)‖ * truncatedMobiusLCMForm X (2*σ-1) - 1) := by
  have hw : 1 < 2*σ-1 := by linarith
  have hh := dirichletTail_mean_square_le_one_energy
    (a := fun n => (truncatedMobiusDivisorSum X n : ℂ)) (σ := σ) (X := X) (H := H) (T := T)
    hX (divisor_abs_summable X hσ)
    (divisor_weight_summable X (by linarith : 1 < 2*σ)) (divisor_weight_summable X hw) hHT
  simpa only [mollifier_error_eq_divisor_dirichletTail hσ hX, divisor_weight,
    truncatedMobiusDivisorSum_tail_energy_eq_lcm hX hw] using hh

/-- Explicit sharp moving-line transfer from a single finite lcm bound. -/
theorem actual_moving_right_error_moment_le_of_lcm {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    {X : ℕ} (hX : 2 ≤ X) {H T : ℝ} (hHT : H ≤ T)
    (hform : truncatedMobiusLCMForm X (1 + 2 * δ / Real.log X) ≤ B) :
    (∫ t in H..T, ‖riemannZeta (((1+δ/Real.log X : ℝ) : ℂ) + I*t) *
      mollifier X (((1+δ/Real.log X : ℝ) : ℂ) + I*t) - 1‖ ^ 2) ≤
      ((T-H)/X + 52) * ((1 + Real.log X / (2*δ))*B - 1) := by
  have hx : (1:ℝ) < X := by exact_mod_cast hX
  have hl := Real.log_pos hx
  have hσ : 1 < 1+δ/Real.log X := by linarith [div_pos hδ hl]
  have hτ : 1 < 1+2*δ/Real.log X := by linarith [div_pos (mul_pos two_pos hδ) hl]
  have hu := actual_right_error_moment_le_lcm hσ (by omega : 1 ≤ X) hHT
  rw [show 2*(1+δ/Real.log X)-1 = 1+2*δ/Real.log X by ring] at hu
  have hz : ‖riemannZeta ((1+2*δ/Real.log X : ℝ) : ℂ)‖ ≤ 1+Real.log X/(2*δ) := by
    have hh := norm_riemannZeta_le_integral_test
      (show 1 < (((1+2*δ/Real.log X : ℝ) : ℂ)).re from hτ)
    simp only [Complex.ofReal_re] at hh
    convert hh using 1
    field_simp
    ring
  apply hu.trans
  apply mul_le_mul_of_nonneg_left _ (by have := sub_nonneg.mpr hHT; positivity)
  exact sub_le_sub_right ((mul_le_mul_of_nonneg_left hform (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_right hz hB)) _

/-- The uniform finite arithmetic estimate appearing in (1.5) of de la
Bretèche–Dress–Tenenbaum. In this formulation the constant is exposed. -/
def DivisorSquarePrefixBound (C : ℝ) : Prop :=
  ∀ X n : ℕ, 2 ≤ X →
    (∑ i ∈ Finset.range (n+1), (truncatedMobiusDivisorSum X i)^2) ≤ C*n

set_option maxHeartbeats 1600000 in
/-- The Abel-summed alternative saves a logarithm on the interval-length term. -/
theorem actual_right_error_moment_le_of_divisor_prefix {C η : ℝ} (hC : 0 ≤ C)
    (hprefix : DivisorSquarePrefixBound C) (hη : 0 < η) {X : ℕ} (hX : 2 ≤ X)
    {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T, ‖riemannZeta (((1+η : ℝ) : ℂ) + I*t) *
      mollifier X (((1+η : ℝ) : ℂ) + I*t) - 1‖ ^ 2) ≤
      (T-H) * (C*(2+2*η)/(1+2*η) * (X : ℝ)^(-1-2*η)) +
      52 * (C*(1+2*η)/(2*η) * (X : ℝ)^(-2*η)) := by
  have hX' : 1 ≤ X := by omega
  have hσ : 1 < 1+η := by linarith
  have hd : 1 < 2*(1+η) := by linarith
  have hw : 1 < 2*(1+η)-1 := by linarith
  have hp := fun n : ℕ => hprefix X n hX
  have hA := (coefficient_rpow_tail_of_linear_prefix
    (fun n => sq_nonneg (truncatedMobiusDivisorSum X n)) hC hX' hd hp).2
  have hB := (coefficient_rpow_tail_of_linear_prefix
    (fun n => sq_nonneg (truncatedMobiusDivisorSum X n)) hC hX' hw hp).2
  have hh := (abs_le.mp (abs_dirichletTail_mean_square_sub_diagonal_le
    (a := fun n => (truncatedMobiusDivisorSum X n : ℂ))
    (σ := 1+η) (X := X) (H := H) (T := T)
    (divisor_abs_summable X hσ) (divisor_weight_summable X hd)
    (divisor_weight_summable X hw) hHT)).2
  simp only [divisor_weight] at hh
  simp only [mollifier_error_eq_divisor_dirichletTail hσ hX']
  have h := (sub_le_iff_le_add.mp hh).trans (add_le_add
    (mul_le_mul_of_nonneg_left hB (by norm_num : (0:ℝ) ≤ 52))
    (mul_le_mul_of_nonneg_left hA (sub_nonneg.mpr hHT)))
  simp only [show 2*(1+η) = 2+2*η by ring, show 2+2*η-1 = 1+2*η by ring,
    show 1+2*η-1 = 2*η by ring, show 1-(2+2*η) = -1-2*η by ring,
    show 1-(1+2*η) = -2*η by ring] at h
  exact h.trans_eq (add_comm _ _)

/-- A fixed positive δ gives the stronger translated-interval estimate
O_δ((T-H)/X + log X) under the finite arithmetic prefix estimate. -/
theorem actual_moving_right_error_moment_le_of_divisor_prefix {C δ : ℝ}
    (hC : 0 ≤ C) (hprefix : DivisorSquarePrefixBound C) (hδ : 0 < δ)
    {X : ℕ} (hX : 2 ≤ X) {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T, ‖riemannZeta (((1+δ/Real.log X : ℝ) : ℂ) + I*t) *
      mollifier X (((1+δ/Real.log X : ℝ) : ℂ) + I*t) - 1‖ ^ 2) ≤
      C*Real.exp (-2*δ) * (2*((T-H)/X) + 52 + 26*Real.log X/δ) := by
  have hx : (1:ℝ) < X := by exact_mod_cast hX
  have hx0 : 0 < (X:ℝ) := by linarith
  have hl := Real.log_pos hx
  let η := δ / Real.log X
  have hη : 0 < η := div_pos hδ hl
  have hh := actual_right_error_moment_le_of_divisor_prefix hC hprefix hη hX hHT
  have hex : (X : ℝ)^(-2*η) = Real.exp (-2*δ) := by
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    dsimp [η]
    field_simp
  have hdex : (X : ℝ)^(-1-2*η) = Real.exp (-2*δ) / X := by
    rw [show -1-2*η = (-2*η)-1 by ring, Real.rpow_sub hx0, Real.rpow_one, hex]
  have hfrac : C*(2+2*η)/(1+2*η) ≤ 2*C := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg hC hη.le]
  rw [hex, hdex] at hh
  apply hh.trans
  calc
    _ ≤ (T-H) * (2*C * (Real.exp (-2*δ)/X)) +
        52 * (C*(1+2*η)/(2*η) * Real.exp (-2*δ)) := by
      gcongr
    _ = _ := by
      dsimp [η]
      field_simp
      ring

end RiemannResearch.Analysis.InghamMollifier
