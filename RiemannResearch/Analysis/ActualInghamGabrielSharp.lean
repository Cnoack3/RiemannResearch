/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualInghamGabrielMovingWindow
import RiemannResearch.Analysis.ActualInghamSharpEndpoint

/-!
# The actual Gabriel inequality with both endpoint estimates supplied

This is the finite-window specialization of mixed-norm Gabriel interpolation
used in Chourasiya–Simonič, arXiv:2507.15184, §3, equation (30). The
Gaussian height parameter is arbitrary. The right-hand constant depends
only on the fixed moving-line parameter. The left-hand constant is absolute.
-/
noncomputable section
open Set Complex MeasureTheory
open RiemannResearch.Analysis.InghamInterpolation
namespace RiemannResearch.Analysis.InghamMollifier

private theorem boundaryBudget_nonneg (X : ℕ) {T b p : ℝ} (hT : 0 ≤ T)
    (x : ℝ) : 0 ≤ gabrielBoundaryBudget X T b x p := by
  apply mul_nonneg (Real.exp_pos _).le
  apply integral_nonneg
  intro u
  apply mul_nonneg (Real.exp_pos _).le
  apply intervalIntegral.integral_nonneg
  · dsimp [gabrielGaussianScale]
    positivity
  · exact fun _ _ => Real.rpow_nonneg (norm_nonneg _) _

/-- The two-log critical endpoint and the sharp one-log moving endpoint
give an unconditional observed moment, uniformly across the whole strip. -/
theorem exists_actual_gabriel_sharp_window {δ : ℝ} (hδ : 0 < δ) :
    ∃ Cₗ Cᵣ : ℝ, 0 < Cₗ ∧ 0 < Cᵣ ∧ ∀ {X : ℕ}, 2 ≤ X →
      ∀ {T H b θ : ℝ}, 2 ≤ T → (X : ℝ) ≤ T → 1 ≤ H → H ≤ T → 0 < b →
      θ ∈ Icc (0 : ℝ) 1 →
      let β := 1 + δ / Real.log (X : ℝ)
      let σ := 1 / 2 + (β - 1 / 2) * θ
      let p := 4 / (3 - θ)
      let aₗ := gabrielGaussianScale T b (4 / 3)
      let aᵣ := gabrielGaussianScale T b 2
      let L := Real.exp ((4/3)*b*(1/2)^2) * (Cₗ*T*(1+Real.log T)^2*(1+aₗ)^3)
      let R := Real.exp (2*b*β^2) *
        (Cᵣ * Real.log X * (1+(T*aᵣ/X)*Real.Gamma (3/2)))
      Real.exp (b*(σ^2-T^2)) * (1-1/H) *
        (∫ t in H..T, stripMomentDensity (mollifiedError X) σ p t)^((3-θ)/4) ≤
        (L^(3/4 : ℝ))^(1-θ) * (R^(1/2 : ℝ))^θ := by
  obtain ⟨Cl, hl, hleft⟩ := exists_actual_gabriel_left_endpoint_bound
  obtain ⟨Cr, hr, hright⟩ := exists_actual_gabriel_right_endpoint_log_one hδ
  refine ⟨Cl, Cr, hl, hr, ?_⟩
  intro X hX T H b θ hT hXT hH hHT hb hθ
  let β := 1 + δ / Real.log (X : ℝ)
  have hT0 : 0 ≤ T := by linarith
  have hscale (p : ℝ) : 0 ≤ gabrielGaussianScale T b p := by
    dsimp [gabrielGaussianScale]
    positivity
  have hL := (hleft (by omega : 1 ≤ X) hT hXT (hscale (4/3))).2
  have hR := (hright hX hT0 (hscale 2)).2
  have eL : stripMomentDensity (mollifiedError X) (1/2) (4/3) =
      fun t : ℝ => ‖riemannZeta ((1/2 : ℂ) + I*t) *
        mollifier X ((1/2 : ℂ) + I*t) - 1‖ ^ (4/3 : ℝ) := by
    funext t
    simp only [stripMomentDensity, mollifiedError, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat, mul_comm _ I]
  have eR : stripMomentDensity (mollifiedError X) β 2 =
      fun t : ℝ => ‖riemannZeta ((β : ℂ) + I*t) *
        mollifier X ((β : ℂ) + I*t) - 1‖ ^ 2 := by
    funext t
    simp only [stripMomentDensity, mollifiedError, Real.rpow_two, mul_comm _ I]
  have lBound : gabrielBoundaryBudget X T b (1/2) (4/3) ≤
      Real.exp ((4/3)*b*(1/2)^2) *
        (Cl*T*(1+Real.log T)^2*(1+gabrielGaussianScale T b (4/3))^3) := by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    rwa [eL]
  have rBound : gabrielBoundaryBudget X T b β 2 ≤ Real.exp (2*b*β^2) *
      (Cr*Real.log X*(1+(T*gabrielGaussianScale T b 2/X)*Real.Gamma (3/2))) := by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    rw [eR]
    exact hR
  have nl := boundaryBudget_nonneg (p := 4/3) (b := b) X hT0 (1/2)
  have nr := boundaryBudget_nonneg (p := 2) (b := b) X hT0 β
  have el := Real.rpow_le_rpow nl lBound (by norm_num : 0 ≤ (3/4 : ℝ))
  have er := Real.rpow_le_rpow nr rBound (by norm_num : 0 ≤ (1/2 : ℝ))
  apply (actual_gabriel_moving_window hδ hX hT hXT hH hHT hb hθ).trans
  exact mul_le_mul
    (Real.rpow_le_rpow (Real.rpow_nonneg nl _) el (sub_nonneg.mpr hθ.2))
    (Real.rpow_le_rpow (Real.rpow_nonneg nr _) er hθ.1)
    (Real.rpow_nonneg (Real.rpow_nonneg nr _) _)
    (Real.rpow_nonneg (Real.rpow_nonneg (nl.trans lBound) _) _)

end RiemannResearch.Analysis.InghamMollifier
