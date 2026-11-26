/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualInghamGabrielMovingWindow
import RiemannResearch.Analysis.ActualInghamSharpLength

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

/-- Gaussian averaging preserves the additive length term in the moving-line moment. -/
theorem exists_actual_gabriel_right_endpoint_add_log {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : ℕ}, 2 ≤ X → ∀ {T a : ℝ}, 0 ≤ T → 0 ≤ a →
      let β := 1 + δ / Real.log (X : ℝ)
      let f := fun t : ℝ => ‖riemannZeta ((β : ℂ) + I*t) *
        mollifier X ((β : ℂ) + I*t) - 1‖ ^ 2
      IntegrableOn (fun u : ℝ => Real.exp (-u) * ∫ t in 0..T*a*Real.sqrt u, f t) (Ioi 0) ∧
      gabrielEndpoint f T a ≤ C * (Real.log X + (T*a/X) * Real.Gamma (3/2)) := by
  obtain ⟨C, hC, h⟩ := exists_actual_moving_right_error_moment_add_log hδ
  refine ⟨C, hC, ?_⟩
  intro X hX T a hT ha
  dsimp only
  have hx : (1 : ℝ) < X := by exact_mod_cast hX
  have hβ : 1 < 1 + δ / Real.log (X : ℝ) := by linarith [div_pos hδ (Real.log_pos hx)]
  have hc := (vertical_error_continuous X hβ.ne').pow 2
  simp only [mollifiedError, mul_comm _ I] at hc
  let K := C * Real.log X
  have hm := gabrielEndpoint_of_affine hc (fun t => sq_nonneg _) hT ha
    (A := K) (B := C / X) (fun U hU => by
      have hu := h hX (H := 0) (T := U) hU
      rw [sub_zero] at hu
      refine hu.trans_eq ?_
      dsimp [K]
      ring)
  refine ⟨hm.1, hm.2.trans_eq ?_⟩
  dsimp [K]
  ring

private theorem gabriel_sharp_window_of_right_bound {δ : ℝ} (hδ : 0 < δ)
    (G : ℝ → ℕ → ℝ → ℝ → ℝ)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ {X : ℕ}, 2 ≤ X → ∀ {T a : ℝ}, 0 ≤ T → 0 ≤ a →
      let β := 1 + δ / Real.log (X : ℝ)
      gabrielEndpoint (fun t : ℝ => ‖riemannZeta ((β : ℂ) + I*t) *
        mollifier X ((β : ℂ) + I*t) - 1‖ ^ 2) T a ≤ G C X T a) :
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
        G Cᵣ X T aᵣ
      Real.exp (b*(σ^2-T^2)) * (1-1/H) *
        (∫ t in H..T, stripMomentDensity (mollifiedError X) σ p t)^((3-θ)/4) ≤
        (L^(3/4 : ℝ))^(1-θ) * (R^(1/2 : ℝ))^θ := by
  obtain ⟨Cl, hl, hleft⟩ := exists_actual_gabriel_left_endpoint_bound
  obtain ⟨Cr, hr, hright⟩ := hbound
  refine ⟨Cl, Cr, hl, hr, ?_⟩
  intro X hX T H b θ hT hXT hH hHT hb hθ
  let β := 1 + δ / Real.log (X : ℝ)
  have hT0 : 0 ≤ T := by linarith
  have hscale (p : ℝ) : 0 ≤ gabrielGaussianScale T b p := by
    dsimp [gabrielGaussianScale]
    positivity
  have hL := (hleft (by omega : 1 ≤ X) hT hXT (hscale (4/3))).2
  have hR := hright hX hT0 (hscale 2)
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
      G Cr X T (gabrielGaussianScale T b 2) := by
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
  apply gabriel_sharp_window_of_right_bound hδ
    (fun C X T a => C * Real.log X * (1 + (T*a/X)*Real.Gamma (3/2)))
  obtain ⟨C, hC, hw⟩ := exists_actual_gabriel_right_endpoint_log_one hδ
  refine ⟨C, hC, ?_⟩
  intro X hX T a hT ha
  exact (hw hX hT ha).2

/-- The sharp strip bound with the right-end logarithm confined to the additive error. -/
theorem exists_actual_gabriel_sharp_window_add_log {δ : ℝ} (hδ : 0 < δ) :
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
        (Cᵣ * (Real.log X + (T*aᵣ/X)*Real.Gamma (3/2)))
      Real.exp (b*(σ^2-T^2)) * (1-1/H) *
        (∫ t in H..T, stripMomentDensity (mollifiedError X) σ p t)^((3-θ)/4) ≤
        (L^(3/4 : ℝ))^(1-θ) * (R^(1/2 : ℝ))^θ := by
  apply gabriel_sharp_window_of_right_bound hδ
    (fun C X T a => C * (Real.log X + (T*a/X)*Real.Gamma (3/2)))
  obtain ⟨C, hC, hw⟩ := exists_actual_gabriel_right_endpoint_add_log hδ
  refine ⟨C, hC, ?_⟩
  intro X hX T a hT ha
  exact (hw hX hT ha).2

end RiemannResearch.Analysis.InghamMollifier
