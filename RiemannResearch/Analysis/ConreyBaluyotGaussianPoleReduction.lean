/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualConreyBaluyotDensity
import RiemannResearch.Analysis.ConreyBaluyotGaussianEstermann
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Removing the pole term on the actual near-line Gaussian windows

The exact Estermann formula retains a signed pole correction. On Baluyot's
padded window this term decays faster than any fixed power of the height,
uniformly in the evaluation line, the center and the mollifier cutoff
parameter. Thus the remaining Gaussian upper bound concerns only the
real part of the signed sum of both Estermann rays.

Source for the Gaussian and mollifier parameters: S. A. C. Baluyot,
*On the Zeros of Riemann's Zeta-function* (2017), Chapter 3,
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .
-/

noncomputable section
open Filter Asymptotics Set

namespace RiemannResearch.Analysis.ConreyBaluyot

/-- Uniform power saving for the full normalized pole term, including its
`2√π/Δ` coefficient, throughout the actual padded source window. -/
theorem exists_padded_gaussian_pole_power_bound {θ δ : ℝ}
    (hθ : 0 < θ) (hδ : 0 < δ) (hδhi : δ ≤ 1) :
    ∃ η K : ℝ, 0 < η ∧ η < 1 / 4 ∧ 0 ≤ K ∧
      ∀ A : ℝ, 0 ≤ A → ∃ H : ℝ, 1 < H ∧ ∀ T : ℝ, H ≤ T →
        ∀ σ : ℝ, 1 / 2 + 1 / Real.log (T ^ θ) ≤ σ → σ ≤ 1 / 2 + η →
        ∀ ε u : ℝ, T - T ^ (1 - δ) * Real.log T ≤ u →
          ‖((2 * Real.sqrt Real.pi / T ^ (1 - δ) : ℝ) : ℂ) *
            mollifiedGaussianPoleCoeff σ (T ^ θ) ε σ (T ^ (1 - δ)) u‖ ≤
            K * T ^ (-A) := by
  obtain ⟨η, Y, C, hη, hηhi, hY, hC, hbound⟩ :=
    exists_uniform_mollifiedGaussianPoleCoeff_bound
  refine ⟨η, 2 * Real.sqrt Real.pi * C, hη, hηhi, by positivity, ?_⟩
  intro A hA
  have hsmall : ∀ᶠ T : ℝ in atTop, ‖Real.log T‖ ≤ (1/2 : ℝ) * ‖T ^ δ‖ :=
    (isLittleO_log_rpow_atTop hδ).bound (by norm_num)
  have hevent : ∀ᶠ T : ℝ in atTop,
      1 < T ∧ Y ≤ T ^ θ ∧ 2 * (2*θ+A) ≤ Real.log T ∧
      2 * Real.log T ≤ T ^ δ := by
    filter_upwards [eventually_gt_atTop (1:ℝ), (tendsto_rpow_atTop hθ).eventually_ge_atTop Y,
      Real.tendsto_log_atTop.eventually_ge_atTop (2*(2*θ+A)), hsmall] with T hT hTy hlog hs
    have ht : 0 ≤ T := by linarith
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hT.le),
      abs_of_nonneg (Real.rpow_nonneg ht δ)] at hs
    exact ⟨hT, hTy, hlog, by linarith⟩
  obtain ⟨H, hH⟩ := eventually_atTop.1 hevent
  refine ⟨max H 2, by linarith [le_max_right H (2:ℝ)], ?_⟩
  intro T hT σ hσ hση ε u hu
  obtain ⟨hT1, hy, hlog, hlogpow⟩ := hH T ((le_max_left _ _).trans hT)
  have hT0 : 0 < T := by linarith
  let Δ := T ^ (1 - δ)
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos hT0 _
  have hΔ1 : 1 ≤ Δ := Real.one_le_rpow hT1.le (by linarith)
  have hprod : Δ * T ^ δ = T := by
    dsimp [Δ]
    rw [← Real.rpow_add hT0, sub_add_cancel, Real.rpow_one]
  have hratio : Real.log T ≤ u / Δ := by
    apply (le_div_iff₀ hΔ).2
    change T - Δ * Real.log T ≤ u at hu
    have hx := mul_le_mul_of_nonneg_left hlogpow hΔ.le
    rw [hprod] at hx
    linarith
  have hlog0 := Real.log_nonneg hT1.le
  have hexp : Real.exp (-(u / Δ)^2) ≤ T ^ (-(2*θ+A)) := by
    refine (Real.exp_le_exp.mpr ?_).trans
      (Real.exp_neg_log_sq_le_rpow hT0 (by positivity) hlog)
    nlinarith only [pow_le_pow_left₀ hlog0 hratio 2, sq_nonneg (Real.log T)]
  have hysq : (T ^ θ)^2 = T ^ (2*θ) := by
    rw [pow_two, ← Real.rpow_add hT0, two_mul]
  have hpole : ‖mollifiedGaussianPoleCoeff σ (T ^ θ) ε σ Δ u‖ ≤ C * T ^ (-A) := by
    calc
      _ ≤ C * (T ^ θ)^2 * Real.exp (-(u / Δ)^2) :=
        hbound _ hy σ hσ hση ε Δ hΔ1 u
      _ ≤ C * (T ^ θ)^2 * T ^ (-(2*θ+A)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = C * (T ^ (2*θ) * T ^ (-(2*θ+A))) := by rw [hysq]; ring
      _ = _ := by rw [← Real.rpow_add hT0, show 2*θ + -(2*θ+A) = -A by ring]
  have hcoef : 2 * Real.sqrt Real.pi / Δ ≤ 2 * Real.sqrt Real.pi :=
    (div_le_iff₀ hΔ).2 (le_mul_of_one_le_right (by positivity) hΔ1)
  change ‖((2 * Real.sqrt Real.pi / Δ : ℝ) : ℂ) *
    mollifiedGaussianPoleCoeff σ (T ^ θ) ε σ Δ u‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (2 * Real.sqrt Real.pi) * (C * T ^ (-A)) :=
      mul_le_mul hcoef hpole (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- On every fixed positive ray angle, a bound on the real part of the
finite sum of paired Estermann rays is equivalent to the actual Gaussian
moment bound. Both signed rays and all finite arithmetic coefficients enter
the Estermann value. -/
theorem uniformGaussianMollifiedMoment_iff_estermann_real {θ ε δ φ : ℝ}
    (hθ : 0 < θ) (hδ : 0 < δ) (hδhi : δ ≤ 1) (hφ : φ ∈ Ioo 0 Real.pi) :
    UniformGaussianMollifiedMoment θ ε δ ↔
      ∃ η C H : ℝ, 0 < η ∧ 0 ≤ C ∧ 1 < H ∧
        ∀ T : ℝ, H ≤ T → ∀ σ : ℝ,
          1 / 2 + 1 / Real.log (T ^ θ) ≤ σ → σ ≤ 1 / 2 + η →
          ∀ u ∈ Icc (T - T ^ (1 - δ) * Real.log T) (2*T + T ^ (1 - δ) * Real.log T),
            (mollifiedGaussianEstermannValue σ (T ^ θ) ε σ (T ^ (1 - δ)) u φ).re ≤
              1 + C * T ^ (-(2*θ) * (σ - 1/2)) := by
  let m := fun T σ u : ℝ => mollifiedGaussianMoment σ (T ^ θ) ε σ (T ^ (1-δ)) u
  let e := fun T σ u : ℝ =>
    (mollifiedGaussianEstermannValue σ (T ^ θ) ε σ (T ^ (1-δ)) u φ).re
  let P := fun f : ℝ → ℝ → ℝ → ℝ => ∃ η C H : ℝ, 0 < η ∧ 0 ≤ C ∧ 1 < H ∧
    ∀ T : ℝ, H ≤ T → ∀ σ : ℝ, 1/2 + 1 / Real.log (T^θ) ≤ σ → σ ≤ 1/2 + η →
    ∀ u ∈ Icc (T - T^(1-δ)*Real.log T) (2*T + T^(1-δ)*Real.log T),
      f T σ u ≤ 1 + C * T ^ (-(2*θ)*(σ-1/2))
  change P m ↔ P e
  obtain ⟨η₀, K, hη₀, hη₀hi, hK, hbound⟩ :=
    exists_padded_gaussian_pole_power_bound hθ hδ hδhi
  obtain ⟨H₀, hH₀, hpow⟩ := hbound (2*θ) (by positivity)
  have transfer {f g : ℝ → ℝ → ℝ → ℝ}
      (heq : ∀ T σ u, |f T σ u - g T σ u| = |m T σ u - e T σ u|) : P f → P g := by
    rintro ⟨η, C, H, hη, hC, hH, hf⟩
    refine ⟨min η η₀, C+K, max H H₀, lt_min hη hη₀, add_nonneg hC hK,
      hH.trans_le (le_max_left _ _), ?_⟩
    intro T hT σ hσ hση u hu
    have hTH : H ≤ T := (le_max_left _ _).trans hT
    have hTH₀ : H₀ ≤ T := (le_max_right _ _).trans hT
    have hT1 : 1 < T := hH.trans_le hTH
    have hT0 : 0 < T := by linarith
    have hση' : σ ≤ 1/2 + η₀ := hση.trans (by linarith [min_le_right η η₀])
    have hy : 0 < T ^ θ := Real.rpow_pos_of_pos hT0 _
    have hσpos : 0 < σ := by
      have := one_div_pos.mpr (Real.log_pos (Real.one_lt_rpow hT1 hθ))
      linarith
    have hσ1 : σ < 1 := by linarith
    have hΔ : 0 < T^(1-δ) := Real.rpow_pos_of_pos hT0 _
    have hid := congrArg Complex.re
      (mollifiedGaussianMoment_eq_estermann σ ε u hy hσpos hσ1 hΔ hφ)
    simp only [Complex.ofReal_re, Complex.sub_re] at hid
    have hd : m T σ u - e T σ u = -(((2 * Real.sqrt Real.pi / T^(1-δ) : ℝ) : ℂ) *
        mollifiedGaussianPoleCoeff σ (T^θ) ε σ (T^(1-δ)) u).re := by
      dsimp only [m, e]
      linarith only [hid]
    have hgap : |f T σ u - g T σ u| ≤ K * T ^ (-(2*θ)) := by
      rw [heq, hd, abs_neg]
      exact (Complex.abs_re_le_norm _).trans (hpow T hTH₀ σ hσ hση' ε u hu.1)
    have horder : -(2*θ) ≤ -(2*θ) * (σ-1/2) := by
      nlinarith only [mul_le_mul_of_nonneg_left (show σ-1/2 ≤ 1 by linarith)
        (show 0 ≤ 2*θ by positivity)]
    have hp := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT1.le horder) hK
    have hf' := hf T hTH σ hσ (hση.trans (by linarith [min_le_left η η₀])) u hu
    linarith only [hf', neg_le_abs (f T σ u - g T σ u), hgap, hp]
  exact ⟨transfer (by intros; rfl), transfer (fun T σ u => abs_sub_comm _ _)⟩

end RiemannResearch.Analysis.ConreyBaluyot
