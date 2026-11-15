/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotGoodHorizontalArgument

/-!
# Dyadic horizontal argument bounds for one fixed mollifier

For every nominal height in [T,2T], a zero-free height can be chosen
arbitrarily close while keeping the same actual mollifier of length T^theta.
The normalized horizontal argument integral is uniformly O(log T) on those
good heights. The Littlewood contour identity and boundary limits remain
separate obligations.
-/

noncomputable section
open Complex Set
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- Uniform O(log T) horizontal argument integrals at good heights near
every U in [T,2T], with the one mollifier of length T^theta held fixed.
In particular, the same result applies at both ends of the dyadic window. -/
theorem exists_uniform_mollifiedZeta_dyadic_good_horizontal_argument
    {ε θ : ℝ} (hε : 0 ≤ ε) (hθ : 0 < θ) :
    ∃ η b D H : ℝ, 0 < η ∧ η < 1 / 4 ∧ 2 ≤ b ∧ 0 < D ∧ b + 2 ≤ H ∧
      ∀ T : ℝ, H ≤ T → ∀ σ : ℝ,
        1 / 2 + 1 / Real.log (T ^ θ) ≤ σ → σ ≤ 1 / 2 + η →
          ∀ U ∈ Set.Icc T (2 * T), ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
            ∃ t : ℝ, |t - U| < δ ∧
              (∀ x ∈ Set.Icc (1 / 2 : ℝ) b,
                mollifiedZeta σ (T ^ θ) ε ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
              ∃ φ : ℝ → ℝ, ContinuousOn φ (Set.Icc (1 / 2 : ℝ) b) ∧
                φ b = (mollifiedZeta σ (T ^ θ) ε ((b : ℂ) + (t : ℂ) * I)).arg ∧
                (∀ x ∈ Set.Icc (1 / 2 : ℝ) b,
                  mollifiedZeta σ (T ^ θ) ε ((x : ℂ) + (t : ℂ) * I) =
                    (‖mollifiedZeta σ (T ^ θ) ε ((x : ℂ) + (t : ℂ) * I)‖ : ℂ) *
                      Complex.exp ((φ x : ℂ) * I)) ∧
                (∀ α ∈ Set.Icc (1 / 2 : ℝ) b,
                  ‖∫ x in α..b, φ x‖ ≤ D * Real.log T) := by
  obtain ⟨η, Y, b, C, H, hη, hη', hY, hb, hC, hH, hgood⟩ :=
    exists_uniform_mollifiedZeta_good_horizontal_argument hε
  let d := Real.log ((b - 1 / 4) / (b - 1 / 2))
  let K := 2 * (1 + C * (b + 2))
  let Q := (Real.log K + 1 + θ) / d + 3
  let D := 2 * Q * Real.pi * (b - 1 / 2)
  let H' := max H (Y ^ θ⁻¹)
  have hr : 0 < b - 1 / 2 := by linarith
  have hratio : 1 < (b - 1 / 4) / (b - 1 / 2) :=
    (one_lt_div hr).mpr (by linarith)
  have hd : 0 < d := Real.log_pos hratio
  have hK1 : 1 ≤ K := by
    dsimp [K]
    nlinarith [mul_nonneg hC.le (show 0 ≤ b + 2 by linarith)]
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨η, b, D, H', hη, hη', hb, hD,
    by dsimp [H']; exact hH.trans (le_max_left _ _), ?_⟩
  intro T hT σ hσ hση U hU δ hδ hδ'
  have hTH : H ≤ T := (le_max_left _ _).trans hT
  have hTY : Y ^ θ⁻¹ ≤ T := (le_max_right _ _).trans hT
  have hT3 : 3 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hU3 : 3 ≤ U := by linarith [hU.1]
  have hU0 : 0 < U := by linarith
  have hUH : H ≤ U := hTH.trans hU.1
  have hYpow : Y ≤ T ^ θ := by
    calc
      Y = (Y ^ θ⁻¹) ^ θ :=
        (Real.rpow_inv_rpow (by linarith : 0 ≤ Y) (ne_of_gt hθ)).symm
      _ ≤ T ^ θ := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hTY hθ.le
  obtain ⟨t, ht, hfree, φ, hφ, hφb, hrep, hint⟩ :=
    hgood (T ^ θ) hYpow σ hσ hση U hUH δ hδ hδ'
  have ht14 : |t - U| ≤ 1 / 4 := ht.le.trans hδ'
  have ht0 : 0 < t := by have hh := (abs_lt.mp ht).1; linarith [hU.1]
  have hR0 : 0 < b - 1 / 4 := by linarith
  have hpow : T ^ θ ≤ U ^ θ := Real.rpow_le_rpow hT0.le hU.1 hθ.le
  have hNle :
      2 * (1 + C * (t + (b - 1 / 4)) * T ^ θ) ≤
        2 * (1 + C * (t + (b - 1 / 4)) * U ^ θ) := by
    have hh := mul_le_mul_of_nonneg_left hpow
      (show 0 ≤ C * (t + (b - 1 / 4)) by positivity)
    nlinarith
  have hN0 : 0 < 2 * (1 + C * (t + (b - 1 / 4)) * T ^ θ) := by positivity
  have hlogN := Real.log_le_log hN0 hNle
  have hJcomp :
      Real.log (2 * (1 + C * (t + (b - 1 / 4)) * T ^ θ)) / d + 3 ≤
        Real.log (2 * (1 + C * (t + (b - 1 / 4)) * U ^ θ)) / d + 3 := by
    have hh := div_le_div_of_nonneg_right hlogN hd.le
    linarith
  have hJU :
      Real.log (2 * (1 + C * (t + (b - 1 / 4)) * U ^ θ)) / d + 3 ≤
        Q * Real.log U := by
    simpa only [d, Q, K] using
      jensen_count_power_log_bound b C θ U t hb hC hθ.le hU3 ht14
  have hlogU : Real.log U ≤ 2 * Real.log T := by
    calc
      Real.log U ≤ Real.log (2 * T) := Real.log_le_log hU0 hU.2
      _ = Real.log 2 + Real.log T := by rw [Real.log_mul (by norm_num) (ne_of_gt hT0)]
      _ ≤ 2 * Real.log T := by
        have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ T by linarith)
        linarith
  have hJ :
      Real.log (2 * (1 + C * (t + (b - 1 / 4)) * T ^ θ)) / d + 3 ≤
        (2 * Q) * Real.log T := by
    have hh := mul_le_mul_of_nonneg_left hlogU hQ.le
    nlinarith [hJcomp, hJU]
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hcoef : 0 ≤ (2 * Q) * Real.log T * Real.pi := by positivity
  refine ⟨t, ht, hfree, φ, hφ, hφb, hrep, ?_⟩
  intro α hα
  have hlen : |b - α| ≤ b - 1 / 2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hα.2)]
    linarith [hα.1]
  calc
    ‖∫ x in α..b, φ x‖ ≤
        ((Real.log (2 * (1 + C * (t + (b - 1 / 4)) * T ^ θ)) / d + 3) *
          Real.pi) * |b - α| := hint α hα
    _ ≤ ((2 * Q) * Real.log T * Real.pi) * |b - α| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hJ Real.pi_pos.le) (abs_nonneg _)
    _ ≤ ((2 * Q) * Real.log T * Real.pi) * (b - 1 / 2) :=
      mul_le_mul_of_nonneg_left hlen hcoef
    _ = D * Real.log T := by dsimp [D]; ring

end RiemannResearch.Analysis.ConreyBaluyot
