/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotGoodHorizontalArgument

/-!
# Dyadic horizontal argument bounds for one fixed mollifier

For every nominal height in [T-1/4,2T+1/4], a zero-free height can be chosen
arbitrarily close while keeping the same actual mollifier of length T^theta.
The normalized horizontal argument integral is uniformly O(log T) on those
good heights. The enlarged nominal window allows the dyadic rectangle
consumer to select strictly outward edges. The actual moment estimate
remains a separate obligation.
-/

noncomputable section
open Complex Set
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- Uniform O(log T) horizontal argument integrals at good heights near
every U in [T-1/4,2T+1/4], with the one mollifier of length T^theta held fixed.
In particular, the same result applies at both ends of the dyadic window. -/
theorem exists_uniform_mollifiedZeta_dyadic_good_horizontal_argument
    {ε θ : ℝ} (hε : 0 ≤ ε) (hθ : 0 < θ) :
    ∃ η b D H : ℝ, 0 < η ∧ η < 1 / 4 ∧ 2 ≤ b ∧ 0 < D ∧ b + 2 ≤ H ∧
      (∀ T : ℝ, H ≤ T → ∀ σ : ℝ,
        1 / 2 + 1 / Real.log (T ^ θ) ≤ σ → σ ≤ 1 / 2 + η →
          ∀ s : ℂ, b ≤ s.re → 1 / 2 ≤ (mollifiedZeta σ (T ^ θ) ε s).re) ∧
      ∀ T : ℝ, H ≤ T → ∀ σ : ℝ,
        1 / 2 + 1 / Real.log (T ^ θ) ≤ σ → σ ≤ 1 / 2 + η →
          ∀ U ∈ Set.Icc (T - 1 / 4) (2 * T + 1 / 4), ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
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
  obtain ⟨η, Y, b, C, H, hη, hη', hY, hb, hC, hH, hanchor, hgood⟩ :=
    exists_uniform_mollifiedZeta_good_horizontal_argument hε
  let d := Real.log ((b - 1 / 4) / (b - 1 / 2))
  let K := 2 * (1 + C * (b + 2))
  let Q := (Real.log K + 1 + θ) / d + 3
  let D := Q * Real.pi * (b - 1 / 2)
  let H' := max (H + 1) (Y ^ θ⁻¹)
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
    by dsimp [H']; linarith [le_max_left (H + 1) (Y ^ θ⁻¹)], ?_, ?_⟩
  · intro T hT σ hσ hση s hs
    have hTY : Y ^ θ⁻¹ ≤ T := (le_max_right _ _).trans hT
    have hYpow : Y ≤ T ^ θ := by
      calc
        Y = (Y ^ θ⁻¹) ^ θ :=
          (Real.rpow_inv_rpow (by linarith : 0 ≤ Y) (ne_of_gt hθ)).symm
        _ ≤ T ^ θ := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hTY hθ.le
    exact hanchor (T ^ θ) hYpow σ hσ hση s hs
  · intro T hT σ hσ hση U hU δ hδ hδ'
    have hTH : H + 1 ≤ T := (le_max_left _ _).trans hT
    have hTY : Y ^ θ⁻¹ ≤ T := (le_max_right _ _).trans hT
    have hT3 : 3 ≤ T := by linarith
    have hT0 : 0 < T := by linarith
    have hUH : H ≤ U := by linarith [hU.1]
    have hYpow : Y ≤ T ^ θ := by
      calc
        Y = (Y ^ θ⁻¹) ^ θ :=
          (Real.rpow_inv_rpow (by linarith : 0 ≤ Y) (ne_of_gt hθ)).symm
        _ ≤ T ^ θ := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hTY hθ.le
    obtain ⟨t, ht, hfree, φ, hφ, hφb, hrep, hint⟩ :=
      hgood (T ^ θ) hYpow σ hσ hση U hUH δ hδ hδ'
    have ht0 : 0 < t := by have hh := (abs_lt.mp ht).1; linarith [hU.1]
    have hJ :
        Real.log (2 * (1 + C * (t + (b - 1 / 4)) * T ^ θ)) / d + 3 ≤
          Q * Real.log T := by
      simpa only [d, Q, K] using
        jensen_count_power_log_bound b C θ T t hb hC hθ.le hT3 ht0
          (by have hh := (abs_lt.mp ht).2; linarith [hU.2])
    have hlog0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have hcoef : 0 ≤ Q * Real.log T * Real.pi := by positivity
    refine ⟨t, ht, hfree, φ, hφ, hφb, hrep, ?_⟩
    intro α hα
    have hlen : |b - α| ≤ b - 1 / 2 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hα.2)]
      linarith [hα.1]
    calc
      ‖∫ x in α..b, φ x‖ ≤
          ((Real.log (2 * (1 + C * (t + (b - 1 / 4)) * T ^ θ)) / d + 3) *
            Real.pi) * |b - α| := hint α hα
      _ ≤ (Q * Real.log T * Real.pi) * |b - α| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hJ Real.pi_pos.le) (abs_nonneg _)
      _ ≤ (Q * Real.log T * Real.pi) * (b - 1 / 2) :=
        mul_le_mul_of_nonneg_left hlen hcoef
      _ = D * Real.log T := by dsimp [D]; ring

end RiemannResearch.Analysis.ConreyBaluyot
