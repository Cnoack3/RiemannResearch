/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.DirichletTailMeanSquare
import Mathlib.Tactic

/-!
# Signed diagonal error for Dirichlet tails with general coefficients

The finite signed identity is `tailPartial_mean_square_identity`. Passing its
Montgomery--Vaughan remainder bound to an absolutely convergent tail gives
an explicit two-sided error, and the tail support permits a single weighted
coefficient sum for both terms. The application is the sharp right edge
in Chourasiya--Simonič, arXiv:2507.15184, Lemma 6.
-/
noncomputable section
open MeasureTheory Complex Filter Set
open scoped BigOperators
namespace RiemannResearch.Analysis.DirichletMeanSquare

/-- Squared coefficient at a real Dirichlet exponent. -/
def coefficientSquareWeight (a : ℕ → ℂ) (p : ℝ) (n : ℕ) : ℝ :=
  ‖a n‖ ^ 2 * (n : ℝ) ^ (-p)

theorem coefficientSquareWeight_nonneg (a : ℕ → ℂ) (p : ℝ) (n : ℕ) :
    0 ≤ coefficientSquareWeight a p n := by unfold coefficientSquareWeight; positivity

private theorem tailCoefficient_sq (a : ℕ → ℂ) (σ : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖tailCoefficient a σ n‖ ^ 2 = coefficientSquareWeight a (2 * σ) n := by
  rw [tailCoefficient_norm a σ hn, mul_pow, coefficientSquareWeight]
  have hpow : ((n : ℝ) ^ (-σ)) ^ 2 = (n : ℝ) ^ (-(2 * σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    norm_num
    ring
  rw [hpow]

theorem mul_coefficientSquareWeight (a : ℕ → ℂ) (p : ℝ) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * coefficientSquareWeight a p n = coefficientSquareWeight a (p - 1) n := by
  have h : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold coefficientSquareWeight
  calc
    _ = ‖a n‖ ^ 2 * ((n : ℝ) ^ 1 * (n : ℝ) ^ (-p)) := by ring
    _ = ‖a n‖ ^ 2 * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-p)) := by simp
    _ = _ := by rw [← Real.rpow_add h]; congr 2; ring

/-- The finite mean square with its diagonal removed retains both signs of the error. -/
theorem abs_tailPartial_mean_square_sub_diagonal_le (a : ℕ → ℂ) (σ : ℝ)
    (X N : ℕ) (H T : ℝ) :
    |(∫ t in H..T, ‖tailPartial a σ X N t‖ ^ 2) -
      (T-H) * ∑ k ∈ Finset.range N, coefficientSquareWeight a (2*σ) (k+X+1)| ≤
      52 * ∑ k ∈ Finset.range N, coefficientSquareWeight a (2*σ-1) (k+X+1) := by
  let n : Fin N → ℕ := fun i => i.val + X + 1
  let c : Fin N → ℂ := fun i => tailCoefficient a σ (n i)
  let ω : Fin N → ℝ := fun i => -Real.log (n i)
  have hnpos (i : Fin N) : 1 ≤ n i := by dsimp [n]; omega
  have hinj : Function.Injective n := by intro i j hij; dsimp [n] at hij; ext; omega
  have hω : Function.Injective ω := by
    intro i j hij
    apply hinj
    have hlog : Real.log (n i : ℝ) = Real.log (n j : ℝ) := neg_injective hij
    exact_mod_cast Real.log_injOn_pos
      (show (n i : ℝ) ∈ Ioi 0 from by
        change 0 < (n i : ℝ)
        exact_mod_cast hnpos i)
      (show (n j : ℝ) ∈ Ioi 0 from by
        change 0 < (n j : ℝ)
        exact_mod_cast hnpos j) hlog
  have hsep (i j : Fin N) (hij : i ≠ j) :
      1 / (2 * (n i : ℝ)) ≤ |ω i - ω j| := by
    simpa only [ω, neg_sub_neg, abs_sub_comm] using
      Zeta23.PrimeSide.inv_two_mul_le_abs_log_sub (hnpos i) (hnpos j)
        (fun he => hij (hinj he))
  have hmv := abs_integral_norm_sq_sub_le c ω (fun i => 1 / (2 * (n i : ℝ)))
    hω (fun i => by
      have hi : 0 < (n i : ℝ) := by exact_mod_cast hnpos i
      positivity)
    hsep H T
  have heq : polynomial c ω = tailPartial a σ X N := rfl
  rw [heq] at hmv
  have hc (i : Fin N) : ‖c i‖ ^ 2 = coefficientSquareWeight a (2*σ) (n i) :=
    tailCoefficient_sq a σ (hnpos i)
  have hw (i : Fin N) : ‖c i‖ ^ 2 / (1 / (2 * (n i : ℝ))) =
      2 * coefficientSquareWeight a (2*σ-1) (n i) := by
    rw [div_div_eq_mul_div, div_one, hc, ← mul_coefficientSquareWeight a (2*σ) (hnpos i)]
    ring
  simp only [hw, ← Finset.mul_sum] at hmv
  simp only [hc] at hmv
  rw [Fin.sum_univ_eq_sum_range (fun k => coefficientSquareWeight a (2*σ) (k+X+1)),
      Fin.sum_univ_eq_sum_range (fun k => coefficientSquareWeight a (2*σ-1) (k+X+1))] at hmv
  linarith

private theorem tendsto_tailPartial_integral_general {a : ℕ → ℂ} {σ : ℝ} {X : ℕ}
    (habs : Summable (fun k : ℕ => ‖a (k+X+1)‖ * ((k+X+1 : ℕ) : ℝ) ^ (-σ)))
    {H T : ℝ} (hHT : H ≤ T) :
    Tendsto (fun N : ℕ => ∫ t in H..T, ‖tailPartial a σ X N t‖ ^ 2) atTop
      (nhds (∫ t in H..T, ‖dirichletTail a σ X t‖ ^ 2)) := by
  let b := fun k : ℕ => ‖a (k+X+1)‖ * ((k+X+1 : ℕ) : ℝ) ^ (-σ)
  have hb (k : ℕ) : 0 ≤ b k := by dsimp [b]; positivity
  have ht (k : ℕ) (t : ℝ) : ‖tailTerm a σ (k+X+1) t‖ = b k :=
    tailTerm_norm a σ (by omega) t
  have hbp (N : ℕ) (t : ℝ) : ‖tailPartial a σ X N t‖ ≤ ∑' k, b k := by
    rw [tailPartial_eq_sum_range]
    calc
      _ ≤ ∑ k ∈ Finset.range N, ‖tailTerm a σ (k+X+1) t‖ := norm_sum_le _ _
      _ = ∑ k ∈ Finset.range N, b k := by simp only [ht]
      _ ≤ _ := habs.sum_le_tsum _ (fun k _ => hb k)
  have hconv (t : ℝ) : Tendsto (fun N => tailPartial a σ X N t) atTop
      (nhds (dirichletTail a σ X t)) := by
    have hh : Summable (fun k : ℕ => tailTerm a σ (k+X+1) t) :=
      habs.of_norm_bounded (fun k => (ht k t).le)
    simpa only [tailPartial_eq_sum_range, dirichletTail] using hh.hasSum.tendsto_sum_nat
  simp only [intervalIntegral.integral_of_le hHT]
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioc H T)) (fun _ : ℝ => (∑' k, b k)^2)
  · exact fun N => ((continuous_tailPartial a σ X N).norm.pow 2).aestronglyMeasurable
  · exact integrable_const _
  · exact fun N => Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbp N t) 2)
  · exact Filter.Eventually.of_forall (fun t => (hconv t).norm.pow 2)

/-- Two-sided infinite mean-value theorem for general absolutely convergent
coefficients, with weighted square sum as the full error allowance. -/
theorem abs_dirichletTail_mean_square_sub_diagonal_le {a : ℕ → ℂ} {σ : ℝ} {X : ℕ}
    (habs : Summable (fun k : ℕ => ‖a (k+X+1)‖ * ((k+X+1 : ℕ) : ℝ) ^ (-σ)))
    (hd : Summable (fun k : ℕ => coefficientSquareWeight a (2*σ) (k+X+1)))
    (hw : Summable (fun k : ℕ => coefficientSquareWeight a (2*σ-1) (k+X+1)))
    {H T : ℝ} (hHT : H ≤ T) :
    |(∫ t in H..T, ‖dirichletTail a σ X t‖ ^ 2) -
      (T-H) * ∑' k : ℕ, coefficientSquareWeight a (2*σ) (k+X+1)| ≤
      52 * ∑' k : ℕ, coefficientSquareWeight a (2*σ-1) (k+X+1) := by
  exact le_of_tendsto_of_tendsto'
    (((tendsto_tailPartial_integral_general habs hHT).sub
      (hd.hasSum.tendsto_sum_nat.const_mul (T-H))).abs)
    (hw.hasSum.tendsto_sum_nat.const_mul 52)
    (fun N => abs_tailPartial_mean_square_sub_diagonal_le a σ X N H T)

/-- Tail support absorbs the diagonal into the same weighted coefficient sum. -/
theorem dirichletTail_mean_square_le_one_energy {a : ℕ → ℂ} {σ : ℝ} {X : ℕ}
    (hX : 1 ≤ X)
    (habs : Summable (fun k : ℕ => ‖a (k+X+1)‖ * ((k+X+1 : ℕ) : ℝ) ^ (-σ)))
    (hd : Summable (fun k : ℕ => coefficientSquareWeight a (2*σ) (k+X+1)))
    (hw : Summable (fun k : ℕ => coefficientSquareWeight a (2*σ-1) (k+X+1)))
    {H T : ℝ} (hHT : H ≤ T) :
    (∫ t in H..T, ‖dirichletTail a σ X t‖ ^ 2) ≤
      ((T-H) / X + 52) * ∑' k : ℕ, coefficientSquareWeight a (2*σ-1) (k+X+1) := by
  let D := ∑' k : ℕ, coefficientSquareWeight a (2*σ) (k+X+1)
  let W := ∑' k : ℕ, coefficientSquareWeight a (2*σ-1) (k+X+1)
  have hx : 0 < (X : ℝ) := by exact_mod_cast hX
  have hxd : (X : ℝ) * D ≤ W := by
    dsimp only [D,W]
    rw [← tsum_mul_left]
    apply (hd.mul_left (X : ℝ)).tsum_le_tsum _ hw
    intro k
    rw [← mul_coefficientSquareWeight a (2*σ) (by omega : 0 < k+X+1)]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show X ≤ k+X+1 by omega))
      (coefficientSquareWeight_nonneg a _ _)
  have hdu : D ≤ W / X := (le_div_iff₀ hx).mpr (by linarith)
  have h := (abs_le.mp (abs_dirichletTail_mean_square_sub_diagonal_le habs hd hw hHT)).2
  change _ - (T-H)*D ≤ 52*W at h
  change _ ≤ ((T-H) / X + 52) * W
  calc
    _ ≤ (T-H) * D + 52 * W := by linarith
    _ ≤ (T-H) * (W / X) + 52 * W := by gcongr
    _ = _ := by ring

end RiemannResearch.Analysis.DirichletMeanSquare
