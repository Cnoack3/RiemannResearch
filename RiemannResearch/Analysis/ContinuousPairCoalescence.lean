/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ZeroOrdinateEquidistribution
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Continuous pair tests under vanishing mean displacement

Source: standard uniform-continuity argument on compact metric spaces.
This is an abstract probability-average theorem with explicit convergence
hypotheses. It supplies no zeta equidistribution or gap estimate.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ContinuousPairCoalescence
open ZeroOrdinate

private theorem realMean_const (n : ℕ) (c : ℝ) :
    realMean n (fun _ => c) = c := by
  have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [realMean, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact inv_mul_cancel_left₀ hn c

private theorem realMean_add (n : ℕ) (f g : ℕ → ℝ) :
    realMean n (fun j => f j + g j) = realMean n f + realMean n g := by
  simp only [realMean, Finset.sum_add_distrib, mul_add]

/-- On a compact metric space, any continuous pair test is insensitive in
Cesàro mean to a displacement whose mean distance vanishes. The second
sample may depend on both the averaging cutoff and the sample index. -/
theorem continuous_pair_difference_tendsto_zero
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (x : ℕ → X) (y : ℕ → ℕ → X) (F : C(X × X, ℂ))
    (hdisplacement : Tendsto
      (fun n => realMean n (fun j => dist (y n j) (x j)))
      atTop (𝓝 0)) :
    Tendsto (fun n =>
      mean n (fun j => F (x j, y n j)) -
        mean n (fun j => F (x j, x j))) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ, hδ, hFδ⟩ :=
    Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous F.continuous)
      (ε/2) (by positivity)
  let C : ℝ := (2 * ‖F‖) / δ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hscaled : Tendsto
      (fun n => C * realMean n (fun j => dist (y n j) (x j)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hdisplacement.const_mul C
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hscaled (ε/2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hpoint (j : ℕ) :
      ‖F (x j, y n j) - F (x j, x j)‖ ≤
        ε/2 + C * dist (y n j) (x j) := by
    by_cases hsmall : dist (y n j) (x j) < δ
    · have hp : dist (x j, y n j) (x j, x j) < δ := by
        change max (dist (x j) (x j)) (dist (y n j) (x j)) < δ
        simpa only [dist_self, max_eq_right (dist_nonneg)] using hsmall
      have hh := hFδ hp
      rw [dist_eq_norm] at hh
      linarith [mul_nonneg hC (dist_nonneg (x := y n j) (y := x j))]
    · have hnorm : ‖F (x j, y n j) - F (x j, x j)‖ ≤ 2 * ‖F‖ := by
        calc
          _ ≤ ‖F (x j, y n j)‖ + ‖F (x j, x j)‖ := norm_sub_le _ _
          _ ≤ ‖F‖ + ‖F‖ :=
            add_le_add (F.norm_coe_le_norm _) (F.norm_coe_le_norm _)
          _ = _ := by ring
      have hd : δ ≤ dist (y n j) (x j) := le_of_not_gt hsmall
      have hm := mul_le_mul_of_nonneg_left hd hC
      have hCδ : C * δ = 2 * ‖F‖ := by
        dsimp [C]
        exact div_mul_cancel₀ _ hδ.ne'
      rw [hCδ] at hm
      linarith
  have havg :
      ‖mean n (fun j => F (x j, y n j)) -
        mean n (fun j => F (x j, x j))‖ ≤
        ε/2 + C * realMean n (fun j => dist (y n j) (x j)) := by
    rw [← mean_sub]
    calc
      _ ≤ realMean n (fun j => ‖F (x j, y n j) - F (x j, x j)‖) :=
        norm_mean_le_realMean _ _
      _ ≤ realMean n (fun j => ε/2 + C * dist (y n j) (x j)) :=
        realMean_mono _ _ _ hpoint
      _ = _ := by
        rw [realMean_add, realMean_const, realMean_mul_left]
  have hnear := hN n hn
  rw [Real.dist_eq, sub_zero] at hnear
  have hmean_nonneg :
      0 ≤ C * realMean n (fun j => dist (y n j) (x j)) :=
    mul_nonneg hC (realMean_nonneg _ _ (fun _ => dist_nonneg))
  rw [abs_of_nonneg hmean_nonneg] at hnear
  rw [dist_eq_norm, sub_zero]
  linarith

/-- A diagonal empirical limit transfers to all continuous displaced pair
tests. In an ordinate application the limit functional is diagonal Haar. -/
theorem continuous_pair_tendsto_of_diagonal
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (x : ℕ → X) (y : ℕ → ℕ → X) (F : C(X × X, ℂ)) (L : ℂ)
    (hdisplacement : Tendsto
      (fun n => realMean n (fun j => dist (y n j) (x j)))
      atTop (𝓝 0))
    (hdiag : Tendsto (fun n => mean n (fun j => F (x j, x j)))
      atTop (𝓝 L)) :
    Tendsto (fun n => mean n (fun j => F (x j, y n j)))
      atTop (𝓝 L) := by
  simpa only [sub_add_cancel, zero_add] using
    (continuous_pair_difference_tendsto_zero x y F hdisplacement).add hdiag

end RiemannResearch.Analysis.ContinuousPairCoalescence
