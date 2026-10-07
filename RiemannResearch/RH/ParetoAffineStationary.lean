/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoAffineHeadTrials
import Mathlib.Tactic.Ring

/-!
# Complete affine stationary minimum certificates

Source: user-provided CRT and Four Improvements continuation, 6–7 October 2026.
The extensions retain complete signed identities and correction squares.


Exact completion for any stationary finite signed affine trial, without a
matrix inverse or an independence premise.  Equality is characterized at the
level of synthesized Hilbert vectors, allowing singular coefficient systems.
The complete infinite Gram cross terms are retained.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.AffineHeadTrials

/-- Exact completion around any stationary affine trial. Every signed mixed
interaction is retained. This supplies a finite optimum certificate. -/
theorem affine_residual_norm_sq_eq_stationary_add_difference
    (s : Finset ℕ) (a astar : ℕ → ℝ) (u : ℕ → ThresholdHilbert)
    (ha : ∑ i ∈ s, a i = 1) (hstar : ∑ i ∈ s, astar i = 1)
    (E : ℝ)
    (hstationary : ∀ i ∈ s,
      inner ℝ (hilbertOne - affineTrial s astar u) (hilbertOne - u i) = E) :
    ‖hilbertOne - affineTrial s a u‖ ^ 2 =
      ‖hilbertOne - affineTrial s astar u‖ ^ 2 +
        ‖affineTrial s a u - affineTrial s astar u‖ ^ 2 := by
  let r := hilbertOne - affineTrial s astar u
  let t := hilbertOne - affineTrial s a u
  have hrt : inner ℝ r t = E := by
    dsimp [t]
    rw [affine_residual_eq_sum s a u ha]
    simp only [inner_sum, real_inner_smul_right]
    calc
      _ = ∑ i ∈ s, a i * E := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hstationary i hi]
      _ = E := by rw [← Finset.sum_mul, ha, one_mul]
  have hrr : inner ℝ r r = E := by
    calc
      inner ℝ r r = inner ℝ r (∑ i ∈ s, astar i • (hilbertOne - u i)) := by
        exact congrArg (fun x => inner ℝ r x)
          (affine_residual_eq_sum s astar u hstar)
      _ = ∑ i ∈ s, astar i * E := by
        simp only [inner_sum, real_inner_smul_right]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hstationary i hi]
      _ = E := by rw [← Finset.sum_mul, hstar, one_mul]
  have horth : inner ℝ r (t - r) = 0 := by
    rw [inner_sub_right, hrt, hrr, sub_self]
  have horth' : inner ℝ (t - r) r = 0 := by
    rw [real_inner_comm r (t - r), horth]
  have hex : t = r + (t - r) := by abel
  have hab : inner ℝ (r + (t - r)) (r + (t - r)) =
      inner ℝ r r + inner ℝ (t - r) (t - r) := by
    rw [inner_add_left, inner_add_right, inner_add_right, horth, horth']
    ring
  have hsq : ‖t‖ ^ 2 = ‖r‖ ^ 2 + ‖t - r‖ ^ 2 := by
    calc
      ‖t‖ ^ 2 = inner ℝ t t := (real_inner_self_eq_norm_sq _).symm
      _ = inner ℝ (r + (t - r)) (r + (t - r)) := congrArg₂ (inner ℝ) hex hex
      _ = inner ℝ r r + inner ℝ (t - r) (t - r) := hab
      _ = ‖r‖ ^ 2 + ‖t - r‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have hdiff : t - r = -(affineTrial s a u - affineTrial s astar u) := by
    dsimp [t, r]
    abel
  rw [hdiff, norm_neg] at hsq
  exact hsq

/-- The stationary trial is a complete infinite norm minimizer. -/
theorem affine_residual_norm_sq_ge_stationary
    (s : Finset ℕ) (a astar : ℕ → ℝ) (u : ℕ → ThresholdHilbert)
    (ha : ∑ i ∈ s, a i = 1) (hstar : ∑ i ∈ s, astar i = 1)
    (E : ℝ)
    (hstationary : ∀ i ∈ s,
      inner ℝ (hilbertOne - affineTrial s astar u) (hilbertOne - u i) = E) :
    ‖hilbertOne - affineTrial s astar u‖ ^ 2 ≤
      ‖hilbertOne - affineTrial s a u‖ ^ 2 := by
  rw [affine_residual_norm_sq_eq_stationary_add_difference s a astar u ha hstar E
    hstationary]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Equality in the complete minimum certificate holds exactly when the
synthesized affine trial agrees with the stationary trial. No coefficient
independence is assumed. -/
theorem affine_residual_norm_sq_eq_stationary_iff
    (s : Finset ℕ) (a astar : ℕ → ℝ) (u : ℕ → ThresholdHilbert)
    (ha : ∑ i ∈ s, a i = 1) (hstar : ∑ i ∈ s, astar i = 1)
    (E : ℝ)
    (hstationary : ∀ i ∈ s,
      inner ℝ (hilbertOne - affineTrial s astar u) (hilbertOne - u i) = E) :
    ‖hilbertOne - affineTrial s a u‖ ^ 2 =
        ‖hilbertOne - affineTrial s astar u‖ ^ 2 ↔
      affineTrial s a u = affineTrial s astar u := by
  constructor
  · intro he
    have hc := affine_residual_norm_sq_eq_stationary_add_difference
      s a astar u ha hstar E hstationary
    have hn : ‖affineTrial s a u - affineTrial s astar u‖ ^ 2 = 0 := by
      linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
  · intro he
    rw [he]

end RiemannResearch.RH.Pareto.AffineHeadTrials
