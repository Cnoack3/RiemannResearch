/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CRTPolygammaSigns

/-!
# Exact finite midpoint expansions with strictly positive remainder

No infinite Taylor rearrangement is needed: each finite kernel identity is
algebraic. All progression series are proved summable before taking their sums.
-/

open scoped BigOperators
namespace RiemannResearch.RH.CRTBlock
noncomputable section

def lMidpointTerm (j : ℕ) (t : ℝ) : ℝ := 2 / (t + 1)^(2 * j + 3)
def lMidpointRemainder (N : ℕ) (t : ℝ) : ℝ := lKernel t / (t + 1)^(2 * N)
def lMidpointApprox (Q r : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, ∑' k : ℕ, lMidpointTerm j (Q * k + r)
def lMidpointTail (Q r : ℝ) (N : ℕ) : ℝ :=
  ∑' k : ℕ, lMidpointRemainder N (Q * k + r)

theorem lMidpointRemainder_pos (N : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < lMidpointRemainder N t := by
  unfold lMidpointRemainder lKernel
  positivity

theorem lMidpointRemainder_le_kernel (N : ℕ) {t : ℝ} (ht : 0 < t) :
    lMidpointRemainder N t ≤ lKernel t := by
  apply div_le_self (lKernel_nonneg ht)
  exact one_le_pow₀ (show 1 ≤ t + 1 by linarith)

/-- Exact finite geometric step about the midpoint t+1. -/
theorem lMidpointRemainder_step (N : ℕ) {t : ℝ} (ht : 0 < t) :
    lMidpointRemainder N t = lMidpointTerm N t + lMidpointRemainder (N + 1) t := by
  have h0 : t ≠ 0 := ne_of_gt ht
  have h1 : t + 1 ≠ 0 := by positivity
  have h2 : t + 2 ≠ 0 := by positivity
  unfold lMidpointRemainder lMidpointTerm lKernel
  simp only [Nat.mul_add, Nat.mul_one, pow_add]
  field_simp
  <;> ring

theorem lMidpointTerm_le_kernel (j : ℕ) {t : ℝ} (ht : 0 < t) :
    lMidpointTerm j t ≤ lKernel t := by
  have h := lMidpointRemainder_step j ht
  have hn := lMidpointRemainder_pos (j + 1) ht
  have hl := lMidpointRemainder_le_kernel j ht
  linarith

theorem lMidpointTerm_summable (j : ℕ) {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r) :
    Summable (fun k : ℕ => lMidpointTerm j (Q * k + r)) := by
  exact (progressionL_summable hQ hr).of_nonneg_of_le
    (fun k => by unfold lMidpointTerm; positivity)
    (fun k => lMidpointTerm_le_kernel j (by positivity))

theorem lMidpointRemainder_summable (N : ℕ) {Q r : ℝ}
    (hQ : 0 < Q) (hr : 0 < r) :
    Summable (fun k : ℕ => lMidpointRemainder N (Q * k + r)) := by
  exact (progressionL_summable hQ hr).of_nonneg_of_le
    (fun k => (lMidpointRemainder_pos N (by positivity)).le)
    (fun k => lMidpointRemainder_le_kernel N (by positivity))

theorem lMidpointTail_step (N : ℕ) {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r) :
    lMidpointTail Q r N = (∑' k : ℕ, lMidpointTerm N (Q * k + r)) +
      lMidpointTail Q r (N + 1) := by
  calc
    _ = ∑' k : ℕ, (lMidpointTerm N (Q * k + r) +
        lMidpointRemainder (N + 1) (Q * k + r)) := by
      apply tsum_congr
      intro k
      exact lMidpointRemainder_step N (by positivity)
    _ = _ := (lMidpointTerm_summable N hQ hr).tsum_add
      (lMidpointRemainder_summable (N + 1) hQ hr)

/-- Exact L equality at every finite order N, with a signed (positive) remainder. -/
theorem progressionL_midpoint_exact (N : ℕ) {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r) :
    progressionL Q r = lMidpointApprox Q r N + lMidpointTail Q r N := by
  induction N with
  | zero => simp [lMidpointApprox, lMidpointTail, lMidpointRemainder, progressionL]
  | succ N ih =>
    have ha : lMidpointApprox Q r (N + 1) = lMidpointApprox Q r N +
        (∑' k : ℕ, lMidpointTerm N (Q * k + r)) := by
      simp [lMidpointApprox, Finset.sum_range_succ]
    rw [ha, add_assoc, ← lMidpointTail_step N hQ hr]
    exact ih

theorem lMidpointTail_pos (N : ℕ) {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r) :
    0 < lMidpointTail Q r N := by
  exact (lMidpointRemainder_summable N hQ hr).tsum_pos
    (fun k => (lMidpointRemainder_pos N (by positivity)).le) 0
    (lMidpointRemainder_pos N (by positivity))

theorem lMidpointTail_geometric_bound (N : ℕ) {Q r : ℝ}
    (hQ : 0 < Q) (hr : 0 < r) :
    lMidpointTail Q r N ≤ progressionL Q r / (r + 1)^(2 * N) := by
  change (∑' k : ℕ, lMidpointRemainder N (Q * k + r)) ≤
    (∑' k : ℕ, lKernel (Q * k + r)) / (r + 1)^(2 * N)
  rw [← tsum_div_const]
  apply Summable.tsum_le_tsum _ (lMidpointRemainder_summable N hQ hr)
    ((progressionL_summable hQ hr).div_const _)
  intro k
  apply div_le_div_of_nonneg_left (lKernel_nonneg (by positivity)) (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  have hk : 0 ≤ Q * (k : ℝ) := by positivity
  linarith

/-- The remainder control becomes sharper at every positive starting argument. -/
theorem lMidpointApprox_strict_lower (N : ℕ) {Q r : ℝ}
    (hQ : 0 < Q) (hr : 0 < r) : lMidpointApprox Q r N < progressionL Q r := by
  rw [progressionL_midpoint_exact N hQ hr]
  exact lt_add_of_pos_right _ (lMidpointTail_pos N hQ hr)

/-- A sharp elementary bound for all orders N >= 1 and t >= 1. -/
theorem midpoint_power_bound {t : ℝ} (ht : 1 ≤ t) (N : ℕ) (hN : 0 < N) :
    (4 : ℝ)^N * t ≤ (t + 1)^(2 * N) := by
  cases N with
  | zero => omega
  | succ n =>
    induction n with
    | zero => norm_num; nlinarith [sq_nonneg (t - 1)]
    | succ n ih =>
      have hfour : (4 : ℝ) ≤ (t + 1)^2 := by nlinarith
      have hpow : 0 ≤ (t + 1)^(2 * (n + 1)) := by positivity
      calc
        (4 : ℝ)^(n + 1 + 1) * t = 4 * ((4 : ℝ)^(n + 1) * t) := by
          rw [pow_succ]; ring
        _ ≤ 4 * (t + 1)^(2 * (n + 1)) := mul_le_mul_of_nonneg_left (ih (by omega)) (by norm_num)
        _ ≤ (t + 1)^2 * (t + 1)^(2 * (n + 1)) :=
          mul_le_mul_of_nonneg_right hfour hpow
        _ = (t + 1)^(2 * (n + 1 + 1)) := by
          simp only [Nat.mul_add, Nat.mul_one, pow_add]
          ring

/-- The L remainder is small relative to M, uniformly in the conductor. -/
theorem lMidpointTail_le_M (N : ℕ) (hN : 0 < N) {Q r : ℝ}
    (hQ : 0 < Q) (hr : 1 ≤ r) :
    lMidpointTail Q r N ≤ progressionM Q r / (4 : ℝ)^N := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  change (∑' k : ℕ, lMidpointRemainder N (Q * k + r)) ≤
    (∑' k : ℕ, lKernel (Q * k + r) / (Q * k + r)) / (4 : ℝ)^N
  rw [← tsum_div_const]
  apply Summable.tsum_le_tsum _ (lMidpointRemainder_summable N hQ hr0)
    ((progressionM_summable hQ hr0).div_const _)
  intro k
  have ht : 1 ≤ Q * (k : ℝ) + r := by
    have hprod : 0 ≤ Q * (k : ℝ) := by positivity
    linarith
  unfold lMidpointRemainder
  rw [div_div]
  apply div_le_div_of_nonneg_left (lKernel_nonneg (by positivity)) (by positivity)
  simpa only [mul_comm] using midpoint_power_bound ht N hN

/-- Each finite coefficient is an actual even-order polygamma value. -/
theorem lMidpointTerm_tsum_polygamma (j : ℕ) {Q r : ℝ}
    (hQ : 0 < Q) (hr : 0 < r) :
    (∑' k : ℕ, lMidpointTerm j (Q * k + r)) =
      -2 * iteratedDeriv (2 * j + 2) realDigamma ((r + 1) / Q) /
        (((2 * j + 2).factorial : ℝ) * Q^(2 * j + 3)) := by
  have hs : (∑' k : ℕ, lMidpointTerm j (Q * k + r)) =
      (2 / Q^(2 * j + 3)) * reciprocalPowerSeries (2 * j + 1) ((r + 1) / Q) := by
    unfold reciprocalPowerSeries
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    have he : Q * (k : ℝ) + r + 1 = Q * ((k : ℝ) + (r + 1) / Q) := by
      field_simp
      <;> ring
    unfold lMidpointTerm
    rw [he, mul_pow]
    simp only [Nat.add_assoc, div_eq_mul_inv, mul_inv_rev]
    ring
  have hp := iteratedDeriv_digamma_series (2 * j + 1)
    (show 0 < (r + 1) / Q by positivity)
  have hsign : (-1 : ℝ)^(2 * j + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  simp only [Nat.add_assoc, hsign, neg_one_mul] at hp
  rw [hs, hp]
  have hf : ((2 * j + 2).factorial : ℝ) ≠ 0 := by positivity
  have hQ0 : Q ≠ 0 := ne_of_gt hQ
  field_simp
  <;> ring

end
end RiemannResearch.RH.CRTBlock
