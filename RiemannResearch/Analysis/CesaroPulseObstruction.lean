/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ConditionalMeanEnergy
import RiemannResearch.RH.ArithmeticCumulativeEnergy

/-!
# Actual adjacent-pulse obstruction to a bounded inverse of Cesaro averaging

All weighted series below have finite support, which is proved explicitly.
No statement that these pulses are legal Nyman--Beurling functions is made.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Analysis.Cesaro
open RH.Pareto RH.ArithmeticCumulative Probability.ConditionalIID

/-- A positive unit pulse followed by a negative unit pulse. -/
def adjacentPulse (N n : ℕ) : ℝ :=
  (if n = N then 1 else 0) - (if n = N + 1 then 1 else 0)

theorem adjacentPulse_zero_off (N n : ℕ) (h : n ≠ N) (h' : n ≠ N + 1) :
    adjacentPulse N n = 0 := by simp [adjacentPulse, h, h']

theorem adjacentPulse_square_summable (N : ℕ) :
    Summable (fun n : ℕ => weight n * adjacentPulse N n ^ 2) := by
  apply summable_of_ne_finset_zero (s := {N, N + 1})
  intro n hn
  have h : n ≠ N ∧ n ≠ N + 1 := by simpa using hn
  simp [adjacentPulse_zero_off N n h.1 h.2]

/-- The arithmetic mean of the adjacent pulse is supported at exactly one endpoint. -/
theorem cesaro_adjacentPulse (N : ℕ) (hN : 0 < N) (t : ℕ) :
    cesaro (adjacentPulse N) t = if t = N then 1 / (N : ℝ) else 0 := by
  have he : cesaro (adjacentPulse N) t =
      ((if N ∈ Finset.Icc 1 t then (1 : ℝ) else 0) -
       (if N + 1 ∈ Finset.Icc 1 t then (1 : ℝ) else 0)) / (t : ℝ) := by
    simp only [cesaro, adjacentPulse, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  rw [he]
  by_cases ht : t < N
  · simp [Finset.mem_Icc, ne_of_lt ht, show ¬ N ≤ t by omega,
      show ¬ N + 1 ≤ t by omega]
  · by_cases ht' : t = N
    · subst t
      simp [Finset.mem_Icc, hN, show 1 ≤ N by omega]
    · have hle : N + 1 ≤ t := by omega
      simp [Finset.mem_Icc, ht', show 1 ≤ N by omega, show N ≤ t by omega, hle]

/-- Exact finite-support weighted norm of the adjacent pulse. -/
theorem adjacentPulse_fullSquaredNorm (N : ℕ) (hN : 0 < N) :
    fullSquaredNorm (adjacentPulse N) = 2 / ((N : ℝ) * ((N : ℝ) + 2)) := by
  have hsum : fullSquaredNorm (adjacentPulse N) = weight N + weight (N + 1) := by
    unfold fullSquaredNorm
    rw [tsum_eq_sum (s := {N, N + 1}) (by
      intro n hn
      have h : n ≠ N ∧ n ≠ N + 1 := by simpa using hn
      simp [adjacentPulse_zero_off N n h.1 h.2])]
    simp [adjacentPulse, show N ≠ N + 1 by omega, show N + 1 ≠ N by omega]
  rw [hsum]
  unfold weight
  push_cast
  have hn : (N : ℝ) ≠ 0 := by positivity
  have hn1 : (N : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : (N : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The conditional-mean energy is also a genuine convergent series. -/
theorem adjacentPulse_conditional_summable (N : ℕ) (hN : 0 < N) :
    Summable (fun k : ℕ => conditionalWeight k * (cesaro (adjacentPulse N) (k + 1)) ^ 2) := by
  apply summable_of_ne_finset_zero (s := {N - 1})
  intro k hk
  have hk' : k + 1 ≠ N := by simp only [Finset.mem_singleton] at hk; omega
  simp [cesaro_adjacentPulse N hN, hk']

/-- Exact conditional-mean energy of the pulse. -/
theorem adjacentPulse_conditionalMeanSquare (N : ℕ) (hN : 0 < N) :
    conditionalMeanSquare (adjacentPulse N) =
      2 / ((N : ℝ) ^ 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
  unfold conditionalMeanSquare
  rw [tsum_eq_single (N - 1) (by
    intro k hk
    have hk' : k + 1 ≠ N := by omega
    simp [cesaro_adjacentPulse N hN, hk'])]
  have hn : N - 1 + 1 = N := by omega
  simp only [cesaro_adjacentPulse N hN, hn, ite_true, conditionalWeight]
  unfold mixtureWeight
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

/-- The exact squared-norm ratio tends to zero, despite injectivity of Cesaro means. -/
theorem adjacentPulse_energy_ratio (N : ℕ) (hN : 0 < N) :
    conditionalMeanSquare (adjacentPulse N) =
      weight N * fullSquaredNorm (adjacentPulse N) := by
  rw [adjacentPulse_conditionalMeanSquare N hN, adjacentPulse_fullSquaredNorm N hN]
  unfold weight
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

/-- There is no positive lower energy bound on the whole weighted Hilbert domain. -/
theorem no_positive_cesaro_energy_lower_bound :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ F : ℕ → ℝ,
      Summable (fun n => weight n * F n ^ 2) →
      Summable (fun k => conditionalWeight k * (cesaro F (k + 1)) ^ 2) →
      c * fullSquaredNorm F ≤ conditionalMeanSquare F := by
  rintro ⟨c, hc, hbound⟩
  have hl : ∀ᶠ N : ℕ in atTop, weight N < c :=
    weight_tendsto_zero.eventually (gt_mem_nhds hc)
  obtain ⟨N, hN, hNc⟩ := ((eventually_gt_atTop 0).and hl).exists
  have h := hbound (adjacentPulse N) (adjacentPulse_square_summable N)
    (adjacentPulse_conditional_summable N hN)
  rw [adjacentPulse_energy_ratio N hN] at h
  have hp : 0 < fullSquaredNorm (adjacentPulse N) := by
    rw [adjacentPulse_fullSquaredNorm N hN]
    positivity
  nlinarith

end RiemannResearch.Analysis.Cesaro
