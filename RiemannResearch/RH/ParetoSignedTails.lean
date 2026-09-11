import RiemannResearch.RH.ParetoAnnihilatorPositivity
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
/-!
# Signed Pareto tails
Source: user-provided analytic research notes, September 11, 2026.
The zero coordinate of the anchored tail is conventional; identities for
its discrete difference are restricted to positive indices.
-/
open scoped BigOperators
open Filter
namespace RiemannResearch.RH.Pareto
noncomputable section
def signedCoefficient (h : ℕ → ℝ) (n : ℕ) : ℝ := positiveWeight n * h n
def signedTail (h : ℕ → ℝ) (k : ℕ) : ℝ := ∑' j, signedCoefficient h (j + k)
def anchoredSignedTail (h : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else signedTail h k
theorem signedCoefficient_summable {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2)) :
    Summable (signedCoefficient h) := by
  apply (weighted_abs_summable_of_square hs).of_norm_bounded
  intro k
  simp only [signedCoefficient, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (positiveWeight_nonneg k), le_refl]
theorem signedTail_eq_mean_sub_partial_sum {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2)) (k : ℕ) :
    signedTail h k = paretoMean h - ∑ j ∈ Finset.range k, signedCoefficient h j := by
  have heq := Summable.sum_add_tsum_nat_add k (signedCoefficient_summable hs)
  change (∑ j ∈ Finset.range k, signedCoefficient h j) + signedTail h k =
    paretoMean h at heq
  linarith
theorem signedTail_difference {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2)) (k : ℕ) :
    signedTail h k - signedTail h (k + 1) = signedCoefficient h k := by
  rw [signedTail_eq_mean_sub_partial_sum hs, signedTail_eq_mean_sub_partial_sum hs,
    Finset.sum_range_succ]
  ring
theorem signedTail_tendsto_zero {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2)) :
    Tendsto (signedTail h) atTop (nhds 0) := by
  have hp : Tendsto (fun k => ∑ j ∈ Finset.range k, signedCoefficient h j)
      atTop (nhds (paretoMean h)) :=
    (signedCoefficient_summable hs).hasSum.tendsto_sum_nat
  have ht := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => paretoMean h) atTop (nhds (paretoMean h))).sub hp
  have heq : signedTail h =
      (fun k => paretoMean h - ∑ j ∈ Finset.range k, signedCoefficient h j) :=
    funext (signedTail_eq_mean_sub_partial_sum hs)
  rw [heq]
  simpa only [sub_self] using ht
theorem signedTail_one_eq_mean {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2)) :
    signedTail h 1 = paretoMean h := by
  rw [signedTail_eq_mean_sub_partial_sum hs]
  simp [signedCoefficient, positiveWeight]
theorem anchoredSignedTail_zero (h : ℕ → ℝ) : anchoredSignedTail h 0 = 0 := by
  simp [anchoredSignedTail]
theorem anchoredSignedTail_pos (h : ℕ → ℝ) {k : ℕ} (hk : 0 < k) :
    anchoredSignedTail h k = signedTail h k := by
  simp [anchoredSignedTail, Nat.ne_of_gt hk]
theorem anchoredSignedTail_difference {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2)) {k : ℕ} (hk : 0 < k) :
    anchoredSignedTail h k - anchoredSignedTail h (k + 1) = signedCoefficient h k := by
  rw [anchoredSignedTail_pos h hk, anchoredSignedTail_pos h (by omega)]
  exact signedTail_difference hs k
theorem anchoredSignedTail_tendsto_zero {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2)) :
    Tendsto (anchoredSignedTail h) atTop (nhds 0) := by
  apply (signedTail_tendsto_zero hs).congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact (anchoredSignedTail_pos h (by omega)).symm
theorem anchoredSignedTail_one_eq_mean {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2)) :
    anchoredSignedTail h 1 = paretoMean h := by
  rw [anchoredSignedTail_pos h (by omega)]
  exact signedTail_one_eq_mean hs

theorem anchoredSignedTail_energy_density {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2)) (n : ℕ) :
    (n : ℝ) * ((n : ℝ) + 1) *
      (anchoredSignedTail h n - anchoredSignedTail h (n + 1)) ^ 2 =
      positiveWeight n * h n ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp [positiveWeight]
  · rw [anchoredSignedTail_difference hs (Nat.pos_of_ne_zero hn)]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hnR' : (n : ℝ) + 1 ≠ 0 := by positivity
    unfold signedCoefficient positiveWeight
    field_simp
theorem anchoredSignedTail_energy_summable {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2)) :
    Summable (fun n : ℕ => (n : ℝ) * ((n : ℝ) + 1) *
      (anchoredSignedTail h n - anchoredSignedTail h (n + 1)) ^ 2) := by
  simpa only [anchoredSignedTail_energy_density hs] using hs
theorem anchoredSignedTail_energy_eq {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2)) :
    (∑' n : ℕ, (n : ℝ) * ((n : ℝ) + 1) *
      (anchoredSignedTail h n - anchoredSignedTail h (n + 1)) ^ 2) =
      ∑' n, positiveWeight n * h n ^ 2 := by
  apply tsum_congr
  exact anchoredSignedTail_energy_density hs
theorem eq_zero_of_anchoredSignedTail_eq_zero {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2))
    (ht : anchoredSignedTail h = 0) {n : ℕ} (hn : 0 < n) : h n = 0 := by
  have hd := anchoredSignedTail_difference hs hn
  rw [ht] at hd
  have hc : signedCoefficient h n = 0 := by simpa using hd.symm
  have hw : 0 < positiveWeight n := by unfold positiveWeight; positivity
  exact (mul_eq_zero.mp hc).resolve_left (ne_of_gt hw)
end
end RiemannResearch.RH.Pareto
