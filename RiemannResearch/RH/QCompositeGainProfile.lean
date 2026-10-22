/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.InverseSquareAbelTail
import RiemannResearch.Analysis.PeriodicWeightedMean
import RiemannResearch.RH.QCompositeSixGain
import RiemannResearch.RH.QMobiusExactHead
import RiemannResearch.RH.QSignedEnergyCertificate
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Location dependence of the composite-anchor gain

Independent user-authorized continuation, 18 October 2026, from
QCompositeSixGain's legal B_4,B_5 trial. Kernel rational certificates give
the exact signed period means and centered primitive bounds.

The original legal trial and its actual optimized Q line gain are at least
1/(3100*zetaTwo). In contrast, translating its signed physical gain profile
by K>=63 makes the complete inverse-square sum negative; every positive
step profile does so by K>=110. Translated profiles are not asserted to be
legal growing canonical heads. These are finite arithmetic and location
obstruction results; the growing-block power-cost estimate remains open.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCompositeGainProfile
open QCompositeSixGain ZetaTwoHilbert ZetaTwoProbability
open RiemannResearch.Analysis.InverseSquareAbelTail
open RiemannResearch.Analysis.PeriodicWeightedMean

def linearGain (n : ℕ) : ℝ := -2 * oldError n * errorStep n
def quadraticGain (n : ℕ) : ℝ := -(errorStep n)^2
def profile (t : ℝ) (n : ℕ) : ℝ :=
  oldError n^2 - (oldError n + t * errorStep n)^2

theorem profile_eq (t : ℝ) (n : ℕ) :
    profile t n = t * linearGain n + t^2 * quadraticGain n := by
  unfold profile linearGain quadraticGain
  ring

theorem linearGain_mod (n : ℕ) : linearGain n = linearGain (n % 30) := by
  simp only [linearGain, oldError, errorStep,
    Nat.mod_mod_of_dvd n (by norm_num : 2 ∣ 30),
    Nat.mod_mod_of_dvd n (by norm_num : 3 ∣ 30),
    Nat.mod_mod_of_dvd n (by norm_num : 5 ∣ 30),
    Nat.mod_mod_of_dvd n (by norm_num : 6 ∣ 30)]

theorem quadraticGain_mod (n : ℕ) : quadraticGain n = quadraticGain (n % 30) := by
  simp only [quadraticGain, errorStep,
    Nat.mod_mod_of_dvd n (by norm_num : 5 ∣ 30),
    Nat.mod_mod_of_dvd n (by norm_num : 6 ∣ 30)]

theorem linearGain_period (n : ℕ) : linearGain (n + 30) = linearGain n := by
  rw [linearGain_mod (n + 30), linearGain_mod n]
  simp only [Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod]

theorem quadraticGain_period (n : ℕ) : quadraticGain (n + 30) = quadraticGain n := by
  rw [quadraticGain_mod (n + 30), quadraticGain_mod n]
  simp only [Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod]

theorem linearGain_abs (n : ℕ) : |linearGain n| ≤ 1 := by
  rw [linearGain_mod]
  have h := Nat.mod_lt n (by norm_num : 0 < 30)
  generalize n % 30 = j at *
  interval_cases j <;> norm_num [linearGain, oldError, errorStep]

theorem quadraticGain_abs (n : ℕ) : |quadraticGain n| ≤ 1 := by
  rw [quadraticGain_mod]
  have h := Nat.mod_lt n (by norm_num : 0 < 30)
  generalize n % 30 = j at *
  interval_cases j <;> norm_num [quadraticGain, errorStep]

set_option maxRecDepth 10000 in
theorem linearGain_mean :
    partialSum (fun n => linearGain (n + 1) + 1/540) 30 = 0 := by
  norm_num [partialSum, Finset.sum_range_succ, linearGain, oldError, errorStep]

set_option maxRecDepth 10000 in
theorem quadraticGain_mean :
    partialSum (fun n => quadraticGain (n + 1) + 31/5400) 30 = 0 := by
  norm_num [partialSum, Finset.sum_range_succ, quadraticGain, errorStep]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- Kernel rational normalization of all 30 centered prefixes.
theorem linearGain_short (n : ℕ) (hn : n < 30) :
    |partialSum (fun k => linearGain (k + 1) + 1/540) n| ≤ 11/54 := by
  interval_cases n <;>
    norm_num [partialSum, Finset.sum_range_succ, linearGain, oldError, errorStep]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- Kernel rational normalization of all 30 centered prefixes.
theorem quadraticGain_short (n : ℕ) (hn : n < 30) :
    |partialSum (fun k => quadraticGain (k + 1) + 31/5400) n| ≤ 13/450 := by
  interval_cases n <;>
    norm_num [partialSum, Finset.sum_range_succ, quadraticGain, errorStep]

theorem linearGain_prefix (n : ℕ) :
    |partialSum (fun k => linearGain (k + 1) + 1/540) n| ≤ 11/54 := by
  apply periodic_prefix_bound _ 30 (11/54) (by norm_num)
    (fun k => by rw [show k + 30 + 1 = (k + 1)+30 by omega, linearGain_period])
    linearGain_mean linearGain_short n

theorem quadraticGain_prefix (n : ℕ) :
    |partialSum (fun k => quadraticGain (k + 1) + 31/5400) n| ≤ 13/450 := by
  apply periodic_prefix_bound _ 30 (13/450) (by norm_num)
    (fun k => by rw [show k + 30 + 1 = (k + 1)+30 by omega, quadraticGain_period])
    quadraticGain_mean quadraticGain_short n

theorem linearGain_tail_negative (K : ℕ) (hK : 110 ≤ K) :
    (∑' k, linearGain (k + 1) * weight K k) < 0 := by
  apply weighted_sum_neg (fun k => linearGain (k + 1)) K (-1/540) (11/54) 1
    (fun k => linearGain_abs (k + 1))
  · simpa only [neg_div, sub_neg_eq_add] using linearGain_prefix
  · norm_num
  · have h : (110 : ℝ) ≤ K := by exact_mod_cast hK
    push_cast
    linarith

theorem quadraticGain_tail_negative (K : ℕ) (hK : 110 ≤ K) :
    (∑' k, quadraticGain (k + 1) * weight K k) < 0 := by
  apply weighted_sum_neg (fun k => quadraticGain (k + 1)) K (-31/5400) (13/450) 1
    (fun k => quadraticGain_abs (k + 1))
  · simpa only [neg_div, sub_neg_eq_add] using quadraticGain_prefix
  · norm_num
  · have h : (110 : ℝ) ≤ K := by exact_mod_cast hK
    push_cast
    linarith

theorem profile_tail_eq (t : ℝ) (K : ℕ) :
    (∑' k, profile t (k + 1) * weight K k) =
      t * (∑' k, linearGain (k + 1) * weight K k) +
      t^2 * (∑' k, quadraticGain (k + 1) * weight K k) := by
  have hl := bounded_summable (fun k => linearGain (k + 1)) K 1
    (fun k => linearGain_abs (k + 1))
  have hq := bounded_summable (fun k => quadraticGain (k + 1)) K 1
    (fun k => quadraticGain_abs (k + 1))
  simp_rw [profile_eq, add_mul, mul_assoc]
  rw [(hl.mul_left t).tsum_add (hq.mul_left (t^2)), tsum_mul_left, tsum_mul_left]

theorem positive_profile_translation_negative (K : ℕ) (hK : 110 ≤ K)
    (t : ℝ) (ht : 0 < t) :
    (∑' k, profile t (k + 1) * weight K k) < 0 := by
  rw [profile_tail_eq]
  exact add_neg (mul_neg_of_pos_of_neg ht (linearGain_tail_negative K hK))
    (mul_neg_of_pos_of_neg (sq_pos_of_pos ht) (quadraticGain_tail_negative K hK))


set_option maxRecDepth 10000 in
theorem quarter_mean :
    partialSum (fun n => physicalGain (n + 1) + 71/86400) 30 = 0 := by
  norm_num [partialSum, Finset.sum_range_succ, physicalGain, oldError, errorStep]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- Kernel rational normalization of all 30 centered prefixes.
theorem quarter_short (n : ℕ) (hn : n < 30) :
    |partialSum (fun k => physicalGain (k + 1) + 71/86400) n| ≤ 2249/43200 := by
  interval_cases n <;>
    norm_num [partialSum, Finset.sum_range_succ, physicalGain, oldError, errorStep]

theorem quarter_prefix (n : ℕ) :
    |partialSum (fun k => physicalGain (k + 1) + 71/86400) n| ≤ 2249/43200 := by
  apply periodic_prefix_bound _ 30 (2249/43200) (by norm_num)
    (fun k => by
      rw [physicalGain_mod (k + 30 + 1), physicalGain_mod (k + 1)]
      congr 2
      omega)
    quarter_mean quarter_short n

theorem quarter_translation_negative (K : ℕ) (hK : 63 ≤ K) :
    (∑' k, physicalGain (k + 1) * weight K k) < 0 := by
  apply weighted_sum_neg (fun k => physicalGain (k + 1)) K
    (-71/86400) (2249/43200) 1 (fun k => physicalGain_abs (k + 1))
  · simpa only [neg_div, sub_neg_eq_add] using quarter_prefix
  · norm_num
  · have h : (63 : ℝ) ≤ K := by exact_mod_cast hK
    push_cast
    linarith

theorem profile_period_mean (t : ℝ) :
    (partialSum (fun n => profile t (n + 1)) 30) / 30 =
      -(10*t + 31*t^2)/5400 := by
  have hl : partialSum (fun n => linearGain (n + 1)) 30 = -1/18 := by
    have h := linearGain_mean
    simp only [partialSum, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul] at *
    linarith
  have hq : partialSum (fun n => quadraticGain (n + 1)) 30 = -31/180 := by
    have h := quadraticGain_mean
    simp only [partialSum, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul] at *
    linarith
  have he : partialSum (fun n => profile t (n + 1)) 30 =
      t * partialSum (fun n => linearGain (n + 1)) 30 +
      t^2 * partialSum (fun n => quadraticGain (n + 1)) 30 := by
    unfold partialSum
    simp_rw [profile_eq]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [he, hl, hq]
  ring


theorem line_error_sequence (t : ℝ) (n : ℕ) (hn : 0 < n) :
    ZetaTwoHilbert.qSequence
      (ZetaTwoHilbert.qOne - (QMobiusExactHead.exactHead 4 + t • direction)) n =
        oldError n + t * errorStep n := by
  have he : qOne - (QMobiusExactHead.exactHead 4 + t • direction) =
      (1-t) • (qOne - QMobiusExactHead.exactHead 4) +
        t • (qOne - QMobiusExactHead.exactHead 5) := by
    unfold direction
    module
  rw [he]
  change qSequenceLinear (_ + _) n = _
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change (1-t) * qSequence (qOne - QMobiusExactHead.exactHead 4) n +
    t * qSequence (qOne - QMobiusExactHead.exactHead 5) n = _
  rw [oldError_sequence n hn, freshError_sequence n hn]
  ring

theorem profile_signedEnergy (t : ℝ) (n : ℕ) :
    QSignedEnergyCertificate.signedEnergy
      (qOne - QMobiusExactHead.exactHead 4)
      (qOne - (QMobiusExactHead.exactHead 4 + t • direction)) n =
        profile t n := by
  by_cases hn : n = 0
  · subst n
    norm_num [QSignedEnergyCertificate.signedEnergy, profile, oldError, errorStep]
  · rw [QSignedEnergyCertificate.signedEnergy,
      oldError_sequence n (Nat.pos_of_ne_zero hn),
      line_error_sequence t n (Nat.pos_of_ne_zero hn)]
    rfl

theorem profile_energy_series (t : ℝ) :
    zetaTwo * (‖qOne - QMobiusExactHead.exactHead 4‖^2 -
      ‖qOne - (QMobiusExactHead.exactHead 4 + t • direction)‖^2) =
        ∑' n : ℕ, profile t n / (n : ℝ)^2 := by
  rw [QSignedEnergyCertificate.energy_difference_series]
  apply tsum_congr
  intro n
  rw [profile_signedEnergy]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Kernel rational normalization of the same complete 240-site prefix.
theorem quarter_weighted_prefix :
    (329/1000000 : ℝ) ≤
      ∑ n ∈ Finset.range 241, physicalGain n / (n : ℝ)^2 := by
  norm_num [Finset.sum_range_succ, physicalGain, oldError, errorStep]

theorem trial_gain_lower_refined :
    (1/3100 : ℝ) / zetaTwo ≤
      ‖qOne - QMobiusExactHead.exactHead 4‖^2 - ‖qOne - trial‖^2 := by
  let μ : ℝ := -71/86400
  let B : ℝ := 2249/43200
  have he := QSignedEnergyCertificate.energy_difference_prefix_tail
    (qOne - QMobiusExactHead.exactHead 4) (qOne - trial) 240
  simp only [QCompositeSixGain.signedEnergy_eq] at he
  have hp (k : ℕ) : physicalGain (k + (240 + 1)) = physicalGain (k + 1) := by
    rw [physicalGain_mod (k+(240 + 1)), physicalGain_mod (k + 1)]
    congr 1
    omega
  have ht : (∑' k : ℕ, physicalGain (k+(240 + 1)) /
      ((k+(240 + 1) : ℕ) : ℝ)^2) =
        ∑' k, physicalGain (k + 1) * weight 240 k := by
    apply tsum_congr
    intro k
    rw [hp]
    simp only [weight, mul_one_div, Nat.add_assoc]
  rw [ht] at he
  have hb : ∀ n, |partialSum (fun k => physicalGain (k + 1) - μ) n| ≤ B := by
    simpa only [μ, B, neg_div, sub_neg_eq_add] using quarter_prefix
  have hc := centered_error_bound (fun k => physicalGain (k + 1)) 240 μ B
    (bounded_summable _ 240 1 (fun k => physicalGain_abs (k + 1))) hb
  have hl := (abs_le.mp hc).1
  have hm := mul_le_mul_of_nonpos_left (weight_mass_upper 240 (by norm_num))
    (show μ ≤ 0 by norm_num [μ])
  have hprefix := quarter_weighted_prefix
  apply (div_le_iff₀ zetaTwo_pos).mpr
  dsimp [μ, B] at hl hm
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hl hm he
  nlinarith only [he, hl, hm, hprefix]

theorem optimized_gain_lower_refined : (1/3100 : ℝ) / zetaTwo ≤ gain := by
  have h := line_completion (1/4)
  have ht : QMobiusExactHead.exactHead 4 + (1/4 : ℝ) • direction = trial := by
    unfold trial direction
    module
  rw [ht] at h
  have hn : 0 ≤ denominator * ((1/4 : ℝ) - source / denominator)^2 :=
    mul_nonneg denominator_pos.le (sq_nonneg _)
  linarith only [trial_gain_lower_refined, h, hn]

end RiemannResearch.RH.QCompositeGainProfile
