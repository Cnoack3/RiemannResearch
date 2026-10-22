/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerCoprimeCoefficients
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QDivisorWaveletDensity
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Threshold series for floor-log coefficients

Source: the user's research request and FpCoprimeCoefficientsResearch20261022.md,
22 October 2026. Count positive powers below d*n, then exchange the nonnegative
double series using the already proved integrability of Nat.log p (d*n).

These are actual inverse-square Zipf expectations. F_p remains Nat.log p n,
not the prime valuation. The mean expansion retains its entire threshold tail;
the general conductor error retains every signed Moebius-weighted tail.
Prime-power coefficient terms are finite integer-interval sums, with proved
convergence and an exact remaining series. Quantitative tail-rate certification
is still separate. No legal-closure membership, Parseval saturation, higher
Meixner completeness, or RH conclusion is asserted.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity QDivisorHilbert

def logThresholdMass (p d j : ℕ) : ℝ :=
  ∑' n : ℕ, if p ^ (j + 1) ≤ d * n then positiveQWeight n else 0

theorem log_threshold_iff (p d n j : ℕ) (hp : 1 < p) :
    p ^ (j + 1) ≤ d * n ↔ j < Nat.log p (d * n) := by
  by_cases hn : d * n = 0
  · simp [hn, Nat.not_le_of_gt (pow_pos (by omega : 0 < p) (j + 1))]
  · rw [← Nat.le_log_iff_pow_le hp hn]
    omega

theorem log_threshold_row (p d n : ℕ) (hp : 1 < p) :
    HasSum (fun j : ℕ => if p ^ (j + 1) ≤ d * n then positiveQWeight n else 0)
      (positiveQWeight n * (Nat.log p (d * n) : ℝ)) := by
  have hz : ∀ j ∉ Finset.range (Nat.log p (d * n)),
      (if p ^ (j + 1) ≤ d * n then positiveQWeight n else 0) = 0 := by
    intro j hj
    simp only [Finset.mem_range] at hj
    simp [log_threshold_iff p d n j hp, hj]
  have he : (∑' j : ℕ, if p ^ (j + 1) ≤ d * n then positiveQWeight n else 0) =
      positiveQWeight n * (Nat.log p (d * n) : ℝ) := by
    rw [tsum_eq_sum hz]
    calc
      _ = ∑ _j ∈ Finset.range (Nat.log p (d * n)), positiveQWeight n := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [log_threshold_iff p d n j hp, Finset.mem_range.mp hj]
      _ = _ := by simp [mul_comm]
  exact he ▸ (summable_of_ne_finset_zero hz).hasSum

theorem log_threshold_double_summable (p d : ℕ) (hp : 1 < p) (hd : 0 < d) :
    Summable (fun x : ℕ × ℕ =>
      if p ^ (x.2 + 1) ≤ d * x.1 then positiveQWeight x.1 else 0) := by
  apply (summable_prod_of_nonneg (by
    intro x
    dsimp
    split_ifs
    · exact positiveQWeight_nonneg _
    · exact le_rfl)).2
  constructor
  · intro n
    exact (log_threshold_row p d n hp).summable
  · simpa only [(log_threshold_row p d _ hp).tsum_eq] using
      dilatedTargetMean_summable p d hp hd

theorem dilatedTargetMean_threshold_series (p d : ℕ) (hp : 1 < p) (hd : 0 < d) :
    dilatedTargetMean p d = ∑' j : ℕ, logThresholdMass p d j := by
  rw [dilatedTargetMean_weighted p d hp hd]
  calc
    _ = ∑' n : ℕ, ∑' j : ℕ,
        if p ^ (j + 1) ≤ d * n then positiveQWeight n else 0 := by
      apply tsum_congr
      intro n
      exact (log_threshold_row p d n hp).tsum_eq.symm
    _ = _ := by
      exact (Summable.tsum_comm (f := fun n j : ℕ =>
        if p ^ (j + 1) ≤ d * n then positiveQWeight n else 0)
        (log_threshold_double_summable p d hp hd)).symm

theorem logThresholdMass_nonneg (p d j : ℕ) : 0 ≤ logThresholdMass p d j := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact positiveQWeight_nonneg _
  · exact le_rfl

/-- The exact integer ceiling, avoiding rounding in coefficient evaluation. -/
def logThresholdCutoff (p d j : ℕ) : ℕ := (p ^ (j + 1) - 1) / d + 1

theorem logThresholdCutoff_le_iff (p d j n : ℕ) (hp : 1 < p) (hd : 0 < d) :
    logThresholdCutoff p d j ≤ n ↔ p ^ (j + 1) ≤ d * n := by
  unfold logThresholdCutoff
  rw [Nat.add_one_le_iff, Nat.div_lt_iff_lt_mul hd, Nat.mul_comm n d]
  have hpow : 0 < p ^ (j + 1) := pow_pos (by omega) _
  omega

/-- Threshold mass is the actual Zipf mass above the exact integer ceiling. -/
theorem logThresholdMass_cutoff (p d j : ℕ) (hp : 1 < p) (hd : 0 < d) :
    logThresholdMass p d j =
      ∑' n : ℕ, if logThresholdCutoff p d j ≤ n then positiveQWeight n else 0 := by
  apply tsum_congr
  intro n
  simp only [logThresholdCutoff_le_iff p d j n hp hd]

theorem logThresholdMass_summable (p d : ℕ) (hp : 1 < p) (hd : 0 < d) :
    Summable (logThresholdMass p d) :=
  (log_threshold_double_summable p d hp hd).prod_symm.prod

/-- Threshold truncation retains the literal infinite level tail. -/
theorem dilatedTargetMean_threshold_head_tail (p d K : ℕ)
    (hp : 1 < p) (hd : 0 < d) :
    dilatedTargetMean p d =
      (∑ j ∈ Finset.range K, logThresholdMass p d j) +
      ∑' j : ℕ, logThresholdMass p d (j + K) := by
  rw [dilatedTargetMean_threshold_series p d hp hd]
  exact (Summable.sum_add_tsum_nat_add K (logThresholdMass_summable p d hp hd)).symm

theorem dilatedTargetMean_threshold_tendsto (p d : ℕ) (hp : 1 < p) (hd : 0 < d) :
    Filter.Tendsto (fun K => ∑ j ∈ Finset.range K, logThresholdMass p d j)
      Filter.atTop (nhds (dilatedTargetMean p d)) := by
  rw [dilatedTargetMean_threshold_series p d hp hd]
  exact (logThresholdMass_summable p d hp hd).tendsto_sum_tsum_nat

theorem dilatedTargetMean_threshold_remainder_nonneg (p d K : ℕ)
    (hp : 1 < p) (hd : 0 < d) :
    0 ≤ dilatedTargetMean p d - ∑ j ∈ Finset.range K, logThresholdMass p d j := by
  rw [dilatedTargetMean_threshold_head_tail p d K hp hd]
  simpa only [add_sub_cancel_left] using
    (tsum_nonneg (fun j => logThresholdMass_nonneg p d (j + K)))

/-- Every positive and negative Moebius-weighted tail remains in the error. -/
theorem qTarget_basis_threshold_error_exact (p K : ℕ) (hp : 1 < p) (t : ℕ+) :
    inner ℝ (qTarget p hp) (normalizedDivisorWavelet t) -
      (∑ d ∈ (t : ℕ).divisors, (ArithmeticFunction.moebius ((t : ℕ) / d) : ℝ) *
        ∑ j ∈ Finset.range K, logThresholdMass p d j) / Real.sqrt (qJordanTwo t) =
      (∑ d ∈ (t : ℕ).divisors, (ArithmeticFunction.moebius ((t : ℕ) / d) : ℝ) *
        ∑' j : ℕ, logThresholdMass p d (j + K)) / Real.sqrt (qJordanTwo t) := by
  rw [qTarget_inner_basis_moebius p hp t, ← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [dilatedTargetMean_threshold_head_tail p d K hp (Nat.pos_of_mem_divisors hd)]
  ring

theorem logThresholdMass_difference_interval (p d e j : ℕ)
    (hp : 1 < p) (hd : 0 < d) (hde : d ≤ e) :
    logThresholdMass p e j - logThresholdMass p d j =
      ∑ n ∈ Finset.Ico (logThresholdCutoff p e j) (logThresholdCutoff p d j),
        positiveQWeight n := by
  have he : 0 < e := lt_of_lt_of_le hd hde
  have hs (a : ℕ) : Summable (fun n : ℕ =>
      if p ^ (j + 1) ≤ a * n then positiveQWeight n else 0) := by
    apply Summable.of_nonneg_of_le _ _ positiveQWeight_summable
    · intro n
      split_ifs
      · exact positiveQWeight_nonneg n
      · exact le_rfl
    · intro n
      split_ifs
      · exact le_rfl
      · exact positiveQWeight_nonneg n
  have hab (n : ℕ) : d * n ≤ e * n := Nat.mul_le_mul_right n hde
  unfold logThresholdMass
  rw [← (hs e).tsum_sub (hs d)]
  have hz : ∀ n ∉ Finset.Ico (logThresholdCutoff p e j) (logThresholdCutoff p d j),
      (if p ^ (j + 1) ≤ e * n then positiveQWeight n else 0) -
      (if p ^ (j + 1) ≤ d * n then positiveQWeight n else 0) = 0 := by
    intro n hn
    have ha := logThresholdCutoff_le_iff p e j n hp he
    have hb := logThresholdCutoff_le_iff p d j n hp hd
    simp only [Finset.mem_Ico] at hn
    by_cases h1 : p ^ (j + 1) ≤ e * n
    · by_cases h2 : p ^ (j + 1) ≤ d * n
      · simp [h1, h2]
      · exact False.elim (hn ⟨ha.mpr h1, Nat.lt_of_not_ge (fun h => h2 (hb.mp h))⟩)
    · have h2 : ¬ p ^ (j + 1) ≤ d * n := fun h => h1 (h.trans (hab n))
      simp [h1, h2]
  rw [tsum_eq_sum hz]
  apply Finset.sum_congr rfl
  intro n hn
  rcases Finset.mem_Ico.mp hn with ⟨ha, hb⟩
  have h1 := (logThresholdCutoff_le_iff p e j n hp he).mp ha
  have h2 : ¬p ^ (j + 1) ≤ d * n := by
    rw [← logThresholdCutoff_le_iff p d j n hp hd]
    omega
  simp [h1, h2]

/-- Positive finite interval contributions to a prime-power coefficient. -/
def primePowerThresholdTerm (p q k j : ℕ) : ℝ :=
  (∑ n ∈ Finset.Ico (logThresholdCutoff p (q ^ (k + 1)) j)
      (logThresholdCutoff p (q ^ k) j), positiveQWeight n) /
    Real.sqrt (qJordanTwo (q ^ (k + 1)))

theorem qTarget_primePower_threshold_hasSum (p q k : ℕ)
    (hp : 1 < p) (hq : q.Prime) :
    HasSum (primePowerThresholdTerm p q k)
      (inner ℝ (qTarget p hp)
        (normalizedDivisorWavelet ⟨q ^ (k + 1), pow_pos hq.pos _⟩)) := by
  have hle : q ^ k ≤ q ^ (k + 1) := by
    exact Nat.pow_le_pow_right hq.pos (Nat.le_succ k)
  have hsum := ((logThresholdMass_summable p (q ^ (k + 1)) hp
    (pow_pos hq.pos _)).hasSum.sub
    (logThresholdMass_summable p (q ^ k) hp (pow_pos hq.pos _)).hasSum).div_const
      (Real.sqrt (qJordanTwo (q ^ (k + 1))))
  rw [← dilatedTargetMean_threshold_series p (q ^ (k + 1)) hp (pow_pos hq.pos _),
    ← dilatedTargetMean_threshold_series p (q ^ k) hp (pow_pos hq.pos _),
    ← qTarget_inner_primePower_mean_difference p q k hp hq] at hsum
  have heq : (fun j => (logThresholdMass p (q ^ (k + 1)) j -
      logThresholdMass p (q ^ k) j) / Real.sqrt (qJordanTwo (q ^ (k + 1)))) =
      primePowerThresholdTerm p q k := by
    funext j
    rw [logThresholdMass_difference_interval p (q ^ k) (q ^ (k + 1)) j hp
      (pow_pos hq.pos _) hle]
    rfl
  rw [heq] at hsum
  exact hsum

theorem primePowerThresholdTerm_nonneg (p q k j : ℕ) :
    0 ≤ primePowerThresholdTerm p q k j := by
  apply div_nonneg
  · exact Finset.sum_nonneg (fun n _ => positiveQWeight_nonneg n)
  · exact Real.sqrt_nonneg _

/-- Finite, evaluable threshold head and the complete nonnegative coefficient tail. -/
theorem qTarget_primePower_threshold_head_tail (p q k K : ℕ)
    (hp : 1 < p) (hq : q.Prime) :
    inner ℝ (qTarget p hp)
        (normalizedDivisorWavelet ⟨q ^ (k + 1), pow_pos hq.pos _⟩) =
      (∑ j ∈ Finset.range K, primePowerThresholdTerm p q k j) +
      ∑' j : ℕ, primePowerThresholdTerm p q k (j + K) := by
  rw [← (qTarget_primePower_threshold_hasSum p q k hp hq).tsum_eq]
  exact (Summable.sum_add_tsum_nat_add K
    (qTarget_primePower_threshold_hasSum p q k hp hq).summable).symm

theorem qTarget_primePower_threshold_tendsto (p q k : ℕ)
    (hp : 1 < p) (hq : q.Prime) :
    Filter.Tendsto (fun K => ∑ j ∈ Finset.range K, primePowerThresholdTerm p q k j)
      Filter.atTop (nhds (inner ℝ (qTarget p hp)
        (normalizedDivisorWavelet ⟨q ^ (k + 1), pow_pos hq.pos _⟩))) := by
  rw [← (qTarget_primePower_threshold_hasSum p q k hp hq).tsum_eq]
  exact (qTarget_primePower_threshold_hasSum p q k hp hq).summable.tendsto_sum_tsum_nat

end RiemannResearch.RH.PrimePowerTarget
