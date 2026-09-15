/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.DilationWaveletAlgebra
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.Analysis.PeriodicHarmonicMean

/-!
# Full signed covariance of adjacent digit dilations

Source: independently derived continuation of Christian Noack's ordinary
dilation-block research, 15 September 2026. The moved-interval argument
extends the existing binary-wavelet calculation to mixed digit seeds.
Every identity includes the entire infinite Pareto tail. The arithmetic
covariance does not assert a lower bound for residual-source correlations.
-/

namespace RiemannResearch.RH.Pareto.AdjacentDigit
open scoped BigOperators
open Filter
noncomputable section

def difference (p m n : ℕ) : ℝ :=
  digitSequence p m n - digitSequence p (m+1) n

def jump (p j : ℕ) : ℝ := digitSequence p 1 j - digitSequence p 1 (j-1)

def covarianceTerm (p q m n : ℕ) : ℝ :=
  positiveWeight n * (difference p m n * difference q m n)

def covariance (p q m : ℕ) : ℝ := ∑' n, covarianceTerm p q m n

def harmonicCovariance (p q m : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 m, jump p j * jump q j / (j : ℝ)

def tailTerm (p q m n : ℕ) : ℝ :=
  if m*(m+1) ≤ n then covarianceTerm p q m n else 0

private def jumpMask (p q m j n : ℕ) : ℝ :=
  if n ∈ Finset.Ico (m*j) ((m+1)*j) then
    positiveWeight n * (jump p j * jump q j) else 0

theorem difference_abs_le (p m n : ℕ) (hp : 0 < p) :
    |difference p m n| ≤ p := by
  have h1 : 0 ≤ digitSequence p m n := Nat.cast_nonneg _
  have h2 : 0 ≤ digitSequence p (m+1) n := Nat.cast_nonneg _
  have h3 := digitSequence_abs_le p m hp n
  have h4 := digitSequence_abs_le p (m+1) hp n
  rw [abs_of_nonneg h1] at h3
  rw [abs_of_nonneg h2] at h4
  exact abs_le.mpr ⟨by unfold difference; linarith, by unfold difference; linarith⟩

private theorem interval_quotients (m j n : ℕ) (_hm : 0 < m)
    (hj : 0 < j) (hjm : j ≤ m)
    (hn : n ∈ Finset.Ico (m * j) ((m + 1) * j)) :
    n/m = j ∧ n/(m+1) = j-1 := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hn
  constructor
  · apply Nat.div_eq_of_lt_le <;> nlinarith
  · apply Nat.div_eq_of_lt_le
    · have he : j-1+1 = j := by omega
      have hh : (m+1)*(j-1) ≤ m*j := by nlinarith
      exact (by simpa only [Nat.mul_comm] using hh.trans hlo)
    · have he : j-1+1 = j := by omega
      simpa only [he, Nat.mul_comm] using hhi

private theorem mismatch_interval (m n : ℕ) (hm : 0 < m)
    (ht : n < m * (m + 1)) (hne : n / m ≠ n / (m + 1)) :
    ∃ j ∈ Finset.Icc 1 m, n ∈ Finset.Ico (m*j) ((m+1)*j) := by
  have hmod := Nat.div_add_mod n m
  have hmodlt := Nat.mod_lt n hm
  have hnew := Nat.div_add_mod n (m+1)
  have hnewlt := Nat.mod_lt n (Nat.succ_pos m)
  have holdlo : m*(n/m) ≤ n := by omega
  have hnewlo : (m+1)*(n/(m+1)) ≤ n := by omega
  have holdhi : n < m*(n/m+1) := by nlinarith only [hmod, hmodlt]
  have hnewhi : n < (m+1)*(n/(m+1)+1) := by
    change n % (m+1) < m+1 at hnewlt
    nlinarith only [hnew, hnewlt]
  have hjm : n/m ≤ m := by
    by_contra h
    have h' : m+1 ≤ n/m := by omega
    have hh := Nat.mul_le_mul_left m h'
    omega
  have hle : n/(m+1) ≤ n/m := by
    by_contra h
    have h' : n/m+1 ≤ n/(m+1) := by omega
    have hh := Nat.mul_le_mul (Nat.le_succ m) h'
    exact (Nat.not_lt.mpr (hh.trans hnewlo)) holdhi
  have hlt : n/(m+1) < n/m := lt_of_le_of_ne hle (Ne.symm hne)
  refine ⟨n/m, Finset.mem_Icc.mpr
    ⟨Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hlt), hjm⟩, Finset.mem_Ico.mpr ?_⟩
  constructor
  · exact holdlo
  · have h' : n/(m+1)+1 ≤ n/m := by omega
    exact lt_of_lt_of_le hnewhi (Nat.mul_le_mul_left (m+1) h')

private theorem interval_value (p m j n : ℕ) (hm : 0 < m)
    (hj : 0 < j) (hjm : j ≤ m)
    (hn : n ∈ Finset.Ico (m * j) ((m + 1) * j)) :
    difference p m n = jump p j := by
  obtain ⟨h1,h2⟩ := interval_quotients m j n hm hj hjm hn
  simp [difference, jump, digitSequence, h1, h2]

private theorem jumpMask_summable (p q m j : ℕ) : Summable (jumpMask p q m j) := by
  apply summable_of_ne_finset_zero (s := Finset.Ico (m*j) ((m+1)*j))
  intro n hn
  simp [jumpMask, hn]

private theorem jumpMask_tsum (p q m j : ℕ) (hm : 0 < m) (hj : 0 < j) :
    (∑' n, jumpMask p q m j n) =
      (jump p j * jump q j) / ((m:ℝ)*((m:ℝ)+1)*(j:ℝ)) := by
  rw [tsum_eq_sum (s := Finset.Ico (m*j) ((m+1)*j))
    (fun n hn => by simp [jumpMask, hn])]
  have he : (∑ n ∈ Finset.Ico (m*j) ((m+1)*j), jumpMask p q m j n) =
      (∑ n ∈ Finset.Ico (m*j) ((m+1)*j), positiveWeight n) * (jump p j * jump q j) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun n hn => by simp [jumpMask, hn])
  rw [he, positiveWeight_interval _ _ (Nat.mul_pos hm hj)
    (Nat.mul_le_mul_right j (Nat.le_succ m))]
  push_cast
  field_simp
  ring

private theorem tailWeight_summable (K : ℕ) :
    Summable (fun n => if K ≤ n then positiveWeight n else (0:ℝ)) := by
  have h := weighted_summable_of_bounded
    (f := fun n => if K ≤ n then (1:ℝ) else 0) (C := 1)
    (fun n => by split_ifs <;> norm_num)
  simpa only [mul_ite, mul_one, mul_zero] using h

private theorem tailWeight_tsum (K : ℕ) (hK : 0 < K) :
    (∑' n, if K ≤ n then positiveWeight n else (0:ℝ)) = 1/(K:ℝ) := by
  have hs : Summable (fun n => if n < K then positiveWeight n else (0:ℝ)) := by
    apply summable_of_ne_finset_zero (s := Finset.range K)
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    simp [Nat.not_lt.mpr hn]
  have he : (fun n => (if n < K then positiveWeight n else (0:ℝ)) +
      (if K ≤ n then positiveWeight n else 0)) = positiveWeight := by
    funext n
    by_cases hn : n < K
    · simp [hn, Nat.not_le.mpr hn]
    · simp [hn, Nat.le_of_not_gt hn]
  have hsum := hs.tsum_add (tailWeight_summable K)
  rw [he, positiveWeight_tsum] at hsum
  have hh : (∑' n, if n < K then positiveWeight n else (0:ℝ)) = 1-1/(K:ℝ) := by
    rw [tsum_eq_sum (s := Finset.range K)
      (fun n hn => by simp only [Finset.mem_range] at hn; simp [hn])]
    have hprefix : (∑ n ∈ Finset.range K, if n < K then positiveWeight n else (0:ℝ)) =
        ∑ n ∈ Finset.range K, positiveWeight n :=
      Finset.sum_congr rfl (fun n hn => if_pos (Finset.mem_range.mp hn))
    rw [hprefix, Finset.sum_range_eq_add_Ico positiveWeight hK,
      positiveWeight_interval 1 K (by omega) hK]
    norm_num [positiveWeight]
  rw [hh] at hsum
  linarith

theorem covariance_summable (p q m : ℕ) (hp : 0 < p) (hq : 0 < q) :
    Summable (covarianceTerm p q m) := by
  exact weighted_summable_of_bounded
    (bounded_product (fun n => difference_abs_le p m n hp)
      (fun n => difference_abs_le q m n hq))

theorem tail_summable (p q m : ℕ) (hp : 0 < p) (hq : 0 < q) :
    Summable (tailTerm p q m) := by
  change Summable (fun n => if m*(m+1) ≤ n then
    positiveWeight n * (difference p m n * difference q m n) else 0)
  have h := weighted_summable_of_bounded
    (f := fun n => if m*(m+1) ≤ n then difference p m n * difference q m n else 0)
    (C := (p:ℝ)*q) (fun n => by
      split_ifs
      · exact bounded_product (fun n => difference_abs_le p m n hp)
          (fun n => difference_abs_le q m n hq) n
      · simp only [abs_zero]; positivity)
  simpa only [mul_ite, mul_zero] using h

private theorem pointwise_head_tail (p q m n : ℕ) (hm : 0 < m) :
    covarianceTerm p q m n =
      (∑ j ∈ Finset.Icc 1 m, jumpMask p q m j n) + tailTerm p q m n := by
  classical
  by_cases ht : m*(m+1) ≤ n
  · have hz : (∑ j ∈ Finset.Icc 1 m, jumpMask p q m j n) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjm := (Finset.mem_Icc.mp hj).2
      have hn : n ∉ Finset.Ico (m*j) ((m+1)*j) := by
        simp only [Finset.mem_Ico, not_and]
        intro _
        nlinarith
      simp [jumpMask, hn]
    simp [hz, tailTerm, ht]
  · rw [show tailTerm p q m n = 0 by simp [tailTerm, ht], add_zero]
    by_cases he : n/m = n/(m+1)
    · have hz : covarianceTerm p q m n = 0 := by
        simp [covarianceTerm, difference, digitSequence, he]
      rw [hz]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      have hn : n ∉ Finset.Ico (m*j) ((m+1)*j) := by
        intro hn
        obtain ⟨h1,h2⟩ := interval_quotients m j n hm
          (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 hn
        have hjpos := (Finset.mem_Icc.mp hj).1
        omega
      simp [jumpMask, hn]
    · obtain ⟨j,hj,hn⟩ := mismatch_interval m n hm (Nat.lt_of_not_ge ht) he
      rw [Finset.sum_eq_single j]
      · rw [show jumpMask p q m j n =
            positiveWeight n * (jump p j * jump q j) by simp [jumpMask, hn]]
        unfold covarianceTerm
        rw [interval_value p m j n hm (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 hn,
          interval_value q m j n hm (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 hn]
      · intro i hi hij
        have hni : n ∉ Finset.Ico (m*i) ((m+1)*i) := by
          intro hni
          have hqi := (interval_quotients m i n hm (Finset.mem_Icc.mp hi).1
            (Finset.mem_Icc.mp hi).2 hni).1
          have hqj := (interval_quotients m j n hm (Finset.mem_Icc.mp hj).1
            (Finset.mem_Icc.mp hj).2 hn).1
          exact hij (hqi.symm.trans hqj)
        simp [jumpMask, hni]
      · exact fun h => (h hj).elim

/-- Exact mixed covariance with the full, possibly signed infinite tail. -/
theorem exact_head_tail (p q m : ℕ) (hp : 0 < p) (hq : 0 < q) (hm : 0 < m) :
    covariance p q m = harmonicCovariance p q m / ((m:ℝ)*((m:ℝ)+1)) +
      ∑' n, tailTerm p q m n := by
  have hhead : Summable (fun n => ∑ j ∈ Finset.Icc 1 m, jumpMask p q m j n) :=
    summable_sum (fun j _ => jumpMask_summable p q m j)
  calc
    _ = ∑' n, ((∑ j ∈ Finset.Icc 1 m, jumpMask p q m j n) + tailTerm p q m n) := by
      unfold covariance
      congr 1
      funext n
      exact pointwise_head_tail p q m n hm
    _ = (∑ j ∈ Finset.Icc 1 m, (jump p j * jump q j) /
          ((m:ℝ)*((m:ℝ)+1)*(j:ℝ))) + ∑' n, tailTerm p q m n := by
      rw [hhead.tsum_add (tail_summable p q m hp hq),
        Summable.tsum_finsetSum (fun j hj => jumpMask_summable p q m j)]
      congr 1
      exact Finset.sum_congr rfl (fun j hj => jumpMask_tsum p q m j hm
        (Finset.mem_Icc.mp hj).1)
    _ = _ := by
      congr 1
      unfold harmonicCovariance
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun j hj => by field_simp)

/-- The entire scaled infinite tail is uniformly bounded, including mixed signs. -/
theorem tail_bound (p q m : ℕ) (hp : 0 < p) (hq : 0 < q) (hm : 0 < m) :
    |∑' n, tailTerm p q m n| ≤ (p:ℝ)*q / ((m:ℝ)*((m:ℝ)+1)) := by
  have hb (n : ℕ) : |tailTerm p q m n| ≤
      (p:ℝ)*q * (if m*(m+1) ≤ n then positiveWeight n else 0) := by
    unfold tailTerm covarianceTerm
    split_ifs
    · rw [abs_mul, abs_of_nonneg (positiveWeight_nonneg n), abs_mul]
      have hd := mul_le_mul (difference_abs_le p m n hp) (difference_abs_le q m n hq)
        (abs_nonneg _) (Nat.cast_nonneg _)
      simpa only [mul_comm (positiveWeight n)] using
        mul_le_mul_of_nonneg_left hd (positiveWeight_nonneg n)
    · simp
  have hsum := (tail_summable p q m hp hq).abs.tsum_le_tsum hb
    ((tailWeight_summable (m*(m+1))).mul_left ((p:ℝ)*q))
  have ht : |∑' n, tailTerm p q m n| ≤ ∑' n, |tailTerm p q m n| := by
    have hs := tail_summable p q m hp hq
    have hpos := hs.tsum_le_tsum (fun n => le_abs_self (tailTerm p q m n)) hs.abs
    have hneg := hs.neg.tsum_le_tsum (fun n => neg_le_abs (tailTerm p q m n)) hs.abs
    rw [tsum_neg] at hneg
    exact abs_le.mpr ⟨by linarith, hpos⟩
  apply ht.trans
  calc
    _ ≤ ∑' n, (p:ℝ)*q * (if m*(m+1) ≤ n then positiveWeight n else 0) := hsum
    _ = _ := by
      rw [tsum_mul_left, tailWeight_tsum _ (by positivity)]
      push_cast
      ring

/-- Complete covariance differs from its finite harmonic term by a bounded amount. -/
theorem scaled_covariance_error (p q m : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hm : 0 < m) :
    |(m:ℝ)*((m:ℝ)+1)*covariance p q m - harmonicCovariance p q m| ≤ (p:ℝ)*q := by
  rw [exact_head_tail p q m hp hq hm]
  have hden : (m:ℝ)*((m:ℝ)+1) ≠ 0 := by positivity
  have he : (m:ℝ)*((m:ℝ)+1) *
      (harmonicCovariance p q m / ((m:ℝ)*((m:ℝ)+1)) + ∑' n, tailTerm p q m n) -
      harmonicCovariance p q m =
      (m:ℝ)*((m:ℝ)+1) * ∑' n, tailTerm p q m n := by field_simp; ring
  rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (m:ℝ)*((m:ℝ)+1))]
  have h := mul_le_mul_of_nonneg_left (tail_bound p q m hp hq hm)
    (by positivity : 0 ≤ (m:ℝ)*((m:ℝ)+1))
  have hr : (m:ℝ)*((m:ℝ)+1) * ((p:ℝ)*q / ((m:ℝ)*((m:ℝ)+1))) = (p:ℝ)*q := by
    field_simp
  exact hr ▸ h

private theorem jump_two (k : ℕ) : jump 2 (k+1) = if k % 2 = 0 then 1 else -1 := by
  have hk := Nat.mod_lt k (by omega : 0 < 2)
  interval_cases h : k % 2 <;> simp [jump, digitSequence, Nat.add_mod, h]

private theorem jump_three (k : ℕ) : jump 3 (k+1) = if k % 3 = 2 then -2 else 1 := by
  have hk := Nat.mod_lt k (by omega : 0 < 3)
  interval_cases h : k % 3 <;> norm_num [jump, digitSequence, Nat.add_mod, h]

private theorem jump_two_period (k : ℕ) : jump 2 (k+6+1) = jump 2 (k+1) := by
  simp [jump_two, Nat.add_mod]

private theorem jump_three_period (k : ℕ) : jump 3 (k+6+1) = jump 3 (k+1) := by
  simp [jump_three, Nat.add_mod]

private theorem jump_two_abs (k : ℕ) : |jump 2 (k+1)| ≤ 1 := by
  rw [jump_two]
  split_ifs <;> norm_num

private theorem jump_three_abs (k : ℕ) : |jump 3 (k+1)| ≤ 2 := by
  rw [jump_three]
  split_ifs <;> norm_num

private theorem harmonicCovariance_range (p q m : ℕ) :
    harmonicCovariance p q m =
      ∑ k ∈ Finset.range m, (jump p (k+1) * jump q (k+1)) / ((k:ℝ)+1) := by
  unfold harmonicCovariance
  rw [show Finset.Icc 1 m = Finset.Ico 1 (m+1) by ext j; simp,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right, Nat.add_comm 1]
  push_cast
  rfl

/-- Period six gives the binary diagonal mean one. -/
theorem binary_jump_mean :
    RiemannResearch.Analysis.periodicMean (fun k => jump 2 (k+1) * jump 2 (k+1)) 6 = 1 := by
  norm_num [RiemannResearch.Analysis.periodicMean, Finset.sum_range_succ, jump_two]

/-- Period six gives the ternary diagonal mean two. -/
theorem ternary_jump_mean :
    RiemannResearch.Analysis.periodicMean (fun k => jump 3 (k+1) * jump 3 (k+1)) 6 = 2 := by
  norm_num [RiemannResearch.Analysis.periodicMean, Finset.sum_range_succ, jump_three]

/-- The signed mixed period mean is exactly zero. -/
theorem mixed_jump_mean :
    RiemannResearch.Analysis.periodicMean (fun k => jump 2 (k+1) * jump 3 (k+1)) 6 = 0 := by
  norm_num [RiemannResearch.Analysis.periodicMean, Finset.sum_range_succ, jump_two, jump_three]

theorem binary_covariance_harmonic_error (m : ℕ) (hm : 0 < m) :
    |(m:ℝ)*((m:ℝ)+1)*covariance 2 2 m - (harmonic m:ℝ)| ≤ 28 := by
  have h := RiemannResearch.Analysis.periodic_harmonic_mean_error_bound
    (fun k => jump 2 (k+1)*jump 2 (k+1)) 6 (by omega)
    (fun k => by rw [jump_two_period]) 1
    (fun k => by simpa using bounded_product jump_two_abs jump_two_abs k) m
  rw [binary_jump_mean, ← harmonicCovariance_range] at h
  norm_num at h
  have ht := scaled_covariance_error 2 2 m (by omega) (by omega) hm
  have ha := abs_add_le
    ((m:ℝ)*((m:ℝ)+1)*covariance 2 2 m - harmonicCovariance 2 2 m)
    (harmonicCovariance 2 2 m - (harmonic m:ℝ))
  simp only [sub_add_sub_cancel] at ha
  norm_num at ht
  linarith

theorem ternary_covariance_harmonic_error (m : ℕ) (hm : 0 < m) :
    |(m:ℝ)*((m:ℝ)+1)*covariance 3 3 m - 2*(harmonic m:ℝ)| ≤ 81 := by
  have h := RiemannResearch.Analysis.periodic_harmonic_mean_error_bound
    (fun k => jump 3 (k+1)*jump 3 (k+1)) 6 (by omega)
    (fun k => by rw [jump_three_period]) 4
    (fun k => by simpa only [show (2:ℝ)*2 = 4 by norm_num] using
      bounded_product jump_three_abs jump_three_abs k) m
  rw [ternary_jump_mean, ← harmonicCovariance_range] at h
  norm_num at h
  have ht := scaled_covariance_error 3 3 m (by omega) (by omega) hm
  have ha := abs_add_le
    ((m:ℝ)*((m:ℝ)+1)*covariance 3 3 m - harmonicCovariance 3 3 m)
    (harmonicCovariance 3 3 m - 2*(harmonic m:ℝ))
  simp only [sub_add_sub_cancel] at ha
  norm_num at ht
  linarith

theorem mixed_scaled_covariance_bound (m : ℕ) (hm : 0 < m) :
    |(m:ℝ)*((m:ℝ)+1)*covariance 2 3 m| ≤ 30 := by
  have h := RiemannResearch.Analysis.periodic_harmonic_mean_error_bound
    (fun k => jump 2 (k+1)*jump 3 (k+1)) 6 (by omega)
    (fun k => by rw [jump_two_period, jump_three_period]) 2
    (fun k => by simpa using bounded_product jump_two_abs jump_three_abs k) m
  rw [mixed_jump_mean, ← harmonicCovariance_range] at h
  norm_num at h
  have ht := scaled_covariance_error 2 3 m (by omega) (by omega) hm
  have ha := abs_add_le
    ((m:ℝ)*((m:ℝ)+1)*covariance 2 3 m - harmonicCovariance 2 3 m)
    (harmonicCovariance 2 3 m)
  simp only [sub_add_cancel] at ha
  norm_num at ht
  linarith

/-- Full binary covariance, with all tail terms, has logarithmic coefficient one. -/
theorem binary_covariance_log_limit :
    Tendsto (fun m : ℕ => ((m:ℝ)*((m:ℝ)+1)*covariance 2 2 m) / Real.log m)
      atTop (nhds 1) := by
  have he := RiemannResearch.Analysis.bounded_error_div_log_tendsto_zero
    (fun m => (m:ℝ)*((m:ℝ)+1)*covariance 2 2 m - (harmonic m:ℝ)) 28
    binary_covariance_harmonic_error
  have h := he.add RiemannResearch.Analysis.harmonic_div_log_tendsto_one
  simp only [zero_add] at h
  convert h using 1
  ext m
  ring

/-- Full ternary covariance has logarithmic coefficient two. -/
theorem ternary_covariance_log_limit :
    Tendsto (fun m : ℕ => ((m:ℝ)*((m:ℝ)+1)*covariance 3 3 m) / Real.log m)
      atTop (nhds 2) := by
  have he := RiemannResearch.Analysis.bounded_error_div_log_tendsto_zero
    (fun m => (m:ℝ)*((m:ℝ)+1)*covariance 3 3 m - 2*(harmonic m:ℝ)) 81
    ternary_covariance_harmonic_error
  have h := he.add (RiemannResearch.Analysis.harmonic_div_log_tendsto_one.const_mul 2)
  simp only [zero_add, mul_one] at h
  convert h using 1
  ext m
  ring

/-- The full mixed covariance has zero logarithmic coefficient. -/
theorem mixed_covariance_log_limit :
    Tendsto (fun m : ℕ => ((m:ℝ)*((m:ℝ)+1)*covariance 2 3 m) / Real.log m)
      atTop (nhds 0) :=
  RiemannResearch.Analysis.bounded_error_div_log_tendsto_zero _ 30
    mixed_scaled_covariance_bound

/-- The infinite arithmetic sum is exactly the actual Hilbert inner product. -/
theorem covariance_eq_inner (p q m : ℕ) (hp : 0 < p) (hq : 0 < q) (hm : 0 < m) :
    covariance p q m = inner ℝ
      (digitHilbert p m hp hm - digitHilbert p (m+1) hp (by omega))
      (digitHilbert q m hq hm - digitHilbert q (m+1) hq (by omega)) := by
  rw [hilbert_inner_weighted]
  have hv (a : ℕ) (ha : 0 < a) : hilbertSequence
      (digitHilbert a m ha hm - digitHilbert a (m+1) ha (by omega)) = difference a m := by
    change hilbertSequenceLinear (_-_) = _
    rw [map_sub]
    change hilbertSequence _ - hilbertSequence _ = _
    rw [hilbertSequence_digitHilbert, hilbertSequence_digitHilbert]
    rfl
  rw [hv p hp, hv q hq]
  rfl

end
end RiemannResearch.RH.Pareto.AdjacentDigit
