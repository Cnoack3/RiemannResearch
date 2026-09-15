/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.AdjacentDigitCovariance

/-!
# Cross-index adjacent digit overlap, including the complete signed tail

Source: independently derived arithmetic proof in the resonance-cell
continuation, 15 September 2026. The finite overlap formula applies to arbitrary
positive dilation indices. The resonance geometry identifies every simultaneous
jump below a quadratic cutoff for the six binary/ternary offset pairs.
-/

namespace RiemannResearch.RH.Pareto.AdjacentDigit
open scoped BigOperators
noncomputable section

/-- The full cross-index summand, with its original sign. -/
def crossTerm (p q m l n : ℕ) : ℝ :=
  positiveWeight n * (difference p m n * difference q l n)

def crossCovariance (p q m l : ℕ) : ℝ := ∑' n, crossTerm p q m l n

def crossTail (p q m l K n : ℕ) : ℝ :=
  if K ≤ n then crossTerm p q m l n else 0

def intervalMask (p m j n : ℕ) : ℝ :=
  if n ∈ Finset.Ico (m*j) ((m+1)*j) then jump p j else 0

/-- The two jump intervals intersected with the initial cutoff. -/
def overlapInterval (m l K j i : ℕ) : Finset ℕ :=
  Finset.Ico (max (m*j) (l*i)) (min ((m+1)*j) (min ((l+1)*i) K))

def overlapMask (p q m l K j i n : ℕ) : ℝ :=
  if n ∈ overlapInterval m l K j i then
    positiveWeight n * (jump p j * jump q i) else 0

/-- Reciprocal interval mass; for positive lower endpoints this is the Pareto mass.
Empty overlaps contribute zero. -/
def overlapMass (m l K j i : ℕ) : ℝ :=
  let L := max (m*j) (l*i)
  let U := min ((m+1)*j) (min ((l+1)*i) K)
  if L < U then 1/(L:ℝ) - 1/(U:ℝ) else 0

theorem difference_eq_intervals (p m n : ℕ) (hm : 0 < m)
    (hn : n < m*(m+1)) :
    difference p m n = ∑ j ∈ Finset.Icc 1 m, intervalMask p m j n := by
  classical
  by_cases he : n/m = n/(m+1)
  · have hz : difference p m n = 0 := by simp [difference, digitSequence, he]
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    have hnot : n ∉ Finset.Ico (m*j) ((m+1)*j) := by
      intro hmem
      obtain ⟨h1,h2⟩ := interval_quotients m j n hm
        (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 hmem
      have hjpos := (Finset.mem_Icc.mp hj).1
      omega
    simp [intervalMask, hnot]
  · obtain ⟨j,hj,hmem⟩ := mismatch_interval m n hm hn he
    rw [Finset.sum_eq_single j]
    · simpa [intervalMask, hmem] using interval_value p m j n hm
        (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 hmem
    · intro i hi hij
      have hnot : n ∉ Finset.Ico (m*i) ((m+1)*i) := by
        intro hmemi
        have hqi := (interval_quotients m i n hm (Finset.mem_Icc.mp hi).1
          (Finset.mem_Icc.mp hi).2 hmemi).1
        have hqj := (interval_quotients m j n hm (Finset.mem_Icc.mp hj).1
          (Finset.mem_Icc.mp hj).2 hmem).1
        exact hij (hqi.symm.trans hqj)
      simp [intervalMask, hnot]
    · exact fun h => (h hj).elim

theorem cross_summable (p q m l : ℕ) (hp : 0 < p) (hq : 0 < q) :
    Summable (crossTerm p q m l) := by
  exact weighted_summable_of_bounded
    (bounded_product (fun n => difference_abs_le p m n hp)
      (fun n => difference_abs_le q l n hq))

theorem crossTail_summable (p q m l K : ℕ) (hp : 0 < p) (hq : 0 < q) :
    Summable (crossTail p q m l K) := by
  change Summable (fun n => if K ≤ n then
    positiveWeight n * (difference p m n * difference q l n) else 0)
  have h := weighted_summable_of_bounded
    (f := fun n => if K ≤ n then difference p m n * difference q l n else 0)
    (C := (p:ℝ)*q) (fun n => by
      split_ifs
      · exact bounded_product (fun n => difference_abs_le p m n hp)
          (fun n => difference_abs_le q l n hq) n
      · simp only [abs_zero]; positivity)
  simpa only [mul_ite, mul_zero] using h

theorem overlapMask_summable (p q m l K j i : ℕ) :
    Summable (overlapMask p q m l K j i) := by
  apply summable_of_ne_finset_zero (s := overlapInterval m l K j i)
  intro n hn
  simp [overlapMask, hn]

theorem overlapMask_tsum (p q m l K j i : ℕ) (hm : 0 < m) (hj : 0 < j) :
    (∑' n, overlapMask p q m l K j i n) =
      (jump p j * jump q i) * overlapMass m l K j i := by
  classical
  let L := max (m*j) (l*i)
  let U := min ((m+1)*j) (min ((l+1)*i) K)
  have hL : 0 < L := lt_of_lt_of_le (Nat.mul_pos hm hj) (le_max_left _ _)
  rw [tsum_eq_sum (s := overlapInterval m l K j i)
    (fun n hn => by simp [overlapMask, hn])]
  have he : (∑ n ∈ overlapInterval m l K j i, overlapMask p q m l K j i n) =
      (∑ n ∈ Finset.Ico L U, positiveWeight n) * (jump p j * jump q i) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun n hn => by
      have hn' : n ∈ overlapInterval m l K j i := hn
      simp [overlapMask, hn'])
  rw [he]
  by_cases hLU : L < U
  · have hmass : overlapMass m l K j i = 1/(L:ℝ) - 1/(U:ℝ) := if_pos hLU
    rw [hmass, positiveWeight_interval L U hL (Nat.le_of_lt hLU)]
    ring
  · have hempty : Finset.Ico L U = ∅ :=
      Finset.Ico_eq_empty_of_le (Nat.le_of_not_gt hLU)
    have hmass : overlapMass m l K j i = 0 := if_neg hLU
    simp [hempty, hmass]

/-- Every finite jump intersection is retained before the full infinite tail. -/
theorem cross_pointwise_head_tail (p q m l K n : ℕ) (hm : 0 < m) (hl : 0 < l)
    (hKm : K ≤ m*(m+1)) (hKl : K ≤ l*(l+1)) :
    crossTerm p q m l n =
      (∑ j ∈ Finset.Icc 1 m, ∑ i ∈ Finset.Icc 1 l,
        overlapMask p q m l K j i n) + crossTail p q m l K n := by
  classical
  by_cases hn : n < K
  · have htail : crossTail p q m l K n = 0 := by
      simp [crossTail, Nat.not_le.mpr hn]
    rw [htail, add_zero]
    unfold crossTerm
    rw [difference_eq_intervals p m n hm (lt_of_lt_of_le hn hKm),
      difference_eq_intervals q l n hl (lt_of_lt_of_le hn hKl)]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    unfold intervalMask overlapMask overlapInterval
    simp only [Finset.mem_Ico, max_le_iff, lt_min_iff]
    split_ifs <;> simp_all
  · have htail : crossTail p q m l K n = crossTerm p q m l n := by
      simp [crossTail, Nat.le_of_not_gt hn]
    rw [htail]
    have hhead : (∑ j ∈ Finset.Icc 1 m, ∑ i ∈ Finset.Icc 1 l,
        overlapMask p q m l K j i n) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      apply Finset.sum_eq_zero
      intro i hi
      have hnot : n ∉ overlapInterval m l K j i := by
        simp only [overlapInterval, Finset.mem_Ico, lt_min_iff]
        omega
      simp [overlapMask, hnot]
    simp [hhead]

/-- Exact arbitrary-index overlap formula with its complete signed tail. -/
theorem cross_exact_head_tail (p q m l K : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hm : 0 < m) (hl : 0 < l) (hKm : K ≤ m*(m+1)) (hKl : K ≤ l*(l+1)) :
    crossCovariance p q m l =
      (∑ j ∈ Finset.Icc 1 m, ∑ i ∈ Finset.Icc 1 l,
        (jump p j * jump q i) * overlapMass m l K j i) +
      ∑' n, crossTail p q m l K n := by
  have hh : Summable (fun n => ∑ j ∈ Finset.Icc 1 m, ∑ i ∈ Finset.Icc 1 l,
      overlapMask p q m l K j i n) :=
    summable_sum (fun j _ => summable_sum (fun i _ => overlapMask_summable p q m l K j i))
  unfold crossCovariance
  have he : (fun n => crossTerm p q m l n) =
      fun n => (∑ j ∈ Finset.Icc 1 m, ∑ i ∈ Finset.Icc 1 l,
        overlapMask p q m l K j i n) + crossTail p q m l K n := by
    funext n
    exact cross_pointwise_head_tail p q m l K n hm hl hKm hKl
  rw [he, hh.tsum_add (crossTail_summable p q m l K hp hq)]
  congr 1
  rw [Summable.tsum_finsetSum
    (fun j _ => summable_sum (fun i _ => overlapMask_summable p q m l K j i))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Summable.tsum_finsetSum (fun i _ => overlapMask_summable p q m l K j i)]
  exact Finset.sum_congr rfl (fun i hi => overlapMask_tsum p q m l K j i hm
    (Finset.mem_Icc.mp hj).1)

/-- Uniform absolute control is applied only after the exact signed tail identity. -/
theorem cross_tail_bound (p q m l K : ℕ) (hp : 0 < p) (hq : 0 < q) (hK : 0 < K) :
    |∑' n, crossTail p q m l K n| ≤ (p:ℝ)*q / (K:ℝ) := by
  have hb (n : ℕ) : |crossTail p q m l K n| ≤
      (p:ℝ)*q * (if K ≤ n then positiveWeight n else 0) := by
    unfold crossTail crossTerm
    split_ifs
    · rw [abs_mul, abs_of_nonneg (positiveWeight_nonneg n), abs_mul]
      have hd := mul_le_mul (difference_abs_le p m n hp) (difference_abs_le q l n hq)
        (abs_nonneg _) (Nat.cast_nonneg _)
      simpa only [mul_comm (positiveWeight n)] using
        mul_le_mul_of_nonneg_left hd (positiveWeight_nonneg n)
    · simp
  have hsum := (crossTail_summable p q m l K hp hq).abs.tsum_le_tsum hb
    ((tailWeight_summable K).mul_left ((p:ℝ)*q))
  have ht : |∑' n, crossTail p q m l K n| ≤ ∑' n, |crossTail p q m l K n| := by
    have hs := crossTail_summable p q m l K hp hq
    have hpos := hs.tsum_le_tsum (fun n => le_abs_self (crossTail p q m l K n)) hs.abs
    have hneg := hs.neg.tsum_le_tsum (fun n => neg_le_abs (crossTail p q m l K n)) hs.abs
    rw [tsum_neg] at hneg
    exact abs_le.mpr ⟨by linarith, hpos⟩
  apply ht.trans
  calc
    _ ≤ ∑' n, (p:ℝ)*q * (if K ≤ n then positiveWeight n else 0) := hsum
    _ = _ := by rw [tsum_mul_left, tailWeight_tsum K hK]; ring

/-- The arithmetic covariance is the actual Hilbert inner product at both indices. -/
theorem crossCovariance_eq_inner (p q m l : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hm : 0 < m) (hl : 0 < l) :
    crossCovariance p q m l = inner ℝ
      (digitHilbert p m hp hm - digitHilbert p (m+1) hp (by omega))
      (digitHilbert q l hq hl - digitHilbert q (l+1) hq (by omega)) := by
  rw [hilbert_inner_weighted]
  have hv (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : hilbertSequence
      (digitHilbert a b ha hb - digitHilbert a (b+1) ha (by omega)) = difference a b := by
    change hilbertSequenceLinear (_-_) = _
    rw [map_sub]
    change hilbertSequence _ - hilbertSequence _ = _
    rw [hilbertSequence_digitHilbert, hilbertSequence_digitHilbert]
    rfl
  rw [hv p m hp hm, hv q l hq hl]
  rfl

/-- Short intersecting shifted intervals have the same unshifted start. -/
theorem aligned_of_short_intersection (a b k r s j i n : ℕ)
    (hj : (r+1)*j ≤ k) (hi : (s+1)*i ≤ k)
    (hnj : n ∈ Finset.Ico ((a*k+r)*j) ((a*k+r+1)*j))
    (hni : n ∈ Finset.Ico ((b*k+s)*i) ((b*k+s+1)*i)) :
    a*j = b*i := by
  obtain ⟨hjlo,hjhi⟩ := Finset.mem_Ico.mp hnj
  obtain ⟨hilo,hihi⟩ := Finset.mem_Ico.mp hni
  rcases lt_trichotomy (a*j) (b*i) with hlt | heq | hgt
  · have hm := Nat.mul_le_mul_left k (show a*j+1 ≤ b*i by omega)
    nlinarith
  · exact heq
  · have hm := Nat.mul_le_mul_left k (show b*i+1 ≤ a*j by omega)
    nlinarith

/-- For the six offset pairs, every overlap below `k²` is a true `3:2` resonance. -/
theorem two_three_alignment_below_square (k r s j i n : ℕ) (_hk : 0 < k)
    (hr : r ≤ 2) (hs : s ≤ 1) (hn : n < k*k)
    (hnj : n ∈ Finset.Ico ((3*k+r)*j) ((3*k+r+1)*j))
    (hni : n ∈ Finset.Ico ((2*k+s)*i) ((2*k+s+1)*i)) :
    ∃ t : ℕ, j = 2*t ∧ i = 3*t := by
  have hjlo := (Finset.mem_Ico.mp hnj).1
  have hilo := (Finset.mem_Ico.mp hni).1
  have hj : 3*j < k := by
    by_contra h
    have hm := Nat.mul_le_mul_left k (Nat.le_of_not_gt h)
    nlinarith
  have hi : 2*i < k := by
    by_contra h
    have hm := Nat.mul_le_mul_left k (Nat.le_of_not_gt h)
    nlinarith
  have hjwidth : (r+1)*j ≤ k := by nlinarith
  have hiwidth : (s+1)*i ≤ k := by nlinarith
  have he := aligned_of_short_intersection 3 2 k r s j i n hjwidth hiwidth hnj hni
  exact ⟨j/2, by omega, by omega⟩

/-- Both resonant jumps are negative, so their product has positive sign two. -/
theorem two_three_resonant_jump (t : ℕ) (ht : 0 < t) :
    jump 2 (2*t) * jump 3 (3*t) = 2 := by
  have h2 : 2*t-1 = 2*(t-1)+1 := by omega
  have h3 : 3*t-1 = 3*(t-1)+2 := by omega
  norm_num [jump, digitSequence, h2, h3, Nat.add_mod, Nat.mul_mod]


/-- Distinct offsets from a common scale have no simultaneous low jumps. -/
theorem separated_offsets_product_zero (p q k r s n : ℕ) (hk : 0 < k)
    (hr : r ≤ 2) (hs : s ≤ 2) (hrs : r ≠ s) (hn : 4*n < k*k) :
    difference p (k+r) n * difference q (k+s) n = 0 := by
  by_cases he : n/(k+r) = n/(k+r+1)
  · simp [difference, digitSequence, he]
  by_cases hf : n/(k+s) = n/(k+s+1)
  · simp [difference, digitSequence, hf]
  have hmr : 0 < k+r := by omega
  have hms : 0 < k+s := by omega
  have hnr : n < (k+r)*(k+r+1) := by nlinarith
  have hns : n < (k+s)*(k+s+1) := by nlinarith
  obtain ⟨j,hj,hnj⟩ := mismatch_interval (k+r) n hmr hnr he
  obtain ⟨i,hi,hni⟩ := mismatch_interval (k+s) n hms hns hf
  have hjlo := (Finset.mem_Ico.mp hnj).1
  have hilo := (Finset.mem_Ico.mp hni).1
  have hjwidth : (r+1)*j ≤ k := by
    have hjk : 4*j < k := by
      by_contra h
      have hm := Nat.mul_le_mul_left k (Nat.le_of_not_gt h)
      nlinarith
    nlinarith
  have hiwidth : (s+1)*i ≤ k := by
    have hik : 4*i < k := by
      by_contra h
      have hm := Nat.mul_le_mul_left k (Nat.le_of_not_gt h)
      nlinarith
    nlinarith
  have hji : j = i := by
    simpa only [one_mul] using aligned_of_short_intersection 1 1 k r s j i n
      hjwidth hiwidth (by simpa only [one_mul] using hnj)
      (by simpa only [one_mul] using hni)
  subst i
  obtain ⟨hjlo,hjhi⟩ := Finset.mem_Ico.mp hnj
  obtain ⟨hilo,hihi⟩ := Finset.mem_Ico.mp hni
  rcases lt_or_gt_of_ne hrs with hlt | hgt
  · have hm := Nat.mul_le_mul_right j (show k+r+1 ≤ k+s by omega)
    omega
  · have hm := Nat.mul_le_mul_right j (show k+s+1 ≤ k+r by omega)
    omega

/-- The full off-offset covariance is exactly its tail beyond the quadratic cutoff. -/
theorem separated_offsets_covariance_tail (p q k r s K : ℕ) (hk : 0 < k)
    (hr : r ≤ 2) (hs : s ≤ 2) (hrs : r ≠ s) (hK : 4*K ≤ k*k) :
    crossCovariance p q (k+r) (k+s) =
      ∑' n, crossTail p q (k+r) (k+s) K n := by
  unfold crossCovariance
  congr 1
  funext n
  by_cases hn : K ≤ n
  · simp [crossTail, hn]
  · have hz := separated_offsets_product_zero p q k r s n hk hr hs hrs
      (by omega : 4*n < k*k)
    simp [crossTail, crossTerm, hn, hz]

/-- Uniform off-offset control includes the entire signed covariance. -/
theorem separated_offsets_covariance_bound (p q k r s K : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hk : 0 < k)
    (hr : r ≤ 2) (hs : s ≤ 2) (hrs : r ≠ s)
    (hKpos : 0 < K) (hK : 4*K ≤ k*k) :
    |crossCovariance p q (k+r) (k+s)| ≤ (p:ℝ)*q / (K:ℝ) := by
  rw [separated_offsets_covariance_tail p q k r s K hk hr hs hrs hK]
  exact cross_tail_bound p q (k+r) (k+s) K hp hq hKpos


/-- The two empty entries in the binary/ternary overlap matrix have zero head. -/
theorem separated_two_three_product_zero (p q k r s n : ℕ) (hk : 0 < k)
    (hr : r ≤ 2) (hs : s ≤ 1)
    (hsep : 2*(r+1) ≤ 3*s ∨ 3*(s+1) ≤ 2*r) (hn : n < k*k) :
    difference p (3*k+r) n * difference q (2*k+s) n = 0 := by
  by_cases he : n/(3*k+r) = n/(3*k+r+1)
  · simp [difference, digitSequence, he]
  by_cases hf : n/(2*k+s) = n/(2*k+s+1)
  · simp [difference, digitSequence, hf]
  have hmr : 0 < 3*k+r := by omega
  have hms : 0 < 2*k+s := by omega
  have hnr : n < (3*k+r)*(3*k+r+1) := by nlinarith
  have hns : n < (2*k+s)*(2*k+s+1) := by nlinarith
  obtain ⟨j,hj,hnj⟩ := mismatch_interval (3*k+r) n hmr hnr he
  obtain ⟨i,hi,hni⟩ := mismatch_interval (2*k+s) n hms hns hf
  obtain ⟨t,rfl,rfl⟩ := two_three_alignment_below_square k r s j i n hk hr hs hn hnj hni
  obtain ⟨hjlo,hjhi⟩ := Finset.mem_Ico.mp hnj
  obtain ⟨hilo,hihi⟩ := Finset.mem_Ico.mp hni
  rcases hsep with h | h
  · have hm := Nat.mul_le_mul_right t h
    nlinarith
  · have hm := Nat.mul_le_mul_right t h
    nlinarith

/-- The empty geometric entries retain only their entire infinite tail. -/
theorem separated_two_three_covariance_tail (p q k r s K : ℕ) (hk : 0 < k)
    (hr : r ≤ 2) (hs : s ≤ 1)
    (hsep : 2*(r+1) ≤ 3*s ∨ 3*(s+1) ≤ 2*r) (hK : K ≤ k*k) :
    crossCovariance p q (3*k+r) (2*k+s) =
      ∑' n, crossTail p q (3*k+r) (2*k+s) K n := by
  unfold crossCovariance
  congr 1
  funext n
  by_cases hn : K ≤ n
  · simp [crossTail, hn]
  · have hz := separated_two_three_product_zero p q k r s n hk hr hs hsep
      (by omega : n < k*k)
    simp [crossTail, crossTerm, hn, hz]

/-- A complete signed covariance estimate for the two empty cross-seed entries. -/
theorem separated_two_three_covariance_bound (p q k r s K : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hk : 0 < k)
    (hr : r ≤ 2) (hs : s ≤ 1)
    (hsep : 2*(r+1) ≤ 3*s ∨ 3*(s+1) ≤ 2*r)
    (hKpos : 0 < K) (hK : K ≤ k*k) :
    |crossCovariance p q (3*k+r) (2*k+s)| ≤ (p:ℝ)*q / (K:ℝ) := by
  rw [separated_two_three_covariance_tail p q k r s K hk hr hs hsep hK]
  exact cross_tail_bound p q (3*k+r) (2*k+s) K hp hq hKpos

end
end RiemannResearch.RH.Pareto.AdjacentDigit
