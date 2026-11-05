/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoArithmeticRepair
import Mathlib.Data.Nat.Dist
import RiemannResearch.RH.ArithmeticPacketCore
import RiemannResearch.RH.ParetoPacketGreenGram
import RiemannResearch.RH.ArithmeticCumulativeBasic

/-! # All orders of the centered CRT residue interaction

Source: user-proposed all-order carry decomposition. Center the existing integrated
Ramanujan packet in uniform residues and normalize by its conductor. The exact
first difference and physical prefix apply at any conductor greater than one. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

/-- The normalized, uniformly centered primitive-conductor component. -/
def centeredResiduePacket (D n : ℕ) : ℝ :=
  (ramanujanPacket D n - (D.totient : ℝ) / 2) / (D : ℝ)

/-- Divisor inclusion-exclusion on the centered ordinary residue atoms. -/
theorem centeredResiduePacket_divisors (D n : ℕ) (hD : 1 < D) :
    centeredResiduePacket D n = (∑ d ∈ D.divisors,
      (ArithmeticFunction.moebius (D / d) : ℝ) *
        (residue d n - ((d : ℝ) - 1) / 2)) / (D : ℝ) := by
  have ht := packet_moebius_totient_source D hD
  rw [Finset.sum_coe_sort D.divisors (fun d : ℕ =>
    (ArithmeticFunction.moebius (D / d) : ℝ) * ((d : ℝ) - 1))] at ht
  unfold centeredResiduePacket ramanujanPacket
  congr 1
  simp_rw [mul_sub, ← mul_div_assoc, Finset.sum_sub_distrib]
  rw [← Finset.sum_div, ht]

/-- Complete residue inversion in the centered component basis, at every physical site. -/
theorem residueFraction_full_packets (D n : ℕ) (hD : 0 < D) :
    ArithmeticCumulative.residueFraction D n =
      (∑ q ∈ D.divisors.filter (fun q => 1 < q),
        ((q : ℝ) * centeredResiduePacket q n + (q.totient : ℝ) / 2)) / (D : ℝ) := by
  change residue D n / (D : ℝ) = _
  congr 1
  rw [← ramanujanPacket_divisor_sum_gt_one D n hD]
  apply Finset.sum_congr rfl
  intro q hq
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast (show q ≠ 0 by have := (Finset.mem_filter.mp hq).2; omega)
  unfold centeredResiduePacket
  field_simp
  <;> ring

theorem centeredResiduePacket_difference (D n : ℕ) (hD : 1 < D) (hn : 0 < n) :
    centeredResiduePacket D n - centeredResiduePacket D (n - 1) =
      -ramanujanSum D n / (D : ℝ) := by
  unfold centeredResiduePacket
  rw [← sub_div]
  congr 1
  linarith [ramanujanPacket_increment D n hD hn]

/-- The unscaled triangle governing the prefix of a single centered residue. -/
def residuePrefixTriangle (d t : ℕ) : ℝ :=
  ((t % d : ℕ) : ℝ) * ((d : ℝ) - ((t % d : ℕ) : ℝ))

theorem residuePrefixTriangle_step (d k : ℕ) (hd : 0 < d) :
    residuePrefixTriangle d (k + 1) - residuePrefixTriangle d k =
      (d : ℝ) - 1 - 2 * residue d k := by
  by_cases h1 : d = 1
  · subst d
    simp [residuePrefixTriangle, residue, Nat.mod_one]
  have hr := Nat.mod_lt k hd
  have hmod : (k + 1) % d = (k % d + 1) % d := by
    conv_lhs => rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < d)]
  by_cases h : k % d + 1 < d
  · simp only [residuePrefixTriangle, residue, hmod, Nat.mod_eq_of_lt h,
      Nat.cast_add, Nat.cast_one]
    ring
  · have he : k % d + 1 = d := by omega
    have hR : ((k % d : ℕ) : ℝ) + 1 = d := by exact_mod_cast he
    simp only [residuePrefixTriangle, residue, hmod, he, Nat.mod_self, Nat.cast_zero,
      zero_mul, sub_zero]
    rw [← hR]
    ring

private theorem sum_centered_residue (d t : ℕ) (hd : 0 < d) :
    (∑ n ∈ Finset.range t, (residue d n - ((d : ℝ) - 1) / 2)) =
      -residuePrefixTriangle d t / 2 := by
  induction t with
  | zero => simp [residuePrefixTriangle]
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    linarith [residuePrefixTriangle_step d t hd]

/-- Physical prefix through site t − 1, retaining every signed divisor term. -/
theorem centeredResiduePacket_prefix (D t : ℕ) (hD : 1 < D) :
    (∑ n ∈ Finset.range t, centeredResiduePacket D n) =
      -(∑ d ∈ D.divisors, (ArithmeticFunction.moebius (D / d) : ℝ) *
        residuePrefixTriangle d t) / (2 * (D : ℝ)) := by
  simp_rw [centeredResiduePacket_divisors D _ hD]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hsum := Finset.sum_congr (s₁ := D.divisors) (s₂ := D.divisors) rfl
    (fun d hd => congrArg (fun a : ℝ => (ArithmeticFunction.moebius (D / d) : ℝ) * a)
      (sum_centered_residue d t (Nat.pos_of_mem_divisors hd)))
  rw [hsum]
  simp only [← mul_div_assoc, mul_neg, ← Finset.sum_div, Finset.sum_neg_distrib]
  ring

private theorem ramanujan_zero_totient (D : ℕ) (hD : 1 < D) :
    ramanujanSum D 0 = (D.totient : ℝ) := by
  have ht := packet_moebius_totient_source D hD
  rw [Finset.sum_coe_sort D.divisors (fun d : ℕ =>
    (ArithmeticFunction.moebius (D / d) : ℝ) * ((d : ℝ) - 1))] at ht
  simp_rw [mul_sub, mul_one] at ht
  rw [Finset.sum_sub_distrib, sum_moebius_div D hD, sub_zero] at ht
  simpa only [ramanujanSum, dvd_zero, if_true] using ht

private theorem ramanujan_consecutive_row (D t : ℕ) (hD : 1 < D) :
    (∑ i ∈ Finset.range t, ramanujanSum D (Nat.dist i t)) = -ramanujanPacket D t := by
  classical
  rw [ramanujanPacket_prefix D t hD, neg_neg]
  apply Finset.sum_bij (fun i _ => t - i)
  · intro i hi
    have := Finset.mem_range.mp hi
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro i hi j hj hij
    have := Finset.mem_range.mp hi
    have := Finset.mem_range.mp hj
    omega
  · intro k hk
    have := Finset.mem_Ico.mp hk
    exact ⟨t - k, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i hi
    rw [Nat.dist_eq_sub_of_le (Finset.mem_range.mp hi).le]

/-- The physical prefix is the negative of the quadratic form of the
Ramanujan kernel on the indicator of the integer interval, at every order. -/
theorem centeredResiduePacket_prefix_ramanujan_gram (D t : ℕ) (hD : 1 < D) :
    (∑ n ∈ Finset.range t, centeredResiduePacket D n) =
      -(∑ i ∈ Finset.range t, ∑ j ∈ Finset.range t,
        ramanujanSum D (Nat.dist i j)) / (2 * (D : ℝ)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hc := ramanujan_consecutive_row D t hD
    have hr : (∑ j ∈ Finset.range t, ramanujanSum D (Nat.dist t j)) = -ramanujanPacket D t := by
      exact (Finset.sum_congr rfl (fun j _ => congrArg (ramanujanSum D) (Nat.dist_comm t j))).trans hc
    have hg : (∑ i ∈ Finset.range (t + 1), ∑ j ∈ Finset.range (t + 1),
          ramanujanSum D (Nat.dist i j)) =
        (∑ i ∈ Finset.range t, ∑ j ∈ Finset.range t, ramanujanSum D (Nat.dist i j)) -
          2 * ramanujanPacket D t + (D.totient : ℝ) := by
      simp only [Finset.sum_range_succ, Finset.sum_add_distrib, Nat.dist_self, hc, hr,
        ramanujan_zero_totient D hD]
      ring
    rw [Finset.sum_range_succ, ih, hg]
    have hnon : (D : ℝ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
    unfold centeredResiduePacket
    field_simp [hnon]
    <;> ring

end RiemannResearch.RH.Pareto
