/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MobiusReciprocalCutoff
import RiemannResearch.RH.MertensElementary
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusLogarithmicRateBridge

/-!
# Exact finite estimates for a quantitative Mertens bootstrap

The arithmetic identity is a cutoff refinement of `M_log_identity` in the
repository's compatibility port of the PNT+ project, whose source and license
are recorded in `PrimeNumberTheorem/Consequences.lean`. The finite quotient
regrouping retains the genuine Mobius and von Mangoldt signs. Its bound uses
the elementary factorial/Chebyshev proof in `RH/MertensElementary`.

The final finite theorem displays two estimates as hypotheses: a linear
bound for the actual summatory Mobius function above a chosen cutoff, and an
inverse-fourth-logarithm bound for the actual Chebyshev error. Separate cutoff
optimization and the established quantitative PNT discharge these inputs.

This provides an elementary arithmetic route to the half-damping finite-energy
endpoint in J.-F. Burnol, "On an analytic estimate in the theory of the Riemann
zeta function and a theorem of Baez-Duarte", Acta Cientifica Venezolana 54
(2003), 210-215, Lemma 4.1; author manuscript
https://arxiv.org/abs/math/0202166. That source supports the endpoint statement;
the finite bootstrap here is a direct derivation from the cited formal inputs,
not an import of the paper as an axiom or a claim of a new number-theoretic rate.
-/

noncomputable section
open Filter Finset
open scoped BigOperators

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

theorem finite_log_abel (a : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ Finset.range (N + 1), a d * (Real.log N - Real.log d)) =
      ∑ k ∈ Finset.range N, (∑ d ∈ Finset.range (k + 1), a d) *
        (Real.log (k + 1) - Real.log k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    calc
      _ = (∑ d ∈ Finset.range (N + 1),
          a d * (Real.log N - Real.log d)) +
          (∑ d ∈ Finset.range (N + 1), a d) *
            (Real.log (N + 1) - Real.log N) := by
        rw [Finset.sum_range_succ]
        simp only [Nat.cast_add, Nat.cast_one, sub_self, mul_zero, add_zero]
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d hd
        ring
      _ = _ := by
        rw [ih]
        symm
        simpa only [Nat.cast_add, Nat.cast_one] using
          (Finset.sum_range_succ (fun k : ℕ =>
            (∑ d ∈ Finset.range (k + 1), a d) *
              (Real.log (k + 1) - Real.log k)) N)

theorem M_nat_eq_sum_range (N : ℕ) :
    M (N : ℝ) = ∑ d ∈ Finset.range (N + 1), (ArithmeticFunction.moebius d : ℝ) := by
  unfold M
  simp only [Nat.floor_natCast]
  congr 1
  ext d
  simp only [Finset.mem_Iic, Finset.mem_range]
  omega

theorem M_nat_abs_le_self (N : ℕ) : |M (N : ℝ)| ≤ (N : ℝ) := by
  rw [M_nat_eq_sum_range, Finset.sum_range_succ']
  simp only [ArithmeticFunction.map_zero, Int.cast_zero, add_zero]
  calc
    _ ≤ ∑ k ∈ Finset.range N, |(ArithmeticFunction.moebius (k + 1) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k + 1)
    _ = _ := by simp

theorem mobius_log_div_eq_abel (N : ℕ) :
    (∑ d ∈ Finset.Iic N, (ArithmeticFunction.moebius d : ℝ) *
      Real.log ((N : ℝ) / d)) =
    ∑ k ∈ Finset.range N, M (k : ℝ) *
      (Real.log (k + 1) - Real.log k) := by
  by_cases hN : N = 0
  · simp [hN, M]
  have hset : Finset.Iic N = Finset.range (N + 1) := by ext; simp
  rw [hset]
  calc
    _ = ∑ d ∈ Finset.range (N + 1), (ArithmeticFunction.moebius d : ℝ) *
        (Real.log N - Real.log d) := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hd0 : d = 0
      · simp [hd0]
      · rw [Real.log_div (by exact_mod_cast hN) (by exact_mod_cast hd0)]
    _ = _ := by rw [finite_log_abel]; simp_rw [← M_nat_eq_sum_range]

theorem nat_log_step_nonneg (k : ℕ) : 0 ≤ Real.log (k + 1) - Real.log k := by
  by_cases hk : k = 0
  · simp [hk]
  · apply sub_nonneg.mpr
    apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hk)
    linarith

theorem nat_mul_log_step_le_one (k : ℕ) :
    (k : ℝ) * (Real.log (k + 1) - Real.log k) ≤ 1 := by
  by_cases hk : k = 0
  · simp [hk]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have h := Real.log_le_sub_one_of_pos
    (div_pos (show (0 : ℝ) < k + 1 by positivity) hkpos)
  rw [Real.log_div (by positivity : (k : ℝ) + 1 ≠ 0) hkpos.ne'] at h
  have hm := mul_le_mul_of_nonneg_left h hkpos.le
  have he : (k : ℝ) * (((k : ℝ) + 1) / k - 1) = 1 := by field_simp; ring
  norm_cast at *
  linarith

/-- Finite Abel cancellation above a freely chosen cutoff. -/
theorem mobius_log_div_abs_le_cutoff (N Y : ℕ) (hYN : Y ≤ N)
    (A : ℝ) (hA : 0 ≤ A)
    (hM : ∀ t : ℝ, (Y : ℝ) ≤ t → |M t| ≤ A * t) :
    |∑ d ∈ Finset.Iic N, (ArithmeticFunction.moebius d : ℝ) *
      Real.log ((N : ℝ) / d)| ≤ (Y : ℝ) + A * N := by
  rw [mobius_log_div_eq_abel]
  have hterm (k : ℕ) :
      |M (k : ℝ) * (Real.log (k + 1) - Real.log k)| ≤
        if k < Y then 1 else A := by
    rw [abs_mul, abs_of_nonneg (nat_log_step_nonneg k)]
    by_cases hk : k < Y
    · rw [if_pos hk]
      exact (mul_le_mul_of_nonneg_right (M_nat_abs_le_self k)
        (nat_log_step_nonneg k)).trans (nat_mul_log_step_le_one k)
    · rw [if_neg hk]
      have hh := mul_le_mul_of_nonneg_right
        (hM k (by exact_mod_cast Nat.le_of_not_gt hk)) (nat_log_step_nonneg k)
      have hh' := mul_le_mul_of_nonneg_left (nat_mul_log_step_le_one k) hA
      nlinarith
  calc
    _ ≤ ∑ k ∈ Finset.range N,
        |M (k : ℝ) * (Real.log (k + 1) - Real.log k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N, (if k < Y then (1 : ℝ) else A) :=
      Finset.sum_le_sum (fun k hk => hterm k)
    _ ≤ ∑ k ∈ Finset.range N, ((if k < Y then (1 : ℝ) else 0) + A) := by
      apply Finset.sum_le_sum
      intro k hk
      split_ifs <;> linarith
    _ = (Y : ℝ) + A * N := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      have he : (Finset.range N).filter (fun k => k < Y) = Finset.range Y := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      rw [he]
      simp [mul_comm]

theorem positive_sum_eq_range_succ (f : ℕ → ℝ) (Y : ℕ) :
    (∑ d ∈ Finset.Icc 1 Y, f d) = ∑ k ∈ Finset.range Y, f (k + 1) := by
  have he : (Finset.range Y).image (fun k => k + 1) = Finset.Icc 1 Y := by
    ext d
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨k, hk, rfl⟩; omega
    · intro hd; exact ⟨d - 1, by omega, by omega⟩
  rw [← he, Finset.sum_image]
  intro a ha b hb hab
  dsimp only at hab
  omega

theorem R_inverse_log_fourth_head_bound (N Y : ℕ) (hY : 0 < Y) (hYN : Y ≤ N)
    (C : ℝ) (hC : 0 ≤ C)
    (hR : ∀ u : ℝ, 1 ≤ u → |R u| ≤ C * u / (1 + Real.log u) ^ 4) :
    |∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ) * R ((N : ℝ) / d)| ≤
      3 * C * N / (1 + Real.log ((N : ℝ) / Y)) ^ 2 := by
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  have hNr : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hY hYN
  have hNY : (1 : ℝ) ≤ (N : ℝ) / Y := (le_div_iff₀ hYr).mpr (by
    simpa only [one_mul] using (show (Y : ℝ) ≤ (N : ℝ) by exact_mod_cast hYN))
  have hlogNY : 0 ≤ Real.log ((N : ℝ) / Y) := Real.log_nonneg hNY
  have hterm (d : ℕ) (hd : d ∈ Finset.Icc 1 Y) :
      |(ArithmeticFunction.moebius d : ℝ) * R ((N : ℝ) / d)| ≤
        (C * N / (1 + Real.log ((N : ℝ) / Y)) ^ 2) *
          (1 / ((d : ℝ) * (1 + Real.log ((N : ℝ) / d)) ^ 2)) := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hdY : (d : ℝ) ≤ Y := by exact_mod_cast (Finset.mem_Icc.mp hd).2
    have hNd : (1 : ℝ) ≤ (N : ℝ) / d :=
      (le_div_iff₀ hdpos).mpr (by
        simpa only [one_mul] using
          hdY.trans (show (Y : ℝ) ≤ (N : ℝ) by exact_mod_cast hYN))
    have hlogNd : 0 ≤ Real.log ((N : ℝ) / d) := Real.log_nonneg hNd
    have hlogs : Real.log ((N : ℝ) / Y) ≤ Real.log ((N : ℝ) / d) := by
      apply Real.log_le_log (by positivity)
      exact div_le_div_of_nonneg_left hNr.le hdpos hdY
    have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    rw [abs_mul]
    calc
      _ ≤ |R ((N : ℝ) / d)| := mul_le_of_le_one_left (abs_nonneg _) hmu
      _ ≤ C * ((N : ℝ) / d) / (1 + Real.log ((N : ℝ) / d)) ^ 4 := hR _ hNd
      _ = (C * N / (1 + Real.log ((N : ℝ) / d)) ^ 2) *
          (1 / ((d : ℝ) * (1 + Real.log ((N : ℝ) / d)) ^ 2)) := by
        field_simp
      _ ≤ _ := by gcongr
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 Y, |(ArithmeticFunction.moebius d : ℝ) * R ((N : ℝ) / d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 Y,
        (C * N / (1 + Real.log ((N : ℝ) / Y)) ^ 2) *
          (1 / ((d : ℝ) * (1 + Real.log ((N : ℝ) / d)) ^ 2)) := Finset.sum_le_sum hterm
    _ = (C * N / (1 + Real.log ((N : ℝ) / Y)) ^ 2) *
        ∑ d ∈ Finset.Icc 1 Y, 1 / ((d : ℝ) * (1 + Real.log ((N : ℝ) / d)) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ (C * N / (1 + Real.log ((N : ℝ) / Y)) ^ 2) * 3 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [positive_sum_eq_range_succ]
      simpa only [Nat.cast_add, Nat.cast_one] using
        finite_reciprocal_square_log_sum_le (N : ℝ) Y hY (by exact_mod_cast hYN)
    _ = _ := by ring

theorem weighted_quotient_tail_reindex (a b : ℕ → ℝ) (N Y : ℕ) :
    (∑ d ∈ Finset.Ioc Y N, a d * ∑ q ∈ Finset.Icc 1 (N / d), b q) =
      ∑ q ∈ Finset.Icc 1 (N / (Y + 1)), b q * ∑ d ∈ Finset.Ioc Y (N / q), a d := by
  classical
  let K := N / (Y + 1)
  have hrow (d : ℕ) (hd : d ∈ Finset.Ioc Y N) :
      a d * (∑ q ∈ Finset.Icc 1 (N / d), b q) =
        ∑ q ∈ Finset.Icc 1 K, if q ≤ N / d then a d * b q else 0 := by
    have hdpos : 0 < d := lt_of_le_of_lt (Nat.zero_le Y) (Finset.mem_Ioc.mp hd).1
    have hdY : Y + 1 ≤ d := (Finset.mem_Ioc.mp hd).1
    have hqK : N / d ≤ K := by
      apply (Nat.le_div_iff_mul_le (Nat.succ_pos Y)).mpr
      have h := Nat.div_mul_le_self N d
      nlinarith
    have he : (Finset.Icc 1 K).filter (fun q => q ≤ N / d) = Finset.Icc 1 (N / d) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [← Finset.sum_filter, he, Finset.mul_sum]
  have hcol (q : ℕ) (hq : q ∈ Finset.Icc 1 K) :
      (Finset.Ioc Y N).filter (fun d => q ≤ N / d) = Finset.Ioc Y (N / q) := by
    have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hYd, hdN⟩, hqd⟩
      have hdpos : 0 < d := lt_of_le_of_lt (Nat.zero_le Y) hYd
      refine ⟨hYd, (Nat.le_div_iff_mul_le hqpos).mpr ?_⟩
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hdpos).mp hqd
    · rintro ⟨hYd, hdq⟩
      have hdpos : 0 < d := lt_of_le_of_lt (Nat.zero_le Y) hYd
      have hp : d * q ≤ N := (Nat.le_div_iff_mul_le hqpos).mp hdq
      refine ⟨⟨hYd, (by nlinarith)⟩, (Nat.le_div_iff_mul_le hdpos).mpr ?_⟩
      simpa only [Nat.mul_comm] using hp
  calc
    _ = ∑ d ∈ Finset.Ioc Y N, ∑ q ∈ Finset.Icc 1 K,
        if q ≤ N / d then a d * b q else 0 := Finset.sum_congr rfl hrow
    _ = ∑ q ∈ Finset.Icc 1 K, ∑ d ∈ Finset.Ioc Y N,
        if q ≤ N / d then a d * b q else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [← Finset.sum_filter, hcol q hq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring

theorem Psi_nat_quotient (N d : ℕ) :
    Psi ((N : ℝ) / d) =
      ∑ q ∈ Finset.Icc 1 (N / d), ArithmeticFunction.vonMangoldt q := by
  rw [Psi, Chebyshev.psi_eq_sum_Icc, Nat.floor_div_natCast, Nat.floor_natCast,
    Icc_zero_eq_insert]
  simp

theorem mobius_Psi_tail_eq (N Y : ℕ) :
    (∑ d ∈ Finset.Ioc Y N, (ArithmeticFunction.moebius d : ℝ) * Psi ((N : ℝ) / d)) =
      ∑ q ∈ Finset.Icc 1 (N / (Y + 1)), ArithmeticFunction.vonMangoldt q *
        (M ((N : ℝ) / q) - M (Y : ℝ)) := by
  simp_rw [Psi_nat_quotient]
  rw [weighted_quotient_tail_reindex]
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
  have hqbound := (Nat.le_div_iff_mul_le (Nat.succ_pos Y)).mp (Finset.mem_Icc.mp hq).2
  have hYq : Y ≤ N / q := (Nat.le_div_iff_mul_le hqpos).mpr (by nlinarith)
  have he : M ((N : ℝ) / q) = M ((N / q : ℕ) : ℝ) := by
    unfold M
    rw [Nat.floor_div_natCast]
    simp only [Nat.floor_natCast]
  rw [he, M_nat_difference Y (N / q) hYq]

theorem mangoldtReciprocalPrefix_eq_sum_Icc (K : ℕ) :
    RiemannResearch.RH.mangoldtReciprocalPrefix K =
      ∑ q ∈ Finset.Icc 1 K, ArithmeticFunction.vonMangoldt q / (q : ℝ) := by
  unfold RiemannResearch.RH.mangoldtReciprocalPrefix
  have he : Finset.range (K + 1) = insert 0 (Finset.Icc 1 K) := by
    ext q
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [he]
  simp

theorem mobius_Psi_tail_abs_le_prefix (N Y : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hM : ∀ t : ℝ, (Y : ℝ) ≤ t → |M t| ≤ A * t) :
    |∑ d ∈ Finset.Ioc Y N, (ArithmeticFunction.moebius d : ℝ) * Psi ((N : ℝ) / d)| ≤
      2 * A * N * RiemannResearch.RH.mangoldtReciprocalPrefix (N / (Y + 1)) := by
  rw [mobius_Psi_tail_eq, mangoldtReciprocalPrefix_eq_sum_Icc, Finset.mul_sum]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  apply Finset.sum_le_sum
  intro q hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
  have hp := (Nat.le_div_iff_mul_le (Nat.succ_pos Y)).mp (Finset.mem_Icc.mp hq).2
  have hYq : (Y : ℝ) ≤ (N : ℝ) / q := by
    apply (le_div_iff₀ hqpos).mpr
    exact_mod_cast (show Y * q ≤ N by nlinarith)
  have hdiff : |M ((N : ℝ) / q) - M (Y : ℝ)| ≤ 2 * A * ((N : ℝ) / q) := by
    calc
      _ ≤ |M ((N : ℝ) / q)| + |M (Y : ℝ)| := abs_sub _ _
      _ ≤ A * ((N : ℝ) / q) + A * Y := add_le_add (hM _ hYq) (hM _ le_rfl)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hYq hA]
  rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  calc
    _ ≤ ArithmeticFunction.vonMangoldt q * (2 * A * ((N : ℝ) / q)) :=
      mul_le_mul_of_nonneg_left hdiff ArithmeticFunction.vonMangoldt_nonneg
    _ = _ := by ring

theorem mangoldtReciprocalPrefix_quotient_le_log (N Y : ℕ) (hY : 0 < Y) (hYN : Y ≤ N) :
    RiemannResearch.RH.mangoldtReciprocalPrefix (N / (Y + 1)) ≤
      Real.log ((N : ℝ) / Y) + Real.log 4 + 5 := by
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  have hNY : (1 : ℝ) ≤ (N : ℝ) / Y := (le_div_iff₀ hYr).mpr (by
    simpa only [one_mul] using (show (Y : ℝ) ≤ (N : ℝ) by exact_mod_cast hYN))
  have hlogNY := Real.log_nonneg hNY
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  by_cases hK : N / (Y + 1) = 0
  · simp only [hK, RiemannResearch.RH.mangoldtReciprocalPrefix, Finset.sum_range_succ,
      Finset.sum_range_zero, ArithmeticFunction.map_zero, Nat.cast_zero, div_zero, zero_add]
    linarith
  have hKpos : (0 : ℝ) < (N / (Y + 1) : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hKle : ((N / (Y + 1) : ℕ) : ℝ) ≤ (N : ℝ) / Y := by
    apply (le_div_iff₀ hYr).mpr
    have h := Nat.div_mul_le_self N (Y + 1)
    exact_mod_cast (show N / (Y + 1) * Y ≤ N by nlinarith)
  have hlog := Real.log_le_log hKpos hKle
  have hb := (abs_le.mp
    (RiemannResearch.RH.mangoldtReciprocalPrefix_discrepancy_bound hK)).2
  linarith

theorem mobius_Psi_tail_abs_le_log (N Y : ℕ) (hY : 0 < Y) (hYN : Y ≤ N)
    (A : ℝ) (hA : 0 ≤ A)
    (hM : ∀ t : ℝ, (Y : ℝ) ≤ t → |M t| ≤ A * t) :
    |∑ d ∈ Finset.Ioc Y N, (ArithmeticFunction.moebius d : ℝ) * Psi ((N : ℝ) / d)| ≤
      2 * A * N * (Real.log ((N : ℝ) / Y) + Real.log 4 + 5) :=
  (mobius_Psi_tail_abs_le_prefix N Y A hA hM).trans
    (mul_le_mul_of_nonneg_left (mangoldtReciprocalPrefix_quotient_le_log N Y hY hYN)
      (by positivity))

theorem M_log_bootstrap_identity (N Y : ℕ) (hY : 0 < Y) (hYN : Y ≤ N) :
    M (N : ℝ) * Real.log N =
      (∑ d ∈ Finset.Iic N, (ArithmeticFunction.moebius d : ℝ) * Real.log ((N : ℝ) / d)) -
      (N : ℝ) * RiemannResearch.RH.Pareto.mobiusReciprocalSum Y -
      (∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ) * R ((N : ℝ) / d)) -
      (∑ d ∈ Finset.Ioc Y N, (ArithmeticFunction.moebius d : ℝ) * Psi ((N : ℝ) / d)) := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast lt_of_lt_of_le hY hYN
  rw [M_log_identity (N : ℝ) hN]
  simp only [Nat.floor_natCast, mul_sub, Finset.sum_sub_distrib]
  have hdis : Disjoint (Finset.Iic Y) (Finset.Ioc Y N) := by
    apply Finset.disjoint_left.mpr
    intro d hd hd'
    simp only [Finset.mem_Iic, Finset.mem_Ioc] at hd hd'
    omega
  have hunion : Finset.Iic Y ∪ Finset.Ioc Y N = Finset.Iic N := by
    ext d
    simp only [Finset.mem_union, Finset.mem_Iic, Finset.mem_Ioc]
    omega
  have hhead :
      (∑ d ∈ Finset.Iic Y, (ArithmeticFunction.moebius d : ℝ) * Psi ((N : ℝ) / d)) =
      (N : ℝ) * RiemannResearch.RH.Pareto.mobiusReciprocalSum Y +
      (∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ) * R ((N : ℝ) / d)) := by
    have hz :
        (∑ d ∈ Finset.Iic Y, (ArithmeticFunction.moebius d : ℝ) * Psi ((N : ℝ) / d)) =
        (∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ) * Psi ((N : ℝ) / d)) := by
      symm
      apply Finset.sum_subset
      · intro d hd
        exact Finset.mem_Iic.mpr (Finset.mem_Icc.mp hd).2
      · intro d hd hd'
        have hd0 : d = 0 := by
          simp only [Finset.mem_Iic, Finset.mem_Icc] at hd hd'
          omega
        simp [hd0]
    rw [hz]
    unfold RiemannResearch.RH.Pareto.mobiusReciprocalSum
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    unfold R
    ring
  have htotal :
      (∑ d ∈ Finset.Iic N, (ArithmeticFunction.moebius d : ℝ) * Psi ((N : ℝ) / d)) =
      (∑ d ∈ Finset.Iic Y, (ArithmeticFunction.moebius d : ℝ) * Psi ((N : ℝ) / d)) +
      (∑ d ∈ Finset.Ioc Y N, (ArithmeticFunction.moebius d : ℝ) * Psi ((N : ℝ) / d)) := by
    rw [← hunion, Finset.sum_union hdis]
  rw [htotal, hhead]
  ring

theorem M_log_bootstrap_finite (N Y J : ℕ) (hY : 0 < Y) (hYN : Y ≤ N)
    (hJ : 0 < J) (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hM : ∀ t : ℝ, (Y : ℝ) ≤ t → |M t| ≤ A * t)
    (hR : ∀ u : ℝ, 1 ≤ u → |R u| ≤ C * u / (1 + Real.log u) ^ 4) :
    |M (N : ℝ) * Real.log N| ≤
      (Y : ℝ) + A * N +
      (N : ℝ) * (1 / (J : ℝ) + 1 / ((Y : ℝ) * J) + A * ((harmonic J : ℝ) + 1)) +
      3 * C * N / (1 + Real.log ((N : ℝ) / Y)) ^ 2 +
      2 * A * N * (Real.log ((N : ℝ) / Y) + Real.log 4 + 5) := by
  rw [M_log_bootstrap_identity N Y hY hYN]
  have hL := mobius_log_div_abs_le_cutoff N Y hYN A hA hM
  have hm := mobiusReciprocalSum_cutoff_bound_of_uniform_M_bound Y J hY hJ A hA hM
  have hh := R_inverse_log_fourth_head_bound N Y hY hYN C hC hR
  have ht := mobius_Psi_tail_abs_le_log N Y hY hYN A hA hM
  have hmn := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (α := ℝ) N)
  have h1 := abs_sub (∑ d ∈ Finset.Iic N, (ArithmeticFunction.moebius d : ℝ) *
    Real.log ((N : ℝ) / d)) ((N : ℝ) * RiemannResearch.RH.Pareto.mobiusReciprocalSum Y)
  have h2 := abs_sub ((∑ d ∈ Finset.Iic N, (ArithmeticFunction.moebius d : ℝ) *
    Real.log ((N : ℝ) / d)) - (N : ℝ) * RiemannResearch.RH.Pareto.mobiusReciprocalSum Y)
    (∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ) * R ((N : ℝ) / d))
  have h3 := abs_sub (((∑ d ∈ Finset.Iic N, (ArithmeticFunction.moebius d : ℝ) *
    Real.log ((N : ℝ) / d)) - (N : ℝ) * RiemannResearch.RH.Pareto.mobiusReciprocalSum Y) -
    (∑ d ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius d : ℝ) * R ((N : ℝ) / d)))
    (∑ d ∈ Finset.Ioc Y N, (ArithmeticFunction.moebius d : ℝ) * Psi ((N : ℝ) / d))
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)] at h1
  linarith

theorem M_abs_le_self {x : ℝ} (hx : 0 ≤ x) : |M x| ≤ x := by
  have he : M x = M (⌊x⌋₊ : ℝ) := by simp [M]
  rw [he]
  exact (M_nat_abs_le_self ⌊x⌋₊).trans (Nat.floor_le hx)

end RiemannResearch.NumberTheory.PrimeNumberTheorem
