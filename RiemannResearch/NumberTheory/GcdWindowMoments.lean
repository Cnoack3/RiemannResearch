/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Gcd moments in consecutive integer windows

Source: the divisor-counting argument in the user-provided
RH/QDPPMovingWindowsResearch20261014.md, Section 7, supports the statement.
Exact grouping by gcd precedes the quantitative, location-uniform bound.
-/

open scoped BigOperators

namespace RiemannResearch.NumberTheory

def natWindow (x h : ℕ) : Finset ℕ := Finset.Icc (x + 1) (x + h)

def distinctWindowPairs (x h : ℕ) : Finset (ℕ × ℕ) :=
  ((natWindow x h).product (natWindow x h)).filter (fun p => p.1 ≠ p.2)

/-- An interval contains at most `2 h / d` multiples of `d` when `d ≤ h`.
The multiplicative form avoids division and is enough for all moment estimates. -/
theorem window_multiples_card_mul_le (x h d : ℕ) (hd : 0 < d) (hdh : d ≤ h) :
    ((natWindow x h).filter (fun n => d ∣ n)).card * d ≤ 2 * h := by
  classical
  let A := (natWindow x h).filter (fun n => d ∣ n)
  have hcard : A.card ≤ (x + h) / d - x / d := by
    calc
      A.card ≤ (Finset.Icc (x / d + 1) ((x + h) / d)).card := by
        apply Finset.card_le_card_of_injOn (fun n => n / d)
        · intro n hn
          have hn' : n ∈ natWindow x h ∧ d ∣ n := Finset.mem_filter.mp hn
          have hw : x + 1 ≤ n ∧ n ≤ x + h := Finset.mem_Icc.mp hn'.1
          apply Finset.mem_Icc.mpr
          constructor
          · have ht : x / d < n / d :=
              (Nat.div_lt_iff_lt_mul hd).2 (by
                rw [Nat.div_mul_cancel hn'.2]
                omega)
            change x / d + 1 ≤ n / d
            exact Nat.succ_le_of_lt ht
          · exact Nat.div_le_div_right hw.2
        · intro n hn m hm heq
          exact (Nat.div_left_inj (Finset.mem_filter.mp hn).2
            (Finset.mem_filter.mp hm).2).1 heq
      _ = (x + h) / d - x / d := by
        rw [Nat.card_Icc]
        omega
  have hq : x / d ≤ (x + h) / d := Nat.div_le_div_right (by omega)
  have hprod := congrArg (fun a : ℕ => a * d) (Nat.sub_add_cancel hq)
  have hlow := Nat.lt_div_mul_add (a := x) hd
  have hupp := Nat.div_mul_le_self (x + h) d
  have hcardmul := Nat.mul_le_mul_right d hcard
  change A.card * d ≤ 2 * h
  nlinarith

theorem window_gcd_mem (x h : ℕ) {p : ℕ × ℕ}
    (hp : p ∈ distinctWindowPairs x h) :
    Nat.gcd p.1 p.2 ∈ Finset.Icc 1 h := by
  have hp' := Finset.mem_filter.mp hp
  have hpw := Finset.mem_product.mp hp'.1
  have hn := Finset.mem_Icc.mp hpw.1
  have hm := Finset.mem_Icc.mp hpw.2
  apply Finset.mem_Icc.mpr
  constructor
  · have := Nat.gcd_pos_of_pos_left p.2 (show 0 < p.1 by omega)
    omega
  · rcases lt_or_gt_of_ne hp'.2 with hnm | hmn
    · have hdiv : Nat.gcd p.1 p.2 ∣ p.2 - p.1 :=
        Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
      have hle := Nat.le_of_dvd (show 0 < p.2 - p.1 by omega) hdiv
      omega
    · have hdiv : Nat.gcd p.1 p.2 ∣ p.1 - p.2 :=
        Nat.dvd_sub (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
      have hle := Nat.le_of_dvd (show 0 < p.1 - p.2 by omega) hdiv
      omega

/-- Exact grouping by gcd; no inequality is used in the decomposition. -/
theorem window_gcd_grouping (x h : ℕ) (w : ℕ → ℝ) :
    (∑ p ∈ distinctWindowPairs x h, w (Nat.gcd p.1 p.2)) =
      ∑ d ∈ Finset.Icc 1 h,
        (((distinctWindowPairs x h).filter (fun p => Nat.gcd p.1 p.2 = d)).card : ℝ)
          * w d := by
  classical
  simpa only [Finset.sum_const, nsmul_eq_mul] using
    (Finset.sum_fiberwise_of_maps_to'
      (fun p hp => window_gcd_mem x h hp) w).symm

theorem window_gcd_fiber_card_mul_sq_le (x h d : ℕ)
    (hd : 0 < d) (hdh : d ≤ h) :
    (((distinctWindowPairs x h).filter (fun p => Nat.gcd p.1 p.2 = d)).card : ℝ)
        * (d : ℝ) ^ 2 ≤ 4 * (h : ℝ) ^ 2 := by
  classical
  let A := (natWindow x h).filter (fun n => d ∣ n)
  let E := (distinctWindowPairs x h).filter (fun p => Nat.gcd p.1 p.2 = d)
  have hsub : E ⊆ A.product A := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hw := Finset.mem_product.mp (Finset.mem_filter.mp hp'.1).1
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨hw.1, ?_⟩
      rw [← hp'.2]
      exact Nat.gcd_dvd_left _ _
    · apply Finset.mem_filter.mpr
      refine ⟨hw.2, ?_⟩
      rw [← hp'.2]
      exact Nat.gcd_dvd_right _ _
  have hcard_nat : E.card ≤ A.card ^ 2 := by
    calc
      E.card ≤ (A.product A).card := Finset.card_le_card hsub
      _ = A.card ^ 2 := by rw [Finset.product_eq_sprod, Finset.card_product, pow_two]
  have hcard : (E.card : ℝ) ≤ (A.card : ℝ) ^ 2 := by exact_mod_cast hcard_nat
  have hmass : (A.card : ℝ) * (d : ℝ) ≤ 2 * (h : ℝ) := by
    exact_mod_cast window_multiples_card_mul_le x h d hd hdh
  have hmass_sq := mul_self_le_mul_self
    (show (0 : ℝ) ≤ (A.card : ℝ) * (d : ℝ) by positivity) hmass
  have hcard_sq := mul_le_mul_of_nonneg_right hcard (sq_nonneg (d : ℝ))
  change (E.card : ℝ) * (d : ℝ) ^ 2 ≤ 4 * (h : ℝ) ^ 2
  nlinarith

/-- A location-uniform gcd moment estimate for every real exponent at least two. -/
theorem window_gcd_moment_le (x h : ℕ) (hh : 0 < h)
    (s : ℝ) (hs : 2 ≤ s) :
    (∑ p ∈ distinctWindowPairs x h, (Nat.gcd p.1 p.2 : ℝ) ^ s) ≤
      4 * (h : ℝ) ^ (s + 1) := by
  classical
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  rw [window_gcd_grouping x h (fun d => (d : ℝ) ^ s)]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 h, 4 * (h : ℝ) ^ 2 * (h : ℝ) ^ (s - 2) := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hdpos, hdh⟩ := Finset.mem_Icc.mp hd
      have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
      have hdhR : (d : ℝ) ≤ h := by exact_mod_cast hdh
      have hfiber := window_gcd_fiber_card_mul_sq_le x h d (by omega) hdh
      have hrpow : (d : ℝ) ^ (s - 2) ≤ (h : ℝ) ^ (s - 2) :=
        Real.rpow_le_rpow hdR.le hdhR (by linarith)
      have hsplit : (d : ℝ) ^ s = (d : ℝ) ^ 2 * (d : ℝ) ^ (s - 2) := by
        calc
          (d : ℝ) ^ s = (d : ℝ) ^ ((2 : ℝ) + (s - 2)) := by congr 1; ring
          _ = (d : ℝ) ^ 2 * (d : ℝ) ^ (s - 2) := by rw [Real.rpow_add hdR]; norm_num
      rw [hsplit, ← mul_assoc]
      exact (mul_le_mul_of_nonneg_right hfiber (Real.rpow_nonneg hdR.le _)).trans
        (mul_le_mul_of_nonneg_left hrpow (by positivity))
    _ = (h : ℝ) * (4 * (h : ℝ) ^ 2 * (h : ℝ) ^ (s - 2)) := by simp
    _ = 4 * (h : ℝ) ^ (s + 1) := by
      have hsplit : (h : ℝ) ^ (s + 1) = (h : ℝ) ^ 3 * (h : ℝ) ^ (s - 2) := by
        calc
          (h : ℝ) ^ (s + 1) = (h : ℝ) ^ ((3 : ℝ) + (s - 2)) := by congr 1; ring
          _ = (h : ℝ) ^ 3 * (h : ℝ) ^ (s - 2) := by rw [Real.rpow_add hhR]; norm_num
      rw [hsplit]
      ring

end RiemannResearch.NumberTheory


open scoped BigOperators

namespace RiemannResearch.NumberTheory

/-- Elementary integral comparison for the singular but integrable exponent. -/
theorem sum_Icc_rpow_sub_two_le (h : ℕ) (hh : 0 < h)
    (s : ℝ) (hs : 1 < s) (hs2 : s ≤ 2) :
    (∑ d ∈ Finset.Icc 1 h, (d : ℝ) ^ (s - 2)) ≤
      (h : ℝ) ^ (s - 1) / (s - 1) := by
  classical
  have hsplit : Finset.Icc 1 h = insert 1 (Finset.Icc 2 h) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hshift : (∑ d ∈ Finset.Icc 2 h, (d : ℝ) ^ (s - 2)) =
      ∑ i ∈ Finset.Ico 1 h, ((i + 1 : ℕ) : ℝ) ^ (s - 2) := by
    symm
    apply Finset.sum_bij (fun i _ => i + 1)
    · intro i hi
      have hi' := Finset.mem_Ico.mp hi
      exact Finset.mem_Icc.mpr (by omega)
    · intro i hi j hj hij
      omega
    · intro d hd
      have hd' := Finset.mem_Icc.mp hd
      refine ⟨d - 1, Finset.mem_Ico.mpr (by omega), ?_⟩
      omega
    · intro i hi
      rfl
  have hanti : AntitoneOn (fun t : ℝ => t ^ (s - 2)) (Set.Icc (1 : ℝ) h) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow_of_nonpos (by linarith [ha.1]) hab (by linarith)
  have hint := AntitoneOn.sum_le_integral_Ico (a := 1) (b := h)
    (f := fun t : ℝ => t ^ (s - 2)) (show 1 ≤ h by omega)
    (by simpa only [Nat.cast_one] using hanti)
  norm_num only [Nat.cast_one] at hint
  rw [integral_rpow (Or.inl (show -1 < s - 2 by linarith)),
    show s - 2 + 1 = s - 1 by ring, Real.one_rpow] at hint
  have hspos : 0 < s - 1 := by linarith
  calc
    _ = 1 + ∑ i ∈ Finset.Ico 1 h, ((i + 1 : ℕ) : ℝ) ^ (s - 2) := by
      rw [hsplit, Finset.sum_insert (by simp), hshift]
      simp
    _ ≤ 1 + ((h : ℝ) ^ (s - 1) - 1) / (s - 1) := by linarith only [hint]
    _ = ((s - 1) + (h : ℝ) ^ (s - 1) - 1) / (s - 1) := by
      field_simp [ne_of_gt hspos]
      ring
    _ ≤ (h : ℝ) ^ (s - 1) / (s - 1) :=
      div_le_div_of_nonneg_right (by linarith) hspos.le

/-- Gcd moment bound in the range needed for `1 / 2 < epsilon < 3/4`. -/
theorem window_gcd_moment_le_below_two (x h : ℕ) (hh : 0 < h)
    (s : ℝ) (hs : 1 < s) (hs2 : s ≤ 2) :
    (∑ p ∈ distinctWindowPairs x h, (Nat.gcd p.1 p.2 : ℝ) ^ s) ≤
      (4 / (s - 1)) * (h : ℝ) ^ (s + 1) := by
  classical
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  rw [window_gcd_grouping x h (fun d => (d : ℝ) ^ s)]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 h, 4 * (h : ℝ) ^ 2 * (d : ℝ) ^ (s - 2) := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hdpos, hdh⟩ := Finset.mem_Icc.mp hd
      have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
      have hfiber := window_gcd_fiber_card_mul_sq_le x h d (by omega) hdh
      have hsplit : (d : ℝ) ^ s = (d : ℝ) ^ 2 * (d : ℝ) ^ (s - 2) := by
        calc
          (d : ℝ) ^ s = (d : ℝ) ^ ((2 : ℝ) + (s - 2)) := by congr 1; ring
          _ = (d : ℝ) ^ 2 * (d : ℝ) ^ (s - 2) := by rw [Real.rpow_add hdR]; norm_num
      rw [hsplit, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hfiber (Real.rpow_nonneg hdR.le _)
    _ = 4 * (h : ℝ) ^ 2 * ∑ d ∈ Finset.Icc 1 h, (d : ℝ) ^ (s - 2) := by
      rw [Finset.mul_sum]
    _ ≤ 4 * (h : ℝ) ^ 2 * ((h : ℝ) ^ (s - 1) / (s - 1)) :=
      mul_le_mul_of_nonneg_left (sum_Icc_rpow_sub_two_le h hh s hs hs2) (by positivity)
    _ = (4 / (s - 1)) * (h : ℝ) ^ (s + 1) := by
      have hsplit : (h : ℝ) ^ (s + 1) = (h : ℝ) ^ 2 * (h : ℝ) ^ (s - 1) := by
        calc
          (h : ℝ) ^ (s + 1) = (h : ℝ) ^ ((2 : ℝ) + (s - 1)) := by congr 1; ring
          _ = (h : ℝ) ^ 2 * (h : ℝ) ^ (s - 1) := by rw [Real.rpow_add hhR]; norm_num
      rw [hsplit]
      ring

/-- A single explicit constant valid uniformly for every real `s > 1`. -/
theorem window_gcd_moment_le_all (x h : ℕ) (hh : 0 < h)
    (s : ℝ) (hs : 1 < s) :
    (∑ p ∈ distinctWindowPairs x h, (Nat.gcd p.1 p.2 : ℝ) ^ s) ≤
      (4 + 4 / (s - 1)) * (h : ℝ) ^ (s + 1) := by
  have hspos : 0 < s - 1 := by linarith
  have hc : (0 : ℝ) ≤ 4 / (s - 1) := by positivity
  have hp : 0 ≤ (h : ℝ) ^ (s + 1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  by_cases hs2 : 2 ≤ s
  · exact (window_gcd_moment_le x h hh s hs2).trans
      (mul_le_mul_of_nonneg_right (by linarith : (4 : ℝ) ≤ 4 + 4 / (s - 1)) hp)
  · exact (window_gcd_moment_le_below_two x h hh s hs (by linarith)).trans
      (mul_le_mul_of_nonneg_right (by linarith : 4 / (s - 1) ≤ 4 + 4 / (s - 1)) hp)

end RiemannResearch.NumberTheory


open scoped BigOperators

namespace RiemannResearch.NumberTheory

/-- Reindex a physical consecutive interval by its offsets. -/
theorem natWindow_sum_eq_fin (x h : ℕ) (g : ℕ → ℝ) :
    (∑ n ∈ natWindow x h, g n) =
      ∑ i : Fin h, g (x + (i : ℕ) + 1) := by
  classical
  symm
  apply Finset.sum_bij (fun (i : Fin h) _ => x + (i : ℕ) + 1)
  · intro i hi
    change x + (i : ℕ) + 1 ∈ Finset.Icc (x + 1) (x + h)
    apply Finset.mem_Icc.mpr
    have hi := i.isLt
    constructor <;> omega
  · intro i hi j hj hij
    apply Fin.ext
    change (i : ℕ) = (j : ℕ)
    omega
  · intro n hn
    have hn' : x + 1 ≤ n ∧ n ≤ x + h := Finset.mem_Icc.mp hn
    let i : Fin h := ⟨n - (x + 1), by omega⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    dsimp [i]
    omega
  · intro i hi
    rfl

/-- Exact equality between physical off-diagonal pairs and a finite matrix sum. -/
theorem distinctWindowPairs_sum_eq_fin (x h : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ p ∈ distinctWindowPairs x h, f p.1 p.2) =
      ∑ i : Fin h, ∑ j : Fin h,
        if i = j then 0 else f (x + (i : ℕ) + 1) (x + (j : ℕ) + 1) := by
  classical
  calc
    _ = ∑ n ∈ natWindow x h, ∑ m ∈ natWindow x h,
        if n ≠ m then f n m else 0 := by
      simp only [distinctWindowPairs, Finset.sum_filter,
        Finset.product_eq_sprod, Finset.sum_product]
    _ = ∑ i : Fin h, ∑ m ∈ natWindow x h,
        if x + (i : ℕ) + 1 ≠ m then f (x + (i : ℕ) + 1) m else 0 :=
      natWindow_sum_eq_fin x h _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [natWindow_sum_eq_fin x h]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : i = j
      · simp [hij]
      · have hnat : x + (i : ℕ) + 1 ≠ x + (j : ℕ) + 1 := by
          intro hnat
          apply hij
          apply Fin.ext
          change (i : ℕ) = (j : ℕ)
          omega
        simp only [if_pos hnat, if_neg hij]

end RiemannResearch.NumberTheory
