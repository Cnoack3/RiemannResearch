/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Intervals
import RiemannResearch.RH.NearbyDilationGram

/-! # Eighth-moment budgets on blocks of growing moduli

A uniform eighth-power budget on blocks implies every strictly smaller
moment when block masses decay geometrically. The endpoints need not be
LCMs. Distinct successive LCMs in a divisibility chain grow by at least two.
-/

noncomputable section
open Filter
open scoped BigOperators
namespace RiemannResearch.RH.QLcmShellMoment

/-- Weighted interpolation on a single finite block. -/
theorem block_interpolation (s : Finset ℕ) (w a : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (ha : ∀ n, 0 ≤ a n)
    {t : ℝ} (ht : 0 < t) (ht' : t < 1) :
    (∑ n ∈ s, w n * a n ^ (8 * t)) ≤
      (∑ n ∈ s, w n * a n ^ (8: ℕ)) ^ t * (∑ n ∈ s, w n) ^ (1 - t) := by
  let f (n : ℕ) := (w n * a n ^ (8: ℕ)) ^ t
  let g (n : ℕ) := w n ^ (1 - t)
  have h1t : 0 < 1 - t := by linarith
  have hc : (1 / t).HolderConjugate (1 / (1 - t)) := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · exact (one_lt_div ht).mpr ht'
    · simp [one_div]
  have hf (n : ℕ) : (f n) ^ (1 / t) = w n * a n ^ (8: ℕ) := by
    rw [show f n = (w n * a n ^ (8: ℕ)) ^ t from rfl,
      ← Real.rpow_mul (mul_nonneg (hw _) (by positivity))]
    rw [show t * (1 / t) = 1 by field_simp, Real.rpow_one]
  have hg (n : ℕ) : (g n) ^ (1 / (1 - t)) = w n := by
    rw [show g n = w n ^ (1 - t) from rfl, ← Real.rpow_mul (hw n)]
    rw [show (1 - t) * (1 / (1 - t)) = 1 by field_simp, Real.rpow_one]
  have hfg (n : ℕ) : f n * g n = w n * a n ^ (8 * t) := by
    dsimp only [f, g]
    rw [Real.mul_rpow (hw n) (by positivity)]
    have he : (a n ^ (8: ℕ)) ^ t = a n ^ (8 * t) := by
      rw [← Real.rpow_natCast (a n) 8, ← Real.rpow_mul (ha n)]
      norm_num
    rw [he, mul_right_comm, ← Real.rpow_add' (hw n) (by linarith : t + (1 - t) ≠ 0)]
    rw [show t + (1 - t) = 1 by ring, Real.rpow_one]
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s (f := f) (g := g) hc
    (fun n _ => Real.rpow_nonneg (mul_nonneg (hw n) (by positivity)) _)
    (fun n _ => Real.rpow_nonneg (hw n) _)
  simp only [hf, hg, hfg] at h
  simpa only [one_div, inv_inv] using h

/-- An abstract exhaustion by geometric-mass blocks. A finite initial segment is free. -/
theorem summable_of_uniform_eighth_blocks (L : ℕ → ℕ) (hL : StrictMono L)
    (w a : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (ha : ∀ n, 0 ≤ a n)
    {B C r : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r < 1)
    (hb : ∀ j, (∑ n ∈ Finset.Ico (L j) (L (j + 1)), w n * a n ^ (8: ℕ)) ≤ B)
    (hm : ∀ j, (∑ n ∈ Finset.Ico (L j) (L (j + 1)), w n) ≤ C * r ^ j)
    {t : ℝ} (ht : 0 < t) (ht' : t < 1) :
    Summable (fun n => w n * a n ^ (8 * t)) := by
  let f (n : ℕ) := w n * a n ^ (8 * t)
  let c := B ^ t * C ^ (1 - t)
  let z := r ^ (1 - t)
  have hz0 : 0 ≤ z := Real.rpow_nonneg hr _
  have hz1 : z < 1 := Real.rpow_lt_one hr hr1 (by linarith)
  have hsz : Summable (fun j : ℕ => c * z ^ j) :=
    (summable_geometric_of_lt_one hz0 hz1).mul_left c
  have hfn (n : ℕ) : 0 ≤ f n := mul_nonneg (hw n) (Real.rpow_nonneg (ha n) _)
  have hcz (j : ℕ) : 0 ≤ c * z ^ j := by dsimp [c]; positivity
  have hblock (j : ℕ) :
      (∑ n ∈ Finset.Ico (L j) (L (j + 1)), f n) ≤ c * z ^ j := by
    apply (block_interpolation _ w a hw ha ht ht').trans
    calc
      _ ≤ B ^ t * (C * r ^ j) ^ (1 - t) := by
        have hn₁ : 0 ≤ ∑ n ∈ Finset.Ico (L j) (L (j + 1)), w n * a n ^ (8: ℕ) :=
          Finset.sum_nonneg (fun n _ => mul_nonneg (hw n) (by positivity))
        have hn₂ : 0 ≤ ∑ n ∈ Finset.Ico (L j) (L (j + 1)), w n :=
          Finset.sum_nonneg (fun n _ => hw n)
        exact mul_le_mul (Real.rpow_le_rpow hn₁ (hb j) ht.le)
          (Real.rpow_le_rpow hn₂ (hm j) (by linarith))
          (Real.rpow_nonneg hn₂ _) (Real.rpow_nonneg hB _)
      _ = _ := by
        rw [Real.mul_rpow hC (pow_nonneg hr _)]
        have hex : (r ^ j) ^ (1 - t) = (r ^ (1 - t)) ^ j := by
          rw [← Real.rpow_natCast r j, ← Real.rpow_mul hr,
            ← Real.rpow_natCast (r ^ (1 - t)) j, ← Real.rpow_mul hr]
          rw [mul_comm]
        rw [hex]
        dsimp [c, z]
        ring
  have hpre (j : ℕ) : (∑ n ∈ Finset.range (L j), f n) ≤
      (∑ n ∈ Finset.range (L 0), f n) + ∑ i ∈ Finset.range j, c * z ^ i := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ]
      have he := Finset.sum_range_add_sum_Ico f (hL.monotone (Nat.le_succ j))
      have h' := add_le_add ih (hblock j)
      linarith
  apply summable_of_sum_range_le (c := (∑ n ∈ Finset.range (L 0), f n) + ∑' i, c * z ^ i) hfn
  intro k
  have hkl : k ≤ L k := hL.id_le k
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkl)
    (fun i _ _ => hfn i)
  exact hsub.trans ((hpre k).trans (add_le_add le_rfl (hsz.sum_le_tsum _ (fun i _ => hcz i))))


private theorem reciprocal_square_block_mass (A B : ℕ) (hA : 0 < A) :
    (∑ n ∈ Finset.Ico A B, 1 / (n: ℝ) ^ 2) ≤ 2 / (A: ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.Ico A B, 2 * Pareto.positiveWeight n := by
      apply Finset.sum_le_sum
      intro n hn
      have hnA := (Finset.mem_Ico.mp hn).1
      have hn' : (1: ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hn0 : 0 < (n: ℝ) := by linarith
      have hn1 : 0 < (n: ℝ) + 1 := by positivity
      dsimp only [Pareto.positiveWeight]
      field_simp
      nlinarith [mul_nonneg hn0.le (sub_nonneg.mpr hn')]
    _ = 2 * ∑ n ∈ Finset.range (B - A), Pareto.positiveWeight (n + A) := by
      rw [← Finset.mul_sum, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_comm A]
    _ ≤ 2 * ∑' n, Pareto.positiveWeight (n + A) := by
      gcongr
      exact ((summable_nat_add_iff A).mpr Pareto.positiveWeight_summable).sum_le_tsum _
        (fun n _ => Pareto.positiveWeight_nonneg _)
    _ = _ := by rw [Pareto.positiveWeight_tail_tsum A hA]; ring

/-- Each distinct LCM in a divisibility chain is at least twice its predecessor.
The conclusion is the true sub-eighth moment of the physical sequence. -/
theorem summable_rpow_of_doubling_eighth_blocks
    (L : ℕ → ℕ) (h0 : 0 < L 0) (hd : ∀ j, 2 * L j ≤ L (j + 1))
    (a : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j, (∑ n ∈ Finset.Ico (L j) (L (j + 1)), |a n| ^ 8 / (n: ℝ) ^ 2) ≤ B)
    {q : ℝ} (hq : 0 < q) (hq8 : q < 8) :
    Summable (fun n => |a n| ^ q / (n: ℝ) ^ 2) := by
  have hpow (j : ℕ) : 2 ^ j ≤ L j := by
    induction j with
    | zero => simp only [pow_zero]; omega
    | succ j ih => rw [pow_succ]; exact (by omega : 2 ^ j * 2 ≤ 2 * L j).trans (hd j)
  have hL (j : ℕ) : 0 < L j := (Nat.pow_pos (by decide) : 0 < 2 ^ j).trans_le (hpow j)
  have hmono : StrictMono L := strictMono_nat_of_lt_succ (fun j => by have := hd j; have := hL j; omega)
  have mass (j : ℕ) :
      (∑ n ∈ Finset.Ico (L j) (L (j + 1)), 1 / (n: ℝ) ^ 2) ≤ 2 * (1 / 2: ℝ) ^ j := by
    apply (reciprocal_square_block_mass _ _ (hL j)).trans
    have hh : (2: ℝ) ^ j ≤ (L j : ℝ) := by exact_mod_cast hpow j
    rw [div_pow, one_pow, ← mul_div_assoc, mul_one]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hh
  have h := summable_of_uniform_eighth_blocks L hmono
    (fun n => 1 / (n: ℝ) ^ 2) (fun n => |a n|) (fun _ => by positivity) (fun _ => abs_nonneg _)
    hB (by norm_num : (0: ℝ) ≤ 2) (by norm_num : (0: ℝ) ≤ 1 / 2) (by norm_num)
    (fun j => by simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using hb j) mass
    (t := q / 8) (by linarith) (by linarith)
  rw [show 8 * (q / 8)=q by ring] at h
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using h

/-- The user's actual least common multiples, after repeated endpoints have
been omitted. -/
theorem summable_rpow_of_lcm_eighth_blocks (M : ℕ → ℕ) (hM : Monotone M)
    (hstrict : StrictMono (fun j => (M j).lcmUpto))
    (a : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j, (∑ n ∈ Finset.Ico (M j).lcmUpto (M (j + 1)).lcmUpto,
      |a n| ^ 8 / (n: ℝ) ^ 2) ≤ B) {q : ℝ} (hq : 0 < q) (hq8 : q < 8) :
    Summable (fun n => |a n| ^ q / (n: ℝ) ^ 2) := by
  apply summable_rpow_of_doubling_eighth_blocks (fun j => (M j).lcmUpto)
    (Nat.lcmUpto_pos _) _ a hB hb hq hq8
  intro j
  have hdiv : (M j).lcmUpto ∣ (M (j + 1)).lcmUpto := by
    change (Finset.Icc 1 (M j)).lcm id ∣ (Finset.Icc 1 (M (j + 1))).lcm id
    apply Finset.lcm_dvd
    intro k hk
    apply Finset.dvd_lcm
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,
      (Finset.mem_Icc.mp hk).2.trans (hM (Nat.le_succ j))⟩
  obtain ⟨r, hr⟩ := hdiv
  have hlt := hstrict (Nat.lt_succ_self j)
  change (M j).lcmUpto < (M (j + 1)).lcmUpto at hlt
  rw [hr] at hlt ⊢
  have hr2 : 2 ≤ r := by
    by_contra! h
    have h' := Nat.mul_le_mul_left (M j).lcmUpto (show r ≤ 1 by omega)
    simp only [Nat.mul_one] at h'
    omega
  simpa only [Nat.mul_comm 2] using Nat.mul_le_mul_left (M j).lcmUpto hr2

end RiemannResearch.RH.QLcmShellMoment
