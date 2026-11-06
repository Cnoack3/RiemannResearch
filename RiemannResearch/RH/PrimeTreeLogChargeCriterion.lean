/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QChargeDilation
import RiemannResearch.RH.QCofinalDisplacementMoments
import RiemannResearch.Analysis.PositiveWeightedPrefix
import Mathlib.Analysis.Complex.Exponential
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Logarithmically weighted one-sided charges force projection agreement

A summable logarithmically weighted adverse charge is enough. The proof
keeps the physical remainder row and uses its two pointwise bounds before
invoking the established one-sided harmonic residual criterion.
Source: the user's request to connect the arithmetic charges of the matched
projection displacement to a direct proof of projection agreement.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.PrimeTreeLogChargeCriterion
open Pareto ZetaTwoHilbert QSquarefreeDisplacementRigidity ArithmeticCumulative

private def logSize (n : ℕ) : ℝ := 1 + Real.log (n : ℝ)

private theorem logSize_one_le (n : ℕ) : 1 ≤ logSize n := by
  by_cases hn : n = 0
  · simp [hn, logSize]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    dsimp [logSize]
    linarith [Real.log_nonneg hn1]

private theorem logSize_mono {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    logSize m ≤ logSize n := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  exact add_le_add le_rfl (Real.log_le_log hmR hmnR)

private def expConstant (B : ℕ) : ℝ := Real.exp 1 * (B.factorial : ℝ)

private theorem expConstant_one_le (B : ℕ) : 1 ≤ expConstant B := by
  have h := Real.pow_div_factorial_le_exp 1 (by norm_num : (0 : ℝ) ≤ 1) B
  have hf : (0 : ℝ) < B.factorial := by exact_mod_cast Nat.factorial_pos B
  have h' := (div_le_iff₀ hf).mp h
  simpa [expConstant] using h'

/-- Exact conductors below the site cost at most one; conductors above it
cost n/m. These two regimes give a uniform logarithmic row estimate. -/
private theorem logarithmic_remainder_bound (B n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    logSize m ^ B * residueFraction m n ≤ expConstant B * logSize n ^ B := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hln : 0 ≤ logSize n := zero_le_one.trans (logSize_one_le n)
  have hlm : 0 ≤ logSize m := zero_le_one.trans (logSize_one_le m)
  have hres0 : 0 ≤ residueFraction m n := div_nonneg (Nat.cast_nonneg _) hmR.le
  by_cases hmn : m ≤ n
  · have hr : residueFraction m n ≤ 1 := by
      apply (div_le_one hmR).mpr
      exact_mod_cast (Nat.mod_lt n hm).le
    calc
      _ ≤ logSize m ^ B := mul_le_of_le_one_right (pow_nonneg hlm B) hr
      _ ≤ logSize n ^ B := pow_le_pow_left₀ hlm (logSize_mono hm hmn) B
      _ ≤ _ := le_mul_of_one_le_left (pow_nonneg hln B) (expConstant_one_le B)
  · have hnm : n < m := lt_of_not_ge hmn
    have hnmR : (n : ℝ) < m := by exact_mod_cast hnm
    let q : ℝ := (m : ℝ) / n
    have hq1 : 1 ≤ q := (one_le_div hnR).mpr hnmR.le
    have hq0 : 0 < q := zero_lt_one.trans_le hq1
    have hqlog := Real.log_nonneg hq1
    have hsplit : logSize m = logSize n + Real.log q := by
      dsimp [logSize, q]
      rw [Real.log_div hmR.ne' hnR.ne']
      ring
    have hprod : logSize m ≤ logSize n * (1 + Real.log q) := by
      rw [hsplit]
      nlinarith [mul_nonneg (sub_nonneg.mpr (logSize_one_le n)) hqlog]
    have hpow : (1 + Real.log q) ^ B ≤ expConstant B * q := by
      have h := Real.pow_div_factorial_le_exp (1 + Real.log q)
        (by linarith : 0 ≤ 1 + Real.log q) B
      have hf : (0 : ℝ) < B.factorial := by exact_mod_cast Nat.factorial_pos B
      have h' := (div_le_iff₀ hf).mp h
      rw [Real.exp_add, Real.exp_log hq0] at h'
      simpa only [expConstant, mul_assoc, mul_left_comm, mul_comm] using h'
    rw [residueFraction, Nat.mod_eq_of_lt hnm]
    calc
      _ ≤ (logSize n * (1 + Real.log q)) ^ B * ((n : ℝ) / m) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlm hprod B) (div_nonneg hnR.le hmR.le)
      _ = logSize n ^ B * ((1 + Real.log q) ^ B) * ((n : ℝ) / m) := by rw [mul_pow]
      _ ≤ logSize n ^ B * (expConstant B * q) * ((n : ℝ) / m) := by
        gcongr
      _ = _ := by dsimp [q]; field_simp [hmR.ne', hnR.ne']

/-- The actual physical upper bound follows from the weighted adverse sum.
The hypothesis concerns the positive part of the signed charge itself. -/
theorem oneSided_polylog_of_logWeighted (f : QHilbert) (σ : ℝ) (B : ℕ)
    (h : Summable (fun m : ℕ =>
      max (-(σ * mobiusDifference m (qSequence f))) 0 / (1 + Real.log (m : ℝ)) ^ B)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      σ * qSequence f n ≤ C * (1 + Real.log (n : ℝ)) ^ B := by
  let w (m : ℕ) := max (-(σ * mobiusDifference m (qSequence f))) 0 / logSize m ^ B
  have hw (m : ℕ) : 0 ≤ w m :=
    div_nonneg (le_max_right _ _) (pow_nonneg (zero_le_one.trans (logSize_one_le m)) B)
  let S := ∑' m, w m
  have hS : 0 ≤ S := tsum_nonneg hw
  refine ⟨expConstant B * S, mul_nonneg (zero_le_one.trans (expConstant_one_le B)) hS, ?_⟩
  intro n hn
  apply QChargeDilation.oneSided_le_of_charge_rows
  intro H
  calc
    _ = ∑ m ∈ Finset.Icc 1 H, w m * (logSize m ^ B * residueFraction m n) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hl : logSize m ≠ 0 := ne_of_gt (zero_lt_one.trans_le (logSize_one_le m))
      dsimp [w]
      field_simp [hl]
    _ ≤ ∑ m ∈ Finset.Icc 1 H, w m * (expConstant B * logSize n ^ B) := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_left
        (logarithmic_remainder_bound B n m hn (Finset.mem_Icc.mp hm).1) (hw m)
    _ = (∑ m ∈ Finset.Icc 1 H, w m) * (expConstant B * logSize n ^ B) := by rw [Finset.sum_mul]
    _ ≤ S * (expConstant B * logSize n ^ B) := by
      apply mul_le_mul_of_nonneg_right (h.sum_le_tsum _ (fun m _ => hw m))
      exact mul_nonneg (zero_le_one.trans (expConstant_one_le B))
        (pow_nonneg (zero_le_one.trans (logSize_one_le n)) B)
    _ = _ := by dsimp [logSize]; ring

/-- A one-sided polylog bound on physical displacement already forces the
faithful residual, hence the matched displacement, to be exactly zero. -/
theorem displacement_eq_zero_of_oneSided_polylog (σ C : ℝ) (B : ℕ)
    (hσ : |σ| = 1) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, 0 < n → σ * qSequence displacement n ≤
      C * (1 + Real.log (n : ℝ)) ^ B) : displacement = 0 := by
  apply displacement_eq_zero_of_residual_eq_zero
  apply residual_zero_iff_cofinal_harmonic_polylog.mpr
  refine ⟨(B + 1 : ℕ), C * (2 : ℝ) ^ (B + 1), by positivity, by positivity, ?_⟩
  apply Filter.Eventually.frequently
  have ht : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (1 : ℝ))] with X hX
  have hmin : minimumHarmonicPrefix X ≤ harmonicSide σ X := by
    rcases le_total 0 σ with hs | hs
    · have he : σ = 1 := (abs_of_nonneg hs).symm.trans hσ
      rw [he]
      exact min_le_left _ _
    · rw [abs_of_nonpos hs] at hσ
      have he : σ = -1 := by linarith
      rw [he]
      exact min_le_right _ _
  have hh : (∑ n ∈ Finset.range (X + 1), (1 : ℝ) / (n : ℝ)) = (harmonic X : ℝ) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, div_zero, add_zero, harmonic, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast, one_div]
  calc
    minimumHarmonicPrefix X ≤ harmonicSide σ X := hmin
    _ ≤ ∑ n ∈ Finset.range (X + 1), (C * (1 + Real.log (X : ℝ)) ^ B) / (n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hn0 : n = 0
      · simp [hn0]
      have hnpos := Nat.pos_of_ne_zero hn0
      have hnX : n ≤ X := by have := Finset.mem_range.mp hn; omega
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      apply max_le
      · exact (h n hnpos).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (zero_le_one.trans (logSize_one_le n))
            (logSize_mono hnpos hnX) B) hC)
      · positivity
    _ = C * (1 + Real.log (X : ℝ)) ^ B * (harmonic X : ℝ) := by
      rw [← hh, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ C * (1 + Real.log (X : ℝ)) ^ B * (1 + Real.log (X : ℝ)) :=
      mul_le_mul_of_nonneg_left (harmonic_le_one_add_log X) (by positivity)
    _ = C * (1 + Real.log (X : ℝ)) ^ (B+1) := by rw [pow_succ]; ring
    _ ≤ C * (2 * Real.log (X : ℝ)) ^ (B+1) := by gcongr; linarith
    _ = _ := by rw [Real.rpow_natCast, mul_pow]; ring

/-- The direct projection-agreement criterion uses only one sign of the
logarithmically weighted charges, and no converse approximation theorem. -/
theorem displacement_eq_zero_of_logWeighted_charges (σ : ℝ) (B : ℕ) (hσ : |σ| = 1)
    (h : Summable (fun m : ℕ =>
      max (-(σ * mobiusDifference m (qSequence displacement))) 0 /
        (1 + Real.log (m : ℝ)) ^ B)) : displacement = 0 := by
  obtain ⟨C, hC, hb⟩ := oneSided_polylog_of_logWeighted displacement σ B h
  exact displacement_eq_zero_of_oneSided_polylog σ C B hσ hC hb


private theorem shifted_range_sum (a : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, a (k+1)) = ∑ m ∈ Finset.Icc 1 N, a m := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]

/-- Every nonnegative polylogarithmic prefix bound gives a summable sequence
once one more logarithmic power is inserted into the denominator. -/
theorem logWeighted_summable_of_polylog_prefix (a : ℕ → ℝ) (B : ℕ) (C : ℝ)
    (ha : ∀ n : ℕ, 0 < n → 0 ≤ a n) (hC : 0 ≤ C)
    (hbound : ∀ H : ℕ, (∑ m ∈ Finset.Icc 1 H, a m) ≤
      C * (1 + Real.log (H : ℝ)) ^ B) :
    Summable (fun m : ℕ => a m / (1 + Real.log (m : ℝ)) ^ (B+1)) := by
  let w (n : ℕ) : ℝ := (logSize (n+1))⁻¹
  have hpos (n : ℕ) : 0 < logSize (n+1) := zero_lt_one.trans_le (logSize_one_le _)
  have hw (n : ℕ) : 0 ≤ w n := inv_nonneg.mpr (hpos n).le
  have hw1 (n : ℕ) : w n ≤ 1 := by
    simpa only [one_div, inv_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (logSize_one_le (n+1))
  have hanti : Antitone w := by
    intro m n hmn
    simpa only [one_div] using one_div_le_one_div_of_le (hpos m)
      (logSize_mono (by omega : 0 < m+1) (Nat.add_le_add_right hmn 1))
  have hp (n : ℕ) : (∑ k ∈ Finset.range (n+1), a (k+1)) * w n ^ B ≤ C := by
    rw [shifted_range_sum]
    have hb : (∑ m ∈ Finset.Icc 1 (n+1), a m) ≤ C * logSize (n+1) ^ B := hbound (n+1)
    have hh := mul_le_mul_of_nonneg_right hb (pow_nonneg (hw n) B)
    simpa only [w, inv_pow, mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero B (hpos n).ne'), mul_one] using hh
  have hs := RiemannResearch.Analysis.summable_weighted_of_prefix_bound
    (fun n => a (n+1)) w B C (fun n => ha (n+1) (by omega)) hw hw1 hanti hC hp
  apply (summable_nat_add_iff 1).mp
  simpa only [w, logSize, inv_pow, div_eq_mul_inv] using hs

/-- A polynomial logarithmic bound for one side of the actual charge mass
forces exact agreement of the two matched projections. -/
theorem displacement_eq_zero_of_polylog_charge_prefix (σ C : ℝ) (B : ℕ)
    (hσ : |σ| = 1) (hC : 0 ≤ C)
    (hbound : ∀ H : ℕ, (∑ m ∈ Finset.Icc 1 H,
      max (-(σ * mobiusDifference m (qSequence displacement))) 0) ≤
        C * (1 + Real.log (H : ℝ)) ^ B) : displacement = 0 := by
  have hs := logWeighted_summable_of_polylog_prefix
    (fun m => max (-(σ * mobiusDifference m (qSequence displacement))) 0) B C
    (fun _ _ => le_max_right _ _) hC hbound
  exact displacement_eq_zero_of_logWeighted_charges σ (B+1) hσ hs


/-- If the matched projections differ, neither choice of charge sign can
satisfy a fixed polylogarithmic cumulative bound. -/
theorem no_polylog_charge_prefix_of_displacement_ne_zero
    (hd : displacement ≠ 0) (σ : ℝ) (B : ℕ) (hσ : |σ| = 1) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℕ, (∑ m ∈ Finset.Icc 1 H,
      max (-(σ * mobiusDifference m (qSequence displacement))) 0) ≤
        C * (1 + Real.log (H : ℝ)) ^ B := by
  rintro ⟨C, hC, hb⟩
  exact hd (displacement_eq_zero_of_polylog_charge_prefix σ C B hσ hC hb)

end RiemannResearch.RH.PrimeTreeLogChargeCriterion
