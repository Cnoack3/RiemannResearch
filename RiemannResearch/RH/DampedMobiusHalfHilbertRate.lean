/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.DampedMobiusUniformHalfRange
import RiemannResearch.Analysis.LogPowerTail

/-!
# Quantitative half-damped Hilbert convergence

This module retains the original explicit quarter-logarithmic estimate.
`DampedMobiusHalfHilbertAllLogRates` strengthens it to every fixed real
logarithmic exponent, using the iterated unconditional Mertens provider.
`DampedMobiusHalfHilbertLoglogStretchedRate` now retains the full MediumPNT
saving and proves C*exp(-a*(L*log L)^(1/11)), L=6+log(M+1), with a>0.
Both strengthen the complete Hilbert error, including its physical head.

The checked finite head has squared error at most a constant times
(6 + log M)^(-3). The conductor-uniform coordinate envelope gives a
physical tail of order (6 + log M)^(-1/2) in squared norm. The complete
norm therefore has the unconditional quarter-logarithmic rate.
All cutoffs, including finitely many small ones, share one constant.
This rate alone proves no fixed subhalf finite-energy statement.

Source: the existing repository endpoint and signed density-tail
providers, with elementary quantitative integral comparison. No
mathematical novelty claim is made.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- A coordinate envelope with log exponent 3/4 bounds its weighted square
by the logarithmic 3/2 series. This algebraic comparison loses no log exponent. -/
theorem positiveWeight_sq_le_log_threeHalves
    {a K : ℝ} {n : ℕ} (hn : 0 < n) (_hK : 0 ≤ K)
    (ha : |a| ≤ K * Real.sqrt (n : ℝ) /
      (6 + Real.log (n : ℝ)) ^ (3 / 4 : ℝ)) :
    positiveWeight n * a ^ 2 ≤
      K ^ 2 * (1 / ((n : ℝ) *
        (6 + Real.log (n : ℝ)) ^ (3 / 2 : ℝ))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hL : 0 < 6 + Real.log (n : ℝ) := by
    have := Real.log_nonneg hn1
    linarith
  have hp : ((6 + Real.log (n : ℝ)) ^ (3 / 4 : ℝ)) ^ 2 =
      (6 + Real.log (n : ℝ)) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    norm_num
  have hs := mul_self_le_mul_self (abs_nonneg a) ha
  have hsq : a ^ 2 ≤ K ^ 2 * (n : ℝ) /
      (6 + Real.log (n : ℝ)) ^ (3 / 2 : ℝ) := by
    simpa only [← pow_two, sq_abs, div_pow, mul_pow,
      Real.sq_sqrt hn0.le, hp] using hs
  have hpow : 0 < (6 + Real.log (n : ℝ)) ^ (3 / 2 : ℝ) := by positivity
  calc
    _ ≤ positiveWeight n * (K ^ 2 * (n : ℝ) /
        (6 + Real.log (n : ℝ)) ^ (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hsq (positiveWeight_nonneg n)
    _ = K ^ 2 / (((n : ℝ) + 1) *
        (6 + Real.log (n : ℝ)) ^ (3 / 2 : ℝ)) := by
      unfold positiveWeight
      field_simp [hn0.ne', hpow.ne']
    _ ≤ K ^ 2 / ((n : ℝ) *
        (6 + Real.log (n : ℝ)) ^ (3 / 2 : ℝ)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _)
        (mul_pos hn0 hpow)
      nlinarith
    _ = _ := by ring

/-- Head plus tail is an exact split of the full Pareto norm. A bound only
on the physical tail cannot replace the head premise here. -/
theorem pareto_norm_sq_le_head_add_tail
    (v : ThresholdHilbert) (M : ℕ) (b : ℕ → ℝ) (A B : ℝ)
    (hb : Summable b)
    (hhead : (∑ n ∈ Finset.range M,
      positiveWeight n * (hilbertSequence v n) ^ 2) ≤ A)
    (henv : ∀ k : ℕ,
      positiveWeight (k + M) * (hilbertSequence v (k + M)) ^ 2 ≤ b k)
    (htail : (∑' k : ℕ, b k) ≤ B) :
    ‖v‖ ^ 2 ≤ A + B := by
  have hs := hilbertSequence_square_summable v
  rw [hilbert_norm_weighted_sq, ← hs.sum_add_tsum_nat_add M]
  apply add_le_add hhead
  exact (Summable.tsum_le_tsum henv ((summable_nat_add_iff M).mpr hs) hb).trans htail

/-- Converting a square-energy rate to a norm rate exactly halves the
logarithmic exponent. -/
private theorem norm_le_log_quarter_of_sq_le {E : Type*} [SeminormedAddGroup E]
    (v : E) {C L : ℝ} (hC : 0 ≤ C) (hL : 0 < L)
    (h : ‖v‖ ^ 2 ≤ C * L ^ (-1 / 2 : ℝ)) :
    ‖v‖ ≤ Real.sqrt C * L ^ (-1 / 4 : ℝ) := by
  have hp : (L ^ (-1 / 4 : ℝ)) ^ 2 = L ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    norm_num
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simpa only [mul_pow, Real.sq_sqrt hC, hp] using h

/-- Quantitative endpoint convergence. The full finite physical head is
bounded by L(M)^(-3); the remaining infinite physical tail is bounded by
L(M)^(-1/2) in square energy. Thus the actual norm rate is L(M)^(-1/4).
All arithmetic premises have checked unconditional providers. -/
theorem dampedMobius_half_cutoffs_eventual_log_rate :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ M : ℕ in atTop,
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M -
        dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ≤
        C * (6 + Real.log (M : ℝ)) ^ (-1 / 4 : ℝ) := by
  let f := dampedMobiusHalfRangeLimit (1 / 2) le_rfl
  obtain ⟨hcoord, hconv⟩ := dampedMobiusHalfRangeLimit_spec (1 / 2) le_rfl
  obtain ⟨K, hK, hbound⟩ := dampedMobius_half_partial_uniform_log_bound
  obtain ⟨D, hD, hhead⟩ := dampedMobius_half_head_error_log_bound
  have hfb (n : ℕ) (hn : 0 < n) (hl : 200 ≤ Real.log (n : ℝ)) :
      |hilbertSequence f n| ≤ K * Real.sqrt (n : ℝ) /
        (6 + Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := by
    have ht : Tendsto (fun M =>
        hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M) n)
        atTop (𝓝 (hilbertSequence f n)) := by
      rw [show hilbertSequence f n = dampedMobiusPrefix (1 / 2) n -
        (n : ℝ) * (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re from hcoord n]
      exact dampedMobius_partial_coordinate_tendsto (by norm_num) n
    exact le_of_tendsto ht.abs (Eventually.of_forall (fun M => hbound M n hn hl))
  have hconstant : 0 ≤ D + 12 * K ^ 2 := by positivity
  refine ⟨Real.sqrt (D + 12 * K ^ 2), Real.sqrt_nonneg _, ?_⟩
  have hlog : Tendsto (fun M : ℕ => Real.log (M : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop (200 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with M hMl hM
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hL : 0 < 6 + Real.log (M : ℝ) := by linarith
  have hL1 : 1 ≤ 6 + Real.log (M : ℝ) := by linarith
  let v := arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M - f
  let b : ℕ → ℝ := fun k => (2 * K) ^ 2 *
    (1 / (((k + M : ℕ) : ℝ) *
      (6 + Real.log ((k + M : ℕ) : ℝ)) ^ (3 / 2 : ℝ)))
  have hb : Summable b :=
    ((summable_nat_add_iff M).mpr summable_shifted_log_threeHalves).mul_left _
  have henv (k : ℕ) :
      positiveWeight (k + M) * (hilbertSequence v (k + M)) ^ 2 ≤ b k := by
    have hnk : 0 < k + M := by omega
    have hlk : 200 ≤ Real.log ((k + M : ℕ) : ℝ) :=
      hMl.trans (Real.log_le_log hM0 (by exact_mod_cast (show M ≤ k + M by omega)))
    apply positiveWeight_sq_le_log_threeHalves hnk (by positivity : 0 ≤ 2 * K)
    change |hilbertSequence
      (arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M - f) (k + M)| ≤ _
    rw [hilbertSequence_sub, Pi.sub_apply]
    calc
      _ ≤ |hilbertSequence
          (arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M) (k + M)| +
          |hilbertSequence f (k + M)| := abs_sub _ _
      _ ≤ K * Real.sqrt ((k + M : ℕ) : ℝ) /
          (6 + Real.log ((k + M : ℕ) : ℝ)) ^ (3 / 4 : ℝ) +
          K * Real.sqrt ((k + M : ℕ) : ℝ) /
          (6 + Real.log ((k + M : ℕ) : ℝ)) ^ (3 / 4 : ℝ) :=
        add_le_add (hbound M (k + M) hnk hlk) (hfb (k + M) hnk hlk)
      _ = _ := by ring
  have ht : (∑' k, b k) ≤
      12 * K ^ 2 * (6 + Real.log (M : ℝ)) ^ (-1 / 2 : ℝ) := by
    dsimp [b]
    rw [tsum_mul_left]
    have h := mul_le_mul_of_nonneg_left
      (log_power_tail_threeHalves hM) (sq_nonneg (2 * K))
    calc
      _ ≤ (2 * K) ^ 2 * (3 *
          (6 + Real.log (M : ℝ)) ^ (-1 / 2 : ℝ)) := by
        simpa only [neg_div] using h
      _ = _ := by ring
  have hh : (∑ n ∈ Finset.range M,
      positiveWeight n * (hilbertSequence v n) ^ 2) ≤
      D * (6 + Real.log (M : ℝ)) ^ (-3 : ℝ) := by
    simpa only [v, f, hilbertSequence_sub, Pi.sub_apply, hcoord]
      using hhead M M le_rfl hM
  have hs := pareto_norm_sq_le_head_add_tail v M b
    (D * (6 + Real.log (M : ℝ)) ^ (-3 : ℝ))
    (12 * K ^ 2 * (6 + Real.log (M : ℝ)) ^ (-1 / 2 : ℝ)) hb hh henv ht
  have hpow : (6 + Real.log (M : ℝ)) ^ (-3 : ℝ) ≤
      (6 + Real.log (M : ℝ)) ^ (-1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hs' : ‖v‖ ^ 2 ≤
      (D + 12 * K ^ 2) * (6 + Real.log (M : ℝ)) ^ (-1 / 2 : ℝ) := by
    calc
      _ ≤ _ := hs
      _ ≤ D * (6 + Real.log (M : ℝ)) ^ (-1 / 2 : ℝ) +
          12 * K ^ 2 * (6 + Real.log (M : ℝ)) ^ (-1 / 2 : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hpow hD) le_rfl
      _ = _ := by ring
  exact norm_le_log_quarter_of_sq_le v hconstant hL hs'

private theorem shifted_log_quarter_succ_bound {M : ℕ} (hM : 1 ≤ M) :
    (6 + Real.log (M : ℝ)) ^ (-1 / 4 : ℝ) ≤
      2 * (6 + Real.log ((M + 1 : ℕ) : ℝ)) ^ (-1 / 4 : ℝ) := by
  have hm0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog0 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hm1
  have hlog1 : 0 ≤ Real.log ((M + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ M + 1 by omega))
  have hL0 : 0 < 6 + Real.log (M : ℝ) := by linarith
  have hL1 : 0 < 6 + Real.log ((M + 1 : ℕ) : ℝ) := by linarith
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog : Real.log ((M + 1 : ℕ) : ℝ) ≤ 1 + Real.log (M : ℝ) := by
    calc
      _ ≤ Real.log (2 * (M : ℝ)) :=
        Real.log_le_log (by positivity) (by push_cast; linarith)
      _ = Real.log 2 + Real.log (M : ℝ) :=
        Real.log_mul (by norm_num) hm0.ne'
      _ ≤ _ := by linarith
  have hLle : 6 + Real.log ((M + 1 : ℕ) : ℝ) ≤
      2 * (6 + Real.log (M : ℝ)) := by linarith
  have hpow : (6 + Real.log ((M + 1 : ℕ) : ℝ)) ^ (1 / 4 : ℝ) ≤
      2 * (6 + Real.log (M : ℝ)) ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ (2 * (6 + Real.log (M : ℝ))) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow hL1.le hLle (by norm_num)
      _ = (2 : ℝ) ^ (1 / 4 : ℝ) *
          (6 + Real.log (M : ℝ)) ^ (1 / 4 : ℝ) :=
        Real.mul_rpow (by norm_num) hL0.le
      _ ≤ 2 * (6 + Real.log (M : ℝ)) ^ (1 / 4 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa using Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 / 4 : ℝ) ≤ 1)
  rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by ring,
    Real.rpow_neg hL0.le, Real.rpow_neg hL1.le]
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div]
  exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hpow)

/-- The quantitative endpoint rate, normalized at log(M+1) and valid for
every conductor cutoff. Finitely many initial cutoffs only enlarge C. -/
theorem dampedMobius_half_cutoffs_log_rate :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ,
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M -
        dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ≤
        C * (6 + Real.log ((M + 1 : ℕ) : ℝ)) ^ (-1 / 4 : ℝ) := by
  obtain ⟨C, hC, hrate⟩ := dampedMobius_half_cutoffs_eventual_log_rate
  let E : ℕ → ℝ := fun M =>
    ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M -
      dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖
  let r : ℕ → ℝ := fun M =>
    (6 + Real.log ((M + 1 : ℕ) : ℝ)) ^ (-1 / 4 : ℝ)
  have hE (M : ℕ) : 0 ≤ E M := norm_nonneg _
  have hr (M : ℕ) : 0 < r M := by
    apply Real.rpow_pos_of_pos
    have hlog := Real.log_nonneg (by exact_mod_cast (show 1 ≤ M + 1 by omega) :
      (1 : ℝ) ≤ ((M + 1 : ℕ) : ℝ))
    linarith
  have hevent : ∀ᶠ M : ℕ in atTop, E M ≤ (2 * C) * r M := by
    filter_upwards [hrate, eventually_ge_atTop (1 : ℕ)] with M hMr hM
    calc
      _ ≤ C * (6 + Real.log (M : ℝ)) ^ (-1 / 4 : ℝ) := hMr
      _ ≤ C * (2 * r M) :=
        mul_le_mul_of_nonneg_left (shifted_log_quarter_succ_bound hM) hC
      _ = _ := by ring
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let S := ∑ k ∈ Finset.range N, E k / r k
  have hS : 0 ≤ S := Finset.sum_nonneg (fun k _ => div_nonneg (hE k) (hr k).le)
  refine ⟨2 * C + S, by positivity, ?_⟩
  intro M
  by_cases hMN : M < N
  · have hsingle : E M / r M ≤ S :=
      Finset.single_le_sum (fun k _ => div_nonneg (hE k) (hr k).le)
        (Finset.mem_range.mpr hMN)
    have hratio : E M / r M ≤ 2 * C + S := hsingle.trans (by linarith)
    exact (div_le_iff₀ (hr M)).mp hratio
  · exact (hN M (by omega)).trans
      (mul_le_mul_of_nonneg_right (by linarith : 2 * C ≤ 2 * C + S) (hr M).le)

end RiemannResearch.RH.Pareto
