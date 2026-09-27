/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.DampedMobiusHalfHilbertRate
import RiemannResearch.Analysis.LogSquareTail

/-!
# Transfer of arbitrary logarithmic coordinate and head estimates

This module is an analytic transfer statement. Its inputs are an eventually
conductor-uniform coordinate envelope and an eventual finite-head estimate.
It has no new arithmetic assumption: an arithmetic application must supply
these hypotheses from the checked Mertens chain.

The logarithmic square kernel is retained in the physical tail, and the
remaining negative power is bounded at the physical split point. The extra
factor `(6 + log M)^(-1)` is discarded. This intentional loss makes the
transfer apply to every nonnegative real target norm exponent using just
the already established logarithmic square-tail lemma.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- A coordinate envelope with log exponent 1 bounds its weighted square
by the logarithmic 2 series. This algebraic comparison loses no log exponent. -/
theorem positiveWeight_sq_le_log_square
    {a K : ℝ} {n : ℕ} (hn : 0 < n) (_hK : 0 ≤ K)
    (ha : |a| ≤ K * Real.sqrt (n : ℝ) /
      (6 + Real.log (n : ℝ)) ^ (1 : ℝ)) :
    positiveWeight n * a ^ 2 ≤
      K ^ 2 * (1 / ((n : ℝ) *
        (6 + Real.log (n : ℝ)) ^ (2 : ℝ))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hL : 0 < 6 + Real.log (n : ℝ) := by
    have := Real.log_nonneg hn1
    linarith
  have hp : ((6 + Real.log (n : ℝ)) ^ (1 : ℝ)) ^ 2 =
      (6 + Real.log (n : ℝ)) ^ (2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    norm_num
  have hs := mul_self_le_mul_self (abs_nonneg a) ha
  have hsq : a ^ 2 ≤ K ^ 2 * (n : ℝ) /
      (6 + Real.log (n : ℝ)) ^ (2 : ℝ) := by
    simpa only [← pow_two, sq_abs, div_pow, mul_pow,
      Real.sq_sqrt hn0.le, hp] using hs
  have hpow : 0 < (6 + Real.log (n : ℝ)) ^ (2 : ℝ) := by positivity
  calc
    _ ≤ positiveWeight n * (K ^ 2 * (n : ℝ) /
        (6 + Real.log (n : ℝ)) ^ (2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hsq (positiveWeight_nonneg n)
    _ = K ^ 2 / (((n : ℝ) + 1) *
        (6 + Real.log (n : ℝ)) ^ (2 : ℝ)) := by
      unfold positiveWeight
      field_simp [hn0.ne', hpow.ne']
    _ ≤ K ^ 2 / ((n : ℝ) *
        (6 + Real.log (n : ℝ)) ^ (2 : ℝ)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _)
        (mul_pos hn0 hpow)
      nlinarith
    _ = _ := by ring



/-- The square-energy exponent is twice the norm exponent. -/
theorem norm_le_log_rpow_of_sq_le {E : Type*} [SeminormedAddGroup E]
    (v : E) {C L r : ℝ} (hC : 0 ≤ C) (hL : 0 < L)
    (h : ‖v‖ ^ 2 ≤ C * L ^ (-2 * r)) :
    ‖v‖ ≤ Real.sqrt C * L ^ (-r) := by
  have hp : (L ^ (-r)) ^ 2 = L ^ (-2 * r) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 1
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simpa only [mul_pow, Real.sq_sqrt hC, hp] using h

/-- An arbitrary eventual, conductor-uniform coordinate envelope and a
finite-head bound imply the corresponding eventual Hilbert norm rate.

The coordinate exponent is `r + 1` and the head square-energy exponent
is `2 * r`. The square-tail estimate in fact contains an extra inverse
logarithm, which is not needed for this conclusion. -/
theorem dampedMobius_half_cutoffs_eventual_log_rate_of_coordinate_and_head
    {r K D : ℝ} (hr : 0 ≤ r) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hbound : ∀ᶠ n : ℕ in atTop, ∀ M : ℕ,
      |hilbertSequence
        (arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M) n| ≤
      K * Real.sqrt (n : ℝ) * (6 + Real.log (n : ℝ)) ^ (-(r + 1)))
    (hhead : ∀ᶠ M : ℕ in atTop,
      (∑ n ∈ Finset.range M, positiveWeight n *
        (hilbertSequence
          (arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M -
            dampedMobiusHalfRangeLimit (1 / 2) le_rfl) n) ^ 2) ≤
      D * (6 + Real.log (M : ℝ)) ^ (-2 * r)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ M : ℕ in atTop,
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M -
        dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ≤
      C * (6 + Real.log (M : ℝ)) ^ (-r) := by
  let f := dampedMobiusHalfRangeLimit (1 / 2) le_rfl
  obtain ⟨hcoord, _hconv⟩ := dampedMobiusHalfRangeLimit_spec (1 / 2) le_rfl
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  have hfb (n : ℕ) (hn : N ≤ n) :
      |hilbertSequence f n| ≤
        K * Real.sqrt (n : ℝ) * (6 + Real.log (n : ℝ)) ^ (-(r + 1)) := by
    have ht : Tendsto (fun M =>
        hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M) n)
        atTop (𝓝 (hilbertSequence f n)) := by
      rw [show hilbertSequence f n = dampedMobiusPrefix (1 / 2) n -
        (n : ℝ) * (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re from hcoord n]
      exact dampedMobius_partial_coordinate_tendsto (by norm_num) n
    exact le_of_tendsto ht.abs (Eventually.of_forall (hN n hn))
  have hconstant : 0 ≤ D + 8 * K ^ 2 := by positivity
  refine ⟨Real.sqrt (D + 8 * K ^ 2), Real.sqrt_nonneg _, ?_⟩
  filter_upwards [hhead, eventually_ge_atTop N, eventually_ge_atTop (1 : ℕ)]
    with M hh hMN hM
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlogM : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hM1
  have hL : 0 < 6 + Real.log (M : ℝ) := by linarith
  have hL1 : 1 ≤ 6 + Real.log (M : ℝ) := by linarith
  let v := arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M - f
  let KM : ℝ := (2 * K) * (6 + Real.log (M : ℝ)) ^ (-r)
  have hKM : 0 ≤ KM := by dsimp [KM]; positivity
  let b : ℕ → ℝ := fun k => KM ^ 2 *
    (1 / (((k + M : ℕ) : ℝ) *
      (6 + Real.log ((k + M : ℕ) : ℝ)) ^ (2 : ℝ)))
  have hb : Summable b :=
    ((summable_nat_add_iff M).mpr summable_shifted_log_square).mul_left _
  have henv (k : ℕ) :
      positiveWeight (k + M) * (hilbertSequence v (k + M)) ^ 2 ≤ b k := by
    have hnk : 0 < k + M := by omega
    have hnN : N ≤ k + M := by omega
    have hlog : Real.log (M : ℝ) ≤ Real.log ((k + M : ℕ) : ℝ) :=
      Real.log_le_log hM0 (by exact_mod_cast (show M ≤ k + M by omega))
    have hLn : 0 < 6 + Real.log ((k + M : ℕ) : ℝ) := by linarith
    have hnegpow : (6 + Real.log ((k + M : ℕ) : ℝ)) ^ (-r) ≤
        (6 + Real.log (M : ℝ)) ^ (-r) :=
      Real.rpow_le_rpow_of_nonpos hL (by linarith) (neg_nonpos.mpr hr)
    have hfactor : (6 + Real.log ((k + M : ℕ) : ℝ)) ^ (-(r + 1)) =
        (6 + Real.log ((k + M : ℕ) : ℝ)) ^ (-r) /
          (6 + Real.log ((k + M : ℕ) : ℝ)) ^ (1 : ℝ) := by
      rw [show -(r + 1) = -r - 1 by ring, Real.rpow_sub hLn]
    apply positiveWeight_sq_le_log_square hnk hKM
    change |hilbertSequence
      (arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M - f) (k + M)| ≤ _
    rw [hilbertSequence_sub, Pi.sub_apply]
    calc
      _ ≤ |hilbertSequence
          (arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M) (k + M)| +
          |hilbertSequence f (k + M)| := abs_sub _ _
      _ ≤ K * Real.sqrt ((k + M : ℕ) : ℝ) *
            (6 + Real.log ((k + M : ℕ) : ℝ)) ^ (-(r + 1)) +
          K * Real.sqrt ((k + M : ℕ) : ℝ) *
            (6 + Real.log ((k + M : ℕ) : ℝ)) ^ (-(r + 1)) :=
        add_le_add (hN (k + M) hnN M) (hfb (k + M) hnN)
      _ = ((2 * K) * Real.sqrt ((k + M : ℕ) : ℝ) /
          (6 + Real.log ((k + M : ℕ) : ℝ)) ^ (1 : ℝ)) *
            (6 + Real.log ((k + M : ℕ) : ℝ)) ^ (-r) := by rw [hfactor]; ring
      _ ≤ ((2 * K) * Real.sqrt ((k + M : ℕ) : ℝ) /
          (6 + Real.log ((k + M : ℕ) : ℝ)) ^ (1 : ℝ)) *
            (6 + Real.log (M : ℝ)) ^ (-r) :=
        mul_le_mul_of_nonneg_left hnegpow (by positivity)
      _ = _ := by dsimp [KM]; ring
  have hpow : ((6 + Real.log (M : ℝ)) ^ (-r)) ^ 2 =
      (6 + Real.log (M : ℝ)) ^ (-2 * r) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 1
    ring
  have hnegone : (6 + Real.log (M : ℝ)) ^ (-1 : ℝ) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (-1 : ℝ) ≤ 0))
  have ht : (∑' k, b k) ≤
      8 * K ^ 2 * (6 + Real.log (M : ℝ)) ^ (-2 * r) := by
    dsimp [b]
    rw [tsum_mul_left]
    have h := mul_le_mul_of_nonneg_left (log_power_tail_square hM) (sq_nonneg KM)
    calc
      _ ≤ KM ^ 2 * (2 * (6 + Real.log (M : ℝ)) ^ (-1 : ℝ)) := by
        simpa only [neg_div] using h
      _ = (2 * KM ^ 2) * (6 + Real.log (M : ℝ)) ^ (-1 : ℝ) := by ring
      _ ≤ (2 * KM ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hnegone (by positivity)
      _ = _ := by dsimp [KM]; rw [mul_pow, hpow]; ring
  have hs := pareto_norm_sq_le_head_add_tail v M b
    (D * (6 + Real.log (M : ℝ)) ^ (-2 * r))
    (8 * K ^ 2 * (6 + Real.log (M : ℝ)) ^ (-2 * r)) hb hh henv ht
  have hs' : ‖v‖ ^ 2 ≤
      (D + 8 * K ^ 2) * (6 + Real.log (M : ℝ)) ^ (-2 * r) := by
    calc
      _ ≤ _ := hs
      _ = _ := by ring
  exact norm_le_log_rpow_of_sq_le v hconstant hL hs'

end RiemannResearch.RH.Pareto
