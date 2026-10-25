/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CRTTrigammaBounds
import RiemannResearch.Analysis.InverseSquareAbelTail

/-!
# Rational two-sided bounds for a complete progression tail

Source: Signed_Quadratic_Correction_Research_Note.pdf, equation (9.11).
The proof uses finite telescoping comparisons and a limit of the explicit
boundary term. There is no assumed integral estimate or asymptotic provider.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.ProgressionSquareTailBounds
open RiemannResearch.RH.CRTBlock RiemannResearch.Analysis.PeriodicWeightedMean

/-- Summability includes every term of the arithmetic progression. -/
theorem progression_summable (L : ℕ) (hL : 0 < L) {a : ℝ} (ha : 0 < a) :
    Summable (fun k : ℕ => 1 / (a + (k : ℝ) * L)^2) := by
  simpa only [mul_comm, add_comm] using
    progressionSquare_summable (show (0 : ℝ) < L by exact_mod_cast hL) ha

/-- The complete progression sum is between the integral-sized term and
that term plus the initial atom. -/
theorem progression_square_bounds (L : ℕ) (hL : 0 < L)
    {a : ℝ} (ha : 0 < a) :
    1 / ((L : ℝ) * a) ≤ (∑' k : ℕ, 1 / (a + (k : ℝ) * L)^2) ∧
    (∑' k : ℕ, 1 / (a + (k : ℝ) * L)^2) ≤
      1 / ((L : ℝ) * a) + 1 / a^2 := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (Nat.succ_le_iff.mpr hL)
  let u : ℕ → ℝ := fun n => 1 / (a + (n : ℝ) * L) / L
  have hstepLower (n : ℕ) :
      u n - u (n + 1) ≤ 1 / (a + (n : ℝ) * L)^2 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hx : 0 < a + (n : ℝ) * L := by positivity
    have hy : 0 < a + ((n : ℝ) + 1) * L := by positivity
    dsimp [u]
    push_cast
    field_simp
    nlinarith
  have hstepUpper (n : ℕ) :
      1 / (a + L + (n : ℝ) * L)^2 ≤ u n - u (n + 1) := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hx : 0 < a + (n : ℝ) * L := by positivity
    have hy : 0 < a + ((n : ℝ) + 1) * L := by positivity
    dsimp [u]
    push_cast
    have he : a + (L : ℝ) + (n : ℝ) * L = a + ((n : ℝ) + 1) * L := by ring
    rw [he]
    field_simp
    nlinarith
  have hs := progression_summable L hL ha
  constructor
  · have hsum (n : ℕ) :
        u 0 - u n ≤ ∑' k : ℕ, 1 / (a + (k : ℝ) * L)^2 := by
      calc
        _ = ∑ k ∈ Finset.range n, (u k - u (k + 1)) :=
          (telescoping_weights u n).symm
        _ ≤ ∑ k ∈ Finset.range n, 1 / (a + (k : ℝ) * L)^2 :=
          Finset.sum_le_sum (fun k _ => hstepLower k)
        _ ≤ _ := hs.sum_le_tsum _ (fun k _ => by positivity)
    have huinf : Filter.Tendsto (fun n : ℕ => a + (n : ℝ) * L)
        Filter.atTop Filter.atTop := by
      apply Filter.tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
      intro n
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    have hu : Filter.Tendsto u Filter.atTop (nhds 0) := by
      simpa only [zero_div] using (huinf.const_div_atTop 1).div_const (L : ℝ)
    have hb := le_of_tendsto' (hu.const_sub (u 0)) hsum
    simpa [u, div_div, div_eq_mul_inv, mul_comm] using hb
  · have hs' := progression_summable L hL (show 0 < a + L by positivity)
    have hb : (∑' k : ℕ, 1 / (a + L + (k : ℝ) * L)^2) ≤ u 0 := by
      apply hs'.tsum_le_of_sum_range_le
      intro n
      calc
        _ ≤ ∑ k ∈ Finset.range n, (u k - u (k + 1)) :=
          Finset.sum_le_sum (fun k _ => hstepUpper k)
        _ = u 0 - u n := telescoping_weights u n
        _ ≤ u 0 := by
          have hn : 0 ≤ u n := by dsimp [u]; positivity
          linarith
    have he := hs.tsum_eq_zero_add
    have hshift : (∑' k : ℕ, 1 / (a + ((k + 1 : ℕ) : ℝ) * L)^2) =
        ∑' k : ℕ, 1 / (a + L + (k : ℝ) * L)^2 := by
      apply tsum_congr
      intro k
      push_cast
      congr 2
      ring
    rw [hshift] at he
    simp only [Nat.cast_zero, zero_mul, add_zero] at he
    have hu0 : u 0 = 1 / ((L : ℝ) * a) := by simp [u, div_div, div_eq_mul_inv, mul_comm]
    rw [hu0] at hb
    linarith

/-- Equation (9.11), with arbitrary prefix length and the complete infinite tail. -/
theorem progression_square_tail_bounds (L M : ℕ) (hL : 0 < L)
    {a : ℝ} (ha : 0 < a) :
    1 / ((L : ℝ) * (a + (M : ℝ) * L)) ≤
        (∑' j : ℕ, 1 / (a + ((j + M : ℕ) : ℝ) * L)^2) ∧
    (∑' j : ℕ, 1 / (a + ((j + M : ℕ) : ℝ) * L)^2) ≤
      1 / ((L : ℝ) * (a + (M : ℝ) * L)) + 1 / (a + (M : ℝ) * L)^2 := by
  have h := progression_square_bounds L hL
    (show 0 < a + (M : ℝ) * L by positivity)
  simpa only [Nat.cast_add, add_mul, add_assoc, add_comm, add_left_comm] using h

end RiemannResearch.Analysis.ProgressionSquareTailBounds
