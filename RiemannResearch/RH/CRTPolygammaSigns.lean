/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CRTExactDigamma
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# All positive-axis polygamma signs, for actual derivatives of digamma

Order m+1 has sign (-1)^m. In particular trigamma is positive and
its derivative is negative. No sign for digamma itself is presumed.
-/

open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.CRTBlock
noncomputable section

def reciprocalPowerSeries (m : ℕ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, 1 / ((k : ℝ) + x)^(m + 2)

theorem reciprocalPowerSeries_summable (m : ℕ) {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ => 1 / ((k : ℝ) + x)^(m + 2)) := by
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_nonneg_of_le (f := fun k : ℕ => 1 / ((k : ℝ) + (x + 1))^2)
    (fun k => by positivity)
  · intro k
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show (k : ℝ) + 1 + x = (k : ℝ) + (x + 1) by ring]
    apply one_div_le_one_div_of_le (by positivity)
    apply pow_le_pow_right₀
    · have hk := Nat.cast_nonneg k (α := ℝ)
      linarith
    · omega
  · exact reciprocalSquareSeries_summable_pos (by linarith)

theorem reciprocalPowerSeries_pos (m : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < reciprocalPowerSeries m x := by
  exact (reciprocalPowerSeries_summable m hx).tsum_pos
    (fun k => by positivity) 0 (by positivity)

theorem hasDerivAt_reciprocalPowerSeries (m : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (reciprocalPowerSeries m)
      (-((m + 2 : ℕ) : ℝ) * reciprocalPowerSeries (m + 1) x) x := by
  let g : ℕ → ℝ → ℝ := fun k y => 1 / ((k : ℝ) + y)^(m + 2)
  let g' : ℕ → ℝ → ℝ := fun k y =>
    -((m + 2 : ℕ) : ℝ) * (1 / ((k : ℝ) + y)^(m + 3))
  let u : ℕ → ℝ := fun k =>
    ((m + 2 : ℕ) : ℝ) * (1 / ((k : ℝ) + x / 2)^(m + 3))
  have hhalf : 0 < x / 2 := by positivity
  have hu : Summable u := by
    simpa only [u, Nat.add_assoc] using
      (reciprocalPowerSeries_summable (m + 1) hhalf).mul_left ((m + 2 : ℕ) : ℝ)
  have hg (k : ℕ) (y : ℝ) (hy : y ∈ Set.Ioi (x / 2)) :
      HasDerivAt (g k) (g' k y) y := by
    have hy0 : 0 < y := lt_trans hhalf hy
    have hn : (k : ℝ) + y ≠ 0 := by positivity
    have hd := ((((hasDerivAt_id y).const_add (k : ℝ)).inv hn).pow (m + 2))
    convert hd using 1 <;> try rfl
    · funext z
      simp [g, one_div, Function.comp_def, inv_pow]
    · dsimp [g']
      simp only [show m + 2 - 1 = m + 1 by omega, id_eq, one_mul, inv_pow]
      simp only [pow_add, pow_one]
      field_simp
      <;> ring
  have hb (k : ℕ) (y : ℝ) (hy : y ∈ Set.Ioi (x / 2)) : ‖g' k y‖ ≤ u k := by
    have hy0 : 0 < y := lt_trans hhalf hy
    dsimp only [g', u]
    rw [norm_mul, norm_neg, Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply one_div_le_one_div_of_le (by positivity)
    have hxy : x / 2 < y := hy
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have h := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi
    (convex_Ioi (x / 2)).isPreconnected hg hb
    (show x ∈ Set.Ioi (x / 2) by change x/2 < x; linarith)
    (reciprocalPowerSeries_summable m hx)
    (show x ∈ Set.Ioi (x / 2) by change x/2 < x; linarith)
  convert h using 1 <;> try rfl
  simp only [g', tsum_mul_left, reciprocalPowerSeries, Nat.add_assoc]

/-- The full classical series formula, identified with actual iterated derivatives. -/
theorem iteratedDeriv_digamma_series (m : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv (m + 1) realDigamma x =
      (-1 : ℝ)^m * ((m + 1).factorial : ℝ) * reciprocalPowerSeries m x := by
  induction m generalizing x with
  | zero =>
    simp only [Nat.zero_add, pow_zero, Nat.factorial_one, Nat.cast_one,
      one_mul, iteratedDeriv_one]
    exact (hasDerivAt_re_digamma_pos hx).deriv
  | succ m ih =>
    have hd := (hasDerivAt_reciprocalPowerSeries m hx).const_mul
      ((-1 : ℝ)^m * ((m + 1).factorial : ℝ))
    have he : HasDerivAt (iteratedDeriv (m + 1) realDigamma)
        (((-1 : ℝ)^m * ((m + 1).factorial : ℝ)) *
          (-((m + 2 : ℕ) : ℝ) * reciprocalPowerSeries (m + 1) x)) x := by
      apply hd.congr_of_eventuallyEq
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      exact ih hy
    rw [iteratedDeriv_succ, he.deriv]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      pow_succ, Nat.succ_eq_add_one]
    ring

/-- Correct sign for all positive-axis polygamma orders m+1. -/
theorem polygamma_strict_sign (m : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < (-1 : ℝ)^m * iteratedDeriv (m + 1) realDigamma x := by
  rw [iteratedDeriv_digamma_series m hx]
  have hsign : (-1 : ℝ)^m * (-1 : ℝ)^m = 1 := by
    rw [← mul_pow]
    norm_num
  have he : (-1 : ℝ)^m *
      ((-1 : ℝ)^m * ((m + 1).factorial : ℝ) * reciprocalPowerSeries m x) =
      ((m + 1).factorial : ℝ) * reciprocalPowerSeries m x := by
    calc
      _ = ((-1 : ℝ)^m * (-1 : ℝ)^m) *
        ((m + 1).factorial : ℝ) * reciprocalPowerSeries m x := by ring
      _ = _ := by rw [hsign]; ring
  rw [he]
  exact mul_pos (by positivity) (reciprocalPowerSeries_pos m hx)

end
end RiemannResearch.RH.CRTBlock
