/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PSeriesTail
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# An explicit zeta bound from absolute convergence

The zeta Dirichlet series is split after its first nonzero term. The proved
p-series integral comparison yields the uniform bound in Re s > 1.
The proof uses Mathlib's LSeries_one_eq_riemannZeta and the local integral-test
tail theorem; no zero-density or critical-line estimate is required.
-/

noncomputable section
open scoped BigOperators

theorem norm_riemannZeta_sub_one_le_integral_test {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s - 1‖ ≤ 1 / (s.re - 1) := by
  have hsum : Summable (LSeries.term (1 : ℕ → ℂ) s) := LSeriesSummable_one_iff.mpr hs
  have hsplit := hsum.sum_add_tsum_nat_add 2
  change (∑ n ∈ Finset.range 2, LSeries.term (1 : ℕ → ℂ) s n) +
    (∑' k : ℕ, LSeries.term (1 : ℕ → ℂ) s (k + 2)) = LSeries 1 s at hsplit
  have hhead : (∑ n ∈ Finset.range 2, LSeries.term (1 : ℕ → ℂ) s n) = 1 := by
    simp [Finset.sum_range_succ, LSeries.term]
  rw [hhead, LSeries_one_eq_riemannZeta hs] at hsplit
  have he : riemannZeta s - 1 = ∑' k : ℕ, LSeries.term (1 : ℕ → ℂ) s (k + 2) := by
    rw [← hsplit]
    ring
  have htail : Summable (fun k : ℕ => LSeries.term (1 : ℕ → ℂ) s (k + 2)) :=
    (summable_nat_add_iff 2).mpr hsum
  have hp0 : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hp : Summable (fun k : ℕ => ((k + 2 : ℕ) : ℝ) ^ (-s.re)) :=
    (summable_nat_add_iff 2).mpr hp0
  have hnorm (k : ℕ) : ‖LSeries.term (1 : ℕ → ℂ) s (k + 2)‖ =
      ((k + 2 : ℕ) : ℝ) ^ (-s.re) := by
    rw [LSeries.norm_term_eq, if_neg (by omega)]
    simp only [Pi.one_apply, norm_one]
    rw [Real.rpow_neg (Nat.cast_nonneg _), one_div]
  rw [he]
  calc ‖∑' k : ℕ, LSeries.term (1 : ℕ → ℂ) s (k + 2)‖ ≤
      ∑' k : ℕ, ‖LSeries.term (1 : ℕ → ℂ) s (k + 2)‖ := norm_tsum_le_tsum_norm htail.norm
    _ = ∑' k : ℕ, ((k + 2 : ℕ) : ℝ) ^ (-s.re) := tsum_congr hnorm
    _ ≤ 1 / (s.re - 1) := by
      simpa [Nat.add_assoc] using Real.tsum_nat_rpow_tail_le hs (show 1 ≤ (1 : ℕ) by rfl)

theorem norm_riemannZeta_le_integral_test {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ 1 + 1 / (s.re - 1) := by
  have hh := norm_le_norm_sub_add (riemannZeta s) (1 : ℂ)
  simp only [norm_one] at hh
  linarith [norm_riemannZeta_sub_one_le_integral_test hs]
