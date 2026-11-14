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

private theorem zeta_real_term_eq_norm (q : ℝ) (n : ℕ) :
    LSeries.term (1 : ℕ → ℂ) (q : ℂ) n =
      (‖LSeries.term (1 : ℕ → ℂ) (q : ℂ) n‖ : ℂ) := by
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · simp [LSeries.term, hn]
  · simp only [LSeries.term, hn, ↓reduceIte, Pi.one_apply, norm_one,
      Complex.ofReal_re]
    rw [Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]

/-- On the real half-line above one the zeta series is a sum of nonnegative real terms. -/
theorem riemannZeta_real_eq_tsum_norm {q : ℝ} (hq : 1 < q) :
    riemannZeta (q : ℂ) =
      ((∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (q : ℂ) n‖ : ℝ) : ℂ) := by
  rw [← LSeries_one_eq_riemannZeta (by simpa using hq), Complex.ofReal_tsum]
  exact tsum_congr (zeta_real_term_eq_norm q)

/-- Exact absolute mass of the zeta series on the real half-line. -/
theorem norm_riemannZeta_real_eq_tsum_norm {q : ℝ} (hq : 1 < q) :
    ‖riemannZeta (q : ℂ)‖ =
      ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (q : ℂ) n‖ := by
  rw [riemannZeta_real_eq_tsum_norm hq,
    Complex.norm_of_nonneg (tsum_nonneg fun n => norm_nonneg _)]

/-- The n=1 term gives a nonzero real-axis denominator. -/
theorem one_le_norm_riemannZeta_real {q : ℝ} (hq : 1 < q) :
    1 ≤ ‖riemannZeta (q : ℂ)‖ := by
  rw [norm_riemannZeta_real_eq_tsum_norm hq]
  have hs : Summable (LSeries.term (1 : ℕ → ℂ) (q : ℂ)) :=
    LSeriesSummable_one_iff.mpr (by simpa using hq)
  have h := hs.norm.le_tsum 1 (fun _ _ => norm_nonneg _)
  simpa [LSeries.term] using h

/-- Absolute convergence and monotonicity of positive Dirichlet coefficients. -/
theorem norm_riemannZeta_le_real_of_re_le {q : ℝ} {s : ℂ}
    (hq : 1 < q) (hqs : q ≤ s.re) :
    ‖riemannZeta s‖ ≤ ‖riemannZeta (q : ℂ)‖ := by
  have hs : 1 < s.re := hq.trans_le hqs
  have hsum : Summable (LSeries.term (1 : ℕ → ℂ) s) := LSeriesSummable_one_iff.mpr hs
  have hqsum : Summable (LSeries.term (1 : ℕ → ℂ) (q : ℂ)) :=
    LSeriesSummable_one_iff.mpr (by simpa using hq)
  rw [norm_riemannZeta_real_eq_tsum_norm hq, ← LSeries_one_eq_riemannZeta hs]
  change ‖∑' n, LSeries.term (1 : ℕ → ℂ) s n‖ ≤ _
  apply (norm_tsum_le_tsum_norm hsum.norm).trans
  apply Summable.tsum_le_tsum _ hsum.norm hqsum.norm
  intro n
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ↓reduceIte, Pi.one_apply, norm_one, Complex.ofReal_re]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hn1) q)
      (Real.rpow_le_rpow_of_exponent_le hn1 hqs)

/-- Normalized zeta domination, uniform as the real parameter approaches one from above. -/
theorem norm_riemannZeta_div_real_le_one {q : ℝ} {s : ℂ}
    (hq : 1 < q) (hqs : q ≤ s.re) :
    ‖riemannZeta s / riemannZeta (q : ℂ)‖ ≤ 1 := by
  rw [norm_div]
  exact (div_le_one (lt_of_lt_of_le zero_lt_one
    (one_le_norm_riemannZeta_real hq))).mpr
      (norm_riemannZeta_le_real_of_re_le hq hqs)
