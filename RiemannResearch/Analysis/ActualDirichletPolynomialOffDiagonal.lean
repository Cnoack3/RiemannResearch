/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualDirichletPolynomialGram
import RiemannResearch.Analysis.OffDiagonalGramBounds
import RiemannResearch.Analysis.ActualZeroCoshMass
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Signed actual-zero quadratic corrections with exact zero diagonal

Source: user-provided fixed-support quadratic correction; finite transfer
proofs developed for this formalization. Ford--Meng--Zaharescu,
https://arxiv.org/pdf/1511.06814, Lemmas 1--2, motivate the analytic
providers, but those quantitative providers are NOT proved in this module.
All actual zero ordinates and analytic multiplicities are retained.
The two Landau comparison bounds use existing checked reflection estimates.
The signed limit is a conditional research reduction with explicit hphase.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.ActualDirichletPolynomialGram
open ZeroOrdinate ActualZeroOrdinate RiemannResearch.Fourier

theorem sampledSquare_prime_offDiagonal_remainder_bound
    (T : ℝ) (s : Finset ℕ) (a : ℕ → ℂ) (η κ : ℝ)
    (hs : ∀ n ∈ s, 0 < n)
    (hR : ∀ n ∈ s, ∀ m ∈ s, n ≠ m →
      ‖gramEntry T n m - (if n = m then (Zeta23.Ncount 0 T : ℂ) else 0) -
        (T : ℂ) * primePowerCovarianceSignedEntry n m‖ ≤
        η + κ * (Real.log n - Real.log m) ^ 2) :
    ‖sampledSquare T s a -
      (Zeta23.Ncount 0 T : ℂ) * (∑ n ∈ s, star (a n) * a n) -
      finiteGramErrorPairing s a (fun n m => (T : ℂ) * primePowerCovarianceSignedEntry n m)‖ ≤
        η * ((∑ n ∈ s, ‖a n‖) ^ 2 - ∑ n ∈ s, ‖a n‖ ^ 2) +
          κ * weightedFrequencySpread s (fun n => ‖a n‖) (fun n => Real.log n) := by
  classical
  let B : ℕ → ℕ → ℂ := fun n m => (T : ℂ) * primePowerCovarianceSignedEntry n m
  let D : ℕ → ℕ → ℂ := fun n m => if n = m then (Zeta23.Ncount 0 T : ℂ) else 0
  let R : ℕ → ℕ → ℂ := fun n m => gramEntry T n m - D n m - B n m
  have he := finiteGramErrorPairing_three_term_split s a (gramEntry T) D B R
    (fun n hn m hm => by dsimp [R]; ring)
  rw [sampledSquare_eq_gram, he, diagonal_pairing]
  have hc : ∀ x y z : ℂ, x + y + z - x - y = z := by intros; ring
  rw [hc]
  apply finiteGramErrorPairing_norm_le_offDiagonal_frequencySpread
    s a R (fun n => Real.log n) η κ
  · intro n hn
    simp [R, D, B, gramEntry_diag, primePowerCovarianceSignedEntry,
      primePowerCovarianceSymmetricEntry_diag n (hs n hn)]
  · exact hR

theorem sampledSquare_landau_error_frequencySpread
    (T L : ℝ) (s : Finset ℕ) (a : ℕ → ℂ)
    (hL : ∀ n ∈ s, ∀ m ∈ s, |Real.log m - Real.log n| ≤ L) :
    ‖sampledSquare T s a -
      finiteGramErrorPairing s a (fun n m =>
        landauSum T (Real.log m - Real.log n))‖ ≤
      (Real.exp (L / 2) * horizontalEnergy T) *
        weightedFrequencySpread s (fun n => ‖a n‖) (fun n => Real.log n) := by
  rw [sampledSquare_eq_gram]
  have he : finiteGramErrorPairing s a (gramEntry T) -
      finiteGramErrorPairing s a (fun n m => landauSum T (Real.log m - Real.log n)) =
      finiteGramErrorPairing s a (fun n m =>
        gramEntry T n m - landauSum T (Real.log m - Real.log n)) := by
    simp only [finiteGramErrorPairing, mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [he]
  have hb := finiteGramErrorPairing_norm_le_frequencySpread s a
    (fun n m => gramEntry T n m - landauSum T (Real.log m - Real.log n))
    (fun n => Real.log n) 0 (Real.exp (L / 2) * horizontalEnergy T)
  simp only [zero_mul, zero_add] at hb
  apply hb
  intro n hn m hm
  have hexp : Real.exp (|Real.log m - Real.log n| / 2) ≤ Real.exp (L / 2) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hL n hn m hm) (by norm_num))
  calc
    _ ≤ ((Real.log m - Real.log n) ^ 2 *
        Real.exp (|Real.log m - Real.log n| / 2)) * horizontalEnergy T :=
      ordinate_landau_error T (Real.log m - Real.log n)
    _ ≤ ((Real.log m - Real.log n) ^ 2 * Real.exp (L / 2)) * horizontalEnergy T :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp (sq_nonneg _)) (horizontalEnergy_nonneg T)
    _ = _ := by ring

end RiemannResearch.Analysis.ActualDirichletPolynomialGram

open Filter

namespace RiemannResearch.Analysis.ActualDirichletPolynomialGram
open ZeroOrdinate ActualZeroOrdinate RiemannResearch.Fourier
/-- The sharp scalar strip coefficient, summed with the actual coefficient magnitudes. -/
theorem sampledSquare_landau_error_cosh
    (T : ℝ) (s : Finset ℕ) (a : ℕ → ℂ) :
    ‖sampledSquare T s a -
      finiteGramErrorPairing s a (fun n m =>
        landauSum T (Real.log m - Real.log n))‖ ≤
      horizontalEnergy T *
        (∑ n ∈ s, ∑ m ∈ s, ‖a n‖ * ‖a m‖ *
          (4 * (Real.cosh (|Real.log m - Real.log n| / 2) - 1))) := by
  rw [sampledSquare_eq_gram]
  have he : finiteGramErrorPairing s a (gramEntry T) -
      finiteGramErrorPairing s a (fun n m => landauSum T (Real.log m - Real.log n)) =
      finiteGramErrorPairing s a (fun n m =>
        gramEntry T n m - landauSum T (Real.log m - Real.log n)) := by
    simp only [finiteGramErrorPairing, mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [he]
  unfold finiteGramErrorPairing
  calc
    _ ≤ ∑ n ∈ s, ‖∑ m ∈ s, star (a n) *
        (gramEntry T n m - landauSum T (Real.log m - Real.log n)) * a m‖ :=
      norm_sum_le s _
    _ ≤ ∑ n ∈ s, ∑ m ∈ s, ‖star (a n) *
        (gramEntry T n m - landauSum T (Real.log m - Real.log n)) * a m‖ :=
      Finset.sum_le_sum (fun n hn => norm_sum_le s _)
    _ ≤ ∑ n ∈ s, ∑ m ∈ s, horizontalEnergy T *
        (‖a n‖ * ‖a m‖ *
          (4 * (Real.cosh (|Real.log m - Real.log n| / 2) - 1))) := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      simp only [norm_mul, norm_star]
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (ActualZeroCoshMass.ordinate_landau_error_sharp T (Real.log m - Real.log n))
          (norm_nonneg (a n))) (norm_nonneg (a m))
      simpa only [gramEntry, mul_assoc, mul_comm, mul_left_comm] using h
    _ = _ := by simp only [Finset.mul_sum]

/-- Fixed support transference. The phase-law provider is a visible hypothesis. -/
theorem sampledSquare_signed_limit_of_phase
    (s : Finset ℕ) (a : ℕ → ℂ) (hs : ∀ n ∈ s, 0 < n)
    (hphase : ∀ n ∈ s, ∀ m ∈ s, n ≠ m →
      Filter.Tendsto (fun T : ℝ => gramEntry T n m / (T : ℂ))
        Filter.atTop (nhds (primePowerCovarianceSignedEntry n m))) :
    Filter.Tendsto (fun T : ℝ =>
      (sampledSquare T s a -
        (Zeta23.Ncount 0 T : ℂ) * ∑ n ∈ s, star (a n) * a n) / (T : ℂ))
      Filter.atTop (nhds (finiteGramErrorPairing s a primePowerCovarianceSignedEntry)) := by
  classical
  let H : ℝ → ℕ → ℕ → ℂ := fun T n m =>
    (gramEntry T n m - if n = m then (Zeta23.Ncount 0 T : ℂ) else 0) / (T : ℂ)
  have hH (n : ℕ) (hn : n ∈ s) (m : ℕ) (hm : m ∈ s) :
      Filter.Tendsto (fun T => H T n m) Filter.atTop
        (nhds (primePowerCovarianceSignedEntry n m)) := by
    by_cases hnm : n = m
    · subst m
      simp only [H, if_true, gramEntry_diag, sub_self, zero_div]
      have hz : primePowerCovarianceSignedEntry n n = 0 := by
        simp [primePowerCovarianceSignedEntry,
          primePowerCovarianceSymmetricEntry_diag n (hs n hn)]
      rw [hz]
      exact tendsto_const_nhds
    · simpa [H, hnm] using hphase n hn m hm hnm
  have hlim : Filter.Tendsto (fun T => finiteGramErrorPairing s a (H T))
      Filter.atTop (nhds (finiteGramErrorPairing s a primePowerCovarianceSignedEntry)) := by
    unfold finiteGramErrorPairing
    apply tendsto_finsetSum
    intro n hn
    apply tendsto_finsetSum
    intro m hm
    exact ((tendsto_const_nhds.mul (hH n hn m hm)).mul tendsto_const_nhds)
  convert hlim using 1
  funext T
  rw [sampledSquare_eq_gram, ← diagonal_pairing]
  simp only [finiteGramErrorPairing, H]
  simp only [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  ring
end RiemannResearch.Analysis.ActualDirichletPolynomialGram
