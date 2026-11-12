/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoDisplacementResolvent
import RiemannResearch.Analysis.ParetoReciprocalTailCertificate

/-!
# A kernel-checkable centered reciprocal-constant certificate

Source: Pareto-first research agenda, Priority 5, 11 November 2026.
Thirty physical sites are evaluated exactly. The complete remaining tail
is bounded by (4/9)/31. This supplies a rational bound without importing
numerical values of zeta(2) or zeta(3).
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QParetoCenteredConstant
open Pareto ZetaTwoHilbert
open RiemannResearch.Analysis.ParetoPeriodicAbelTail
open RiemannResearch.Analysis.ParetoReciprocalTailCertificate

theorem centered_constant_energy_le_seventh :
    ‖reciprocalD hilbertOne - (2 / 3 : ℝ) • hilbertOne‖ ^ 2 ≤ (1 / 7 : ℝ) := by
  let f := reciprocalD hilbertOne - (2 / 3 : ℝ) • hilbertOne
  let a : ℕ → ℝ := fun n => weight 0 n * (1 / ((n : ℝ) + 1) - 2 / 3) ^ 2
  have hone (n : ℕ) : (hilbertOne n) ^ 2 = paretoWeight n := by
    rw [← hilbertSequence_weighted_square, hilbertOne_sequence, positiveWeight_succ]
    simp [zeroAnchor]
  have hf (n : ℕ) : (f n) ^ 2 = a n := by
    change (reciprocalD hilbertOne n - (2 / 3 : ℝ) * hilbertOne n) ^ 2 = _
    rw [reciprocalD_apply]
    have he : hilbertOne n / ((n : ℝ) + 1) - (2 / 3 : ℝ) * hilbertOne n =
        (1 / ((n : ℝ) + 1) - 2 / 3) * hilbertOne n := by ring
    rw [he, mul_pow, hone]
    dsimp [a, weight, paretoWeight]
    push_cast
    ring
  have hs : Summable a := (hilbert_coordinate_square_summable f).congr hf
  have hn : ‖f‖ ^ 2 = ∑' n, a n := by
    rw [hilbert_norm_sq]
    exact tsum_congr hf
  have hfull := hs.sum_add_tsum_nat_add 30
  rw [← hn] at hfull
  have ht : (∑' k, a (k + 30)) =
      ∑' k, (1 / ((k + 31 : ℕ) : ℝ) - 2 / 3) ^ 2 * weight 30 k := by
    apply tsum_congr
    intro k
    dsimp [a, weight]
    push_cast
    ring
  have hb (k : ℕ) : |(1 / ((k + 31 : ℕ) : ℝ) - 2 / 3) ^ 2| ≤ (4 / 9 : ℝ) := by
    have h0 : (0 : ℝ) ≤ 1 / ((k + 31 : ℕ) : ℝ) := by positivity
    have h1 : (1 : ℝ) / ((k + 31 : ℕ) : ℝ) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((k + 31 : ℕ) : ℝ))).mpr
      norm_num only [one_mul]
      exact_mod_cast (show 1 ≤ k + 31 by omega)
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have htail := weighted_tail_bound
    (fun k => (1 / ((k + 31 : ℕ) : ℝ) - 2 / 3) ^ 2) 30 (4 / 9) hb
  have htail' : (∑' k, a (k + 30)) ≤ (4 / 9 : ℝ) / 31 := by
    rw [ht]
    exact (le_abs_self _).trans (by norm_num at htail ⊢; exact htail)
  have hhead : (∑ n ∈ Finset.range 30, a n) + (4 / 9 : ℝ) / 31 ≤ (1 / 7 : ℝ) := by
    norm_num [a, weight, Finset.sum_range_succ]
  change ‖f‖ ^ 2 ≤ _
  linarith

theorem centered_constant_norm_le :
    ‖reciprocalD hilbertOne - (2 / 3 : ℝ) • hilbertOne‖ ≤ Real.sqrt (1 / 7 : ℝ) :=
  Real.le_sqrt_of_sq_le centered_constant_energy_le_seventh

end RiemannResearch.RH.QParetoCenteredConstant
