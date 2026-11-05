/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MertensFirstMomentEnvelope
import RiemannResearch.Analysis.MertensExponentialEntropy

/-!
# Signed pairing with an exponential Mertens cutoff

A monotone arithmetic majorant controls the error on the entire ray beyond
each cutoff. A common physical majorant with a summable constant term and
a summable displacement term forces the projection residual to vanish.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QMertensFirstMoment
open RiemannResearch.Analysis RiemannResearch.NumberTheory.PrimeNumberTheorem
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeDisplacementRigidity

/-- The cutoff pairing annihilates the mean of every orthogonal difference
of a reciprocally smoothed vector and a vector with the given moment. -/
theorem annihilator_mean_zero_of_exponential_cutoff_moment (v z : QHilbert)
    (horth : QShiftedReciprocal.B v - z ∈ ZetaTwoOptimizerStage.closureᗮ) (E : ℝ → ℝ) (W : ℕ → ℝ)
    (hE : Tendsto E atTop atBot)
    (hmono : ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y → E y ≤ E x)
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ Real.exp (E x) * x)
    (henv : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
      errorEnvelope N n (Real.exp (E (N : ℝ))) ≤ 2 + K * W n)
    (hconst : Summable (fun n : ℕ => positiveQWeight n * W n))
    (hd : Summable (fun n : ℕ => positiveQWeight n * W n * |qSequence z n|)) :
    inner ℝ qOne (QShiftedReciprocal.B v - z) = 0 := by
  classical
  choose p hp hprime using (fun j : ℕ => Nat.exists_infinite_primes (j + 2))
  let q : ℕ → ℕ := fun j => p j - 1
  have hq : Tendsto q atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop k] with j hj
    have := hp j
    dsimp [q]; omega
  have hlegal : ∀ᶠ j : ℕ in atTop, Squarefree (q j + 1) := by
    apply Eventually.of_forall
    intro j
    have hqp : q j + 1 = p j := by have := hp j; dsimp [q]; omega
    rw [hqp]; exact (hprime j).squarefree
  have hqr : Tendsto (fun j => (q j : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp hq
  let ε : ℕ → ℝ := fun j => Real.exp (E (q j : ℝ))
  have hε : ∀ᶠ j : ℕ in atTop, 0 < ε j ∧ ε j ≤ 1 ∧
      ε j * (1 + Real.log (1 / ε j)) ≤ 1 / 2 := by
    filter_upwards [(hE.comp hqr).eventually (eventually_le_atBot (-6 : ℝ))] with j hj
    change E (q j : ℝ) ≤ -6 at hj
    refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith), ?_⟩
    have hu : 6 ≤ -E (q j : ℝ) := by linarith
    simpa only [ε, neg_neg] using exponential_entropy_small _ hu
  obtain ⟨L, hL⟩ := eventually_atTop.1 hM
  have htail : ∀ᶠ j : ℕ in atTop, ∀ y : ℝ, (q j : ℝ) ≤ y → |M y| ≤ ε j * y := by
    filter_upwards [hqr.eventually (eventually_ge_atTop L),
      hqr.eventually hmono] with j hj hm y hy
    exact (hL y (hj.trans hy)).trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (hm y hy)) ((Nat.cast_nonneg (q j)).trans hy))
  obtain ⟨K, hK, henv⟩ := henv
  let F : ℕ → ℝ := fun n => positiveQWeight n * (1 + |qSequence z n|)
  let H : ℕ → ℝ := fun n => positiveQWeight n * W n * (1 + |qSequence z n|)
  have hF : Summable F := by
    refine (positiveQWeight_summable.add
      (qSequence_product_summable qOne z).abs).congr ?_
    intro n
    by_cases hn : n = 0
    · subst n; simp [F, positiveQWeight]
    · simp [F, qOneSequence, hn, abs_mul, abs_of_nonneg (positiveQWeight_nonneg n), mul_add]
  have hH : Summable H := by
    refine (hconst.add hd).congr ?_
    intro n
    dsimp only [H]
    ring
  apply annihilator_mean_zero_of_summable_mertens_first_moment v z horth q hq ε hlegal hε htail
    (fun n => 2 * F n + K * H n) ((hF.mul_left 2).add (hH.mul_left K))
  filter_upwards [hq.eventually henv] with j hj n
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hj n) (positiveQWeight_nonneg n))
    (show 0 ≤ 1 + |qSequence z n| by positivity)
  apply h.trans
  dsimp only [F, H]
  exact le_of_eq (by ring)

/-- Pair a uniform exponential Mertens estimate against any common physical weight. -/
theorem residual_zero_of_exponential_cutoff_moment (E : ℝ → ℝ) (W : ℕ → ℝ)
    (hE : Tendsto E atTop atBot)
    (hmono : ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y → E y ≤ E x)
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ Real.exp (E x) * x)
    (henv : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
      errorEnvelope N n (Real.exp (E (N : ℝ))) ≤ 2 + K * W n)
    (hconst : Summable (fun n : ℕ => positiveQWeight n * W n))
    (hd : Summable (fun n : ℕ => positiveQWeight n * W n * |qSequence displacement n|)) :
    ZetaTwoOptimizerStage.limitingResidual = 0 :=
  residual_eq_zero_of_witness_mean_zero
    (annihilator_mean_zero_of_exponential_cutoff_moment pResidual displacement witness_mem_orthogonal
      E W hE hmono hM henv hconst hd)

end RiemannResearch.RH.QMertensFirstMoment
