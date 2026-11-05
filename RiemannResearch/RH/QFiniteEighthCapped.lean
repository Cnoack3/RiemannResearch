/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QFiniteEighthMoment

/-! # Capping individual contributions to the aligned eighth moment

A fixed positive cap on each weighted contribution allows a bounded number
of arbitrarily large moving contributions. Summability of the capped limit
implies ordinary summability because its terms tend to zero.
-/

noncomputable section
open Filter
open scoped Topology BigOperators ENNReal
namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeDisplacementRigidity
open ZetaTwoOptimizerStage QShiftedReciprocal

/-- Cap each site's contribution after applying its physical weight. -/
def cappedEighthHead (L : ℝ) (v : QHilbert) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), min L (|qSequence v n| ^ 8 / (n : ℝ) ^ 2)

/-- A frequently bounded capped moment gives the full eighth moment of the
limit. There is no pointwise bound on the discarded excess at a finite stage. -/
theorem summable_eighth_of_frequent_capped {v : ℕ → QHilbert} {u : QHilbert}
    (hv : Tendsto v atTop (𝓝 u)) {L : ℝ} (hL : 0 < L) (C : ℝ)
    (h : ∃ᶠ N : ℕ in atTop, cappedEighthHead L (v N) N ≤ C) :
    Summable (fun n : ℕ => positiveQWeight n * |qSequence u n| ^ 8) := by
  let a (x : QHilbert) (n : ℕ) : ℝ := |qSequence x n| ^ 8 / (n : ℝ) ^ 2
  have hpos (x : QHilbert) (n : ℕ) : 0 ≤ a x n := by dsimp [a]; positivity
  have hs : Summable (fun n : ℕ => min L (a u n)) := by
    apply summable_of_sum_range_le (c := C) (fun n => le_min hL.le (hpos u n))
    intro K
    by_contra! hbad
    have ht : Tendsto (fun N => ∑ n ∈ Finset.range K, min L (a (v N) n)) atTop
        (𝓝 (∑ n ∈ Finset.range K, min L (a u n))) := by
      apply tendsto_finsetSum
      intro n _
      exact tendsto_const_nhds.min (((qSequence_tendsto_of_tendsto hv n).abs.pow 8).div_const _)
    have he := ht.eventually (Ioi_mem_nhds hbad)
    obtain ⟨N, ⟨hN, hKN⟩, hgt⟩ :=
      ((h.and_eventually (eventually_ge_atTop K)).and_eventually he).exists
    have hle : (∑ n ∈ Finset.range K, min L (a (v N) n)) ≤ cappedEighthHead L (v N) N := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro n _ _
      exact le_min hL.le (hpos (v N) n)
    exact (not_lt_of_ge (hle.trans hN)) hgt
  have hu : Summable (a u) := by
    apply hs.congr_cofinite
    filter_upwards [hs.tendsto_cofinite_zero.eventually (Iio_mem_nhds hL)] with n hn
    change min L (a u n) < L at hn
    apply min_eq_right
    by_contra! hlarge
    rw [min_eq_left hlarge.le] at hn
    exact (lt_irrefl _ hn)
  apply (hu.mul_left (1 / zetaTwo)).congr
  intro n
  simp [a, positiveQWeight, div_eq_mul_inv, mul_comm, mul_assoc]

/-- Capped contributions on the actual aligned stages suffice with the same
subcritical arithmetic premise as the ordinary eighth moment. -/
theorem riemannHypothesis_of_capped_eighth_liminf (happrox : HasSubcriticalApproximation)
    {L : ℝ} (hL : 0 < L)
    (h : liminf (fun N : ℕ =>
      (Real.nnabs (cappedEighthHead L (finiteDisplacement N) N) : ℝ≥0∞)) atTop < ⊤) :
    RiemannHypothesis := by
  obtain ⟨C, hC⟩ := ENNReal.exists_frequently_lt_of_liminf_ne_top h.ne
  exact riemannHypothesis_of_displacement_eighth happrox
    (summable_eighth_of_frequent_capped finiteDisplacement_tendsto hL C (hC.mono fun _ hN => hN.le))

/-- A stage may have up to k exceptional sites at arbitrary positions and with
arbitrary sizes. Their total contribution after capping at one is at most k. -/
theorem riemannHypothesis_of_trimmed_eighth (happrox : HasSubcriticalApproximation)
    (k : ℕ) (C : ℝ)
    (h : ∃ᶠ N : ℕ in atTop, ∃ D : Finset ℕ, D ⊆ Finset.range (N + 1) ∧ D.card ≤ k ∧
      (∑ n ∈ Finset.range (N + 1) \ D,
        |qSequence (finiteDisplacement N) n| ^ 8 / (n : ℝ) ^ 2) ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_displacement_eighth happrox
  apply summable_eighth_of_frequent_capped finiteDisplacement_tendsto
    (L := 1) (by norm_num) (C + (k : ℝ))
  apply h.mono
  rintro N ⟨D, hsub, hcard, hsum⟩
  let a (n : ℕ) : ℝ := |qSequence (finiteDisplacement N) n| ^ 8 / (n : ℝ) ^ 2
  change (∑ n ∈ Finset.range (N + 1), min 1 (a n)) ≤ C + (k : ℝ)
  rw [← Finset.sum_sdiff (f := fun n => min 1 (a n)) hsub]
  apply add_le_add
  · exact (Finset.sum_le_sum fun n _ => min_le_right 1 (a n)).trans hsum
  · calc
      (∑ n ∈ D, min 1 (a n)) ≤ ∑ _n ∈ D, (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => min_le_left 1 (a n)
      _ = (D.card : ℝ) := by simp
      _ ≤ (k : ℝ) := by exact_mod_cast hcard

end RiemannResearch.RH.QSquarefreeFiniteDisplacement
