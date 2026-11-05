/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QFiniteEighthForcing
import RiemannResearch.RH.QSubcriticalDisplacementMoment
import RiemannResearch.RH.QSquarefreeFiniteDisplacement
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.QShiftedReciprocal
import Mathlib.Analysis.MeanInequalities
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # An eighth-moment criterion on aligned finite projection heads

Source: the user's finite-head argument. The arithmetic input is subcritical
approximation in physical L^(8 / 7)(Q). J. Lee's natural approximation is
described by L. Báez-Duarte, https://arxiv.org/abs/math/0011254, §1,
(1.12), (1.17). The strict zero-free margin used to specialize the literature
is reported in B. Liu, https://arxiv.org/abs/2610.12234v2. We keep this input
explicit. The cofinal bound for the actual finite projections is open.
-/

noncomputable section
open Filter
open scoped Topology BigOperators ENNReal
namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeDisplacementRigidity
open ZetaTwoOptimizerStage QShiftedReciprocal

/-- Unnormalized physical eighth moment through coordinate N. The zero term vanishes. -/
def eighthHead (v : QHilbert) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), |qSequence v n| ^ 8 / (n : ℝ) ^ 2

/-- A cofinal bound on aligned heads controls every fixed limiting partial sum. -/
theorem summable_eighth_of_frequent_diagonal {v : ℕ → QHilbert} {u : QHilbert}
    (hv : Tendsto v atTop (𝓝 u)) (C : ℝ)
    (h : ∃ᶠ N : ℕ in atTop, eighthHead (v N) N ≤ C) :
    Summable (fun n : ℕ => positiveQWeight n * |qSequence u n| ^ 8) := by
  have hs : Summable (fun n : ℕ => |qSequence u n| ^ 8 / (n : ℝ) ^ 2) := by
    apply summable_of_sum_range_le (c := C) (fun n => by positivity)
    intro K
    by_contra! hbad
    have ht : Tendsto (fun N => ∑ n ∈ Finset.range K,
        |qSequence (v N) n| ^ 8 / (n : ℝ) ^ 2) atTop
        (𝓝 (∑ n ∈ Finset.range K, |qSequence u n| ^ 8 / (n : ℝ) ^ 2)) := by
      apply tendsto_finsetSum
      intro n _
      exact ((qSequence_tendsto_of_tendsto hv n).abs.pow 8).div_const _
    have he := ht.eventually (Ioi_mem_nhds hbad)
    obtain ⟨N, ⟨hN, hKN⟩, hgt⟩ :=
      ((h.and_eventually (eventually_ge_atTop K)).and_eventually he).exists
    have hle : (∑ n ∈ Finset.range K, |qSequence (v N) n| ^ 8 / (n : ℝ) ^ 2)
        ≤ eighthHead (v N) N := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intros
      positivity
    exact (not_lt_of_ge (hle.trans hN)) hgt
  apply (hs.mul_left (1 / zetaTwo)).congr
  intro n
  simp [positiveQWeight, div_eq_mul_inv, mul_comm, mul_assoc]

/-- The arithmetic approximation input, stated just for the squarefree closure.
Any legal sequence converging to one in physical L^(8 / 7)(Q) supplies it. -/
def HasSubcriticalApproximation : Prop :=
  ∃ G : ℕ → QHilbert, (∀ j, G j ∈ closure) ∧
    (∀ j, Summable (fun n => positiveQWeight n *
      |qSequence (qOne - G j) n| ^ (8 / 7 : ℝ))) ∧
    Tendsto (fun j => (∑' n, positiveQWeight n *
      |qSequence (qOne - G j) n| ^ (8 / 7 : ℝ)) ^ (7 / 8 : ℝ)) atTop (𝓝 0)

/-- Physical L^(8/7) approximation kills the mean of each L^8 annihilator. -/
theorem annihilator_mean_zero_of_eighth (happrox : HasSubcriticalApproximation)
    (w : QHilbert) (hw : w ∈ closureᗮ)
    (hsw : Summable fun n => positiveQWeight n * |qSequence w n| ^ 8) :
    inner ℝ qOne w = 0 := by
  apply annihilator_mean_zero_of_conjugate_moment
    (Real.holderConjugate_iff.mpr (by norm_num) : (8 / 7 : ℝ).HolderConjugate 8)
    _ w hw
  · simpa using hsw
  · simpa only [HasPhysicalApproximationAt, HasSubcriticalApproximation,
      show (1 / (8 / 7) : ℝ) = 7 / 8 by norm_num] using happrox

/-- The dual eighth moment suffices under the physical subcritical approximation. -/
theorem riemannHypothesis_of_displacement_eighth (happrox : HasSubcriticalApproximation)
    (hd : Summable fun n => positiveQWeight n * |qSequence displacement n| ^ 8) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_displacement_conjugate_moment
    (Real.holderConjugate_iff.mpr (by norm_num) : (8 / 7 : ℝ).HolderConjugate 8)
  · simpa only [HasPhysicalApproximationAt, HasSubcriticalApproximation,
      show (1 / (8 / 7) : ℝ) = 7 / 8 by norm_num] using happrox
  · simpa using hd

/-- The aligned finite-head liminf, taken in the extended nonnegative reals. -/
theorem riemannHypothesis_of_finite_eighth_liminf (happrox : HasSubcriticalApproximation)
    (h : liminf (fun N : ℕ =>
      (Real.nnabs (eighthHead (finiteDisplacement N) N) : ℝ≥0∞)) atTop < ⊤) :
    RiemannHypothesis := by
  obtain ⟨C, hC⟩ := ENNReal.exists_frequently_lt_of_liminf_ne_top h.ne
  exact riemannHypothesis_of_displacement_eighth happrox
    (summable_eighth_of_frequent_diagonal finiteDisplacement_tendsto C (hC.mono fun _ hN => hN.le))

/-- For sufficiency alone the input head may grow arbitrarily slowly.
The physical output is still tested through its aligned projection stage. -/
theorem riemannHypothesis_of_truncated_forcing_eighth_liminf
    (happrox : HasSubcriticalApproximation) (T : ℕ → ℕ) (hT : Tendsto T atTop atTop)
    (h : liminf (fun N : ℕ =>
      (Real.nnabs (eighthHead (projectedFiniteForcing N (T N)) N) : ℝ≥0∞)) atTop < ⊤) :
    RiemannHypothesis := by
  obtain ⟨C, hC⟩ := ENNReal.exists_frequently_lt_of_liminf_ne_top h.ne
  apply riemannHypothesis_of_displacement_eighth happrox
  exact summable_eighth_of_frequent_diagonal (projectedFiniteForcing_tendsto T hT) C
    (hC.mono fun _ hN => hN.le)

end RiemannResearch.RH.QSquarefreeFiniteDisplacement
