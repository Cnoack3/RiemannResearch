/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QFiniteEighthForcing
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

private theorem witness_eighth (hd : Summable (fun n : ℕ =>
    positiveQWeight n * |qSequence displacement n| ^ 8)) :
    Summable (fun n : ℕ => positiveQWeight n * |qSequence witness n| ^ 8) := by
  obtain ⟨C, hC⟩ := B_physical_bounded pResidual
  have hc := (abs_nonneg _).trans (hC 0)
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (positiveQWeight_nonneg n) (by positivity))
      _ (((positiveQWeight_summable.mul_right (C ^ 8)).add hd).mul_left 256)
  intro n
  have hw : qSequence witness n = qSequence (B pResidual) n - qSequence displacement n := by
    change qSequenceLinear (B pResidual - displacement) n = _
    rw [map_sub]
    rfl
  have htri : |qSequence witness n| ≤ C + |qSequence displacement n| := by
    rw [hw]
    exact (abs_sub _ _).trans (add_le_add (hC n) le_rfl)
  let a := |qSequence displacement n|
  have hapos : 0 ≤ a := abs_nonneg _
  have bound : |qSequence witness n| ^ 8 ≤ 256 * (C ^ 8 + a ^ 8) := by
    rcases le_total C a with h | h
    · have hh : |qSequence witness n| ≤ 2 * a := by linarith
      calc
        _ ≤ (2 * a) ^ 8 := by gcongr
        _ ≤ _ := by rw [mul_pow]; norm_num; nlinarith [show 0 ≤ C ^ 8 by positivity]
    · have hh : |qSequence witness n| ≤ 2 * C := by linarith
      calc
        _ ≤ (2 * C) ^ 8 := by gcongr
        _ ≤ _ := by rw [mul_pow]; norm_num; nlinarith [show 0 ≤ a ^ 8 by positivity]
  calc
    _ ≤ positiveQWeight n * (256 * (C ^ 8 + a ^ 8)) :=
      mul_le_mul_of_nonneg_left bound (positiveQWeight_nonneg _)
    _ = _ := by dsimp [a]; ring

/-- The arithmetic approximation input, stated just for the squarefree closure.
Any legal sequence converging to one in physical L^(8 / 7)(Q) supplies it. -/
def HasSubcriticalApproximation : Prop :=
  ∃ G : ℕ → QHilbert, (∀ j, G j ∈ closure) ∧
    (∀ j, Summable (fun n => positiveQWeight n *
      |qSequence (qOne - G j) n| ^ (8 / 7 : ℝ))) ∧
    Tendsto (fun j => (∑' n, positiveQWeight n *
      |qSequence (qOne - G j) n| ^ (8 / 7 : ℝ)) ^ (7 / 8 : ℝ)) atTop (𝓝 0)

private theorem weighted_pairing_eighth (x y : QHilbert)
    (hx : Summable fun k => positiveQWeight k * |qSequence x k| ^ (8 / 7 : ℝ))
    (hy : Summable fun k => positiveQWeight k * |qSequence y k| ^ (8 : ℕ)) :
    |inner ℝ x y| ≤ (∑' k, positiveQWeight k * |qSequence x k| ^ (8 / 7 : ℝ)) ^ (7 / 8 : ℝ) *
      (∑' k, positiveQWeight k * |qSequence y k| ^ (8 : ℕ)) ^ (1 / 8 : ℝ) := by
  let a := fun k => positiveQWeight k ^ (7 / 8 : ℝ) * |qSequence x k|
  let b := fun k => positiveQWeight k ^ (1 / 8 : ℝ) * |qSequence y k|
  have ha (k : ℕ) : (a k) ^ (8 / 7 : ℝ) = positiveQWeight k * |qSequence x k| ^ (8 / 7 : ℝ) := by
    dsimp only [a]
    rw [Real.mul_rpow (Real.rpow_nonneg (positiveQWeight_nonneg _) _) (abs_nonneg _),
      ← Real.rpow_mul (positiveQWeight_nonneg _)]
    norm_num
  have hb (k : ℕ) : (b k) ^ (8 : ℝ) = positiveQWeight k * |qSequence y k| ^ (8 : ℕ) := by
    dsimp only [b]
    rw [Real.mul_rpow (Real.rpow_nonneg (positiveQWeight_nonneg _) _) (abs_nonneg _),
      ← Real.rpow_mul (positiveQWeight_nonneg _)]
    norm_num
  have hab (k : ℕ) : a k * b k = ‖positiveQWeight k * qSequence x k * qSequence y k‖ := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (positiveQWeight_nonneg k)]
    dsimp only [a,b]
    calc
      _ = (positiveQWeight k ^ (7 / 8 : ℝ) * positiveQWeight k ^ (1 / 8 : ℝ)) *
          |qSequence x k| * |qSequence y k| := by ring
      _ = _ := by
        rw [← Real.rpow_add' (positiveQWeight_nonneg k) (by norm_num : (7 / 8 : ℝ)+1 / 8 ≠ 0)]
        norm_num
  have hpq : (8 / 7 : ℝ).HolderConjugate 8 := Real.holderConjugate_iff.mpr (by norm_num)
  have H := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg (f := a) (g := b) hpq
    (fun k => mul_nonneg (Real.rpow_nonneg (positiveQWeight_nonneg _) _) (abs_nonneg _))
    (fun k => mul_nonneg (Real.rpow_nonneg (positiveQWeight_nonneg _) _) (abs_nonneg _))
    (by simpa only [ha] using hx) (by simpa only [hb] using hy)
  simp only [ha,hb,hab] at H
  rw [qInner_weighted, ← Real.norm_eq_abs]
  apply (norm_tsum_le_tsum_norm (qSequence_product_summable x y).norm).trans
  rwa [show (1 / (8 / 7) : ℝ) = 7 / 8 by norm_num] at H

/-- The dual eighth moment suffices under the physical subcritical approximation. -/
theorem riemannHypothesis_of_displacement_eighth (happrox : HasSubcriticalApproximation)
    (hd : Summable fun n => positiveQWeight n * |qSequence displacement n| ^ 8) :
    RiemannHypothesis := by
  obtain ⟨G, hG, hs, ht⟩ := happrox
  let D := (∑' n, positiveQWeight n * |qSequence witness n| ^ (8 : ℕ)) ^ (1 / 8 : ℝ)
  have hle (j : ℕ) := weighted_pairing_eighth (qOne - G j) witness (hs j) (witness_eighth hd)
  simp only [inner_sub_left, Submodule.inner_right_of_mem_orthogonal (hG _) witness_mem_orthogonal,
    sub_zero] at hle
  have ht' := ht.mul_const D
  rw [zero_mul] at ht'
  have hz : |inner ℝ qOne witness| ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds ht' hle
  have hr := residual_eq_zero_of_witness_mean_zero (abs_nonpos_iff.mp hz)
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr
      (Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm))

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
