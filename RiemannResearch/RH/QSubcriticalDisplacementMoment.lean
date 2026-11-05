/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.QShiftedReciprocal
import Mathlib.Analysis.MeanInequalities

/-! # Displacement moments at a general pair of conjugate exponents

The arithmetic input is legal approximation in the physical L ^ p(Q) norm.
J. Lee's natural approximation is recorded by L. Báez-Duarte, §1 (1.12),
(1.17), https://arxiv.org/abs/math/0011254. Use of that input is explicit.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeDisplacementRigidity
open ZetaTwoOptimizerStage QShiftedReciprocal

/-- Approximation of one by the squarefree closure in the indicated physical norm. -/
def HasPhysicalApproximationAt (p : ℝ) : Prop :=
  ∃ G : ℕ → QHilbert, (∀ j, G j ∈ closure) ∧
    (∀ j, Summable (fun n => positiveQWeight n * |qSequence (qOne - G j) n| ^ p)) ∧
    Tendsto (fun j => (∑' n, positiveQWeight n * |qSequence (qOne - G j) n| ^ p) ^
      (1 / p)) atTop (𝓝 0)

theorem weighted_pairing_conjugate {p q : ℝ} (hpq : p.HolderConjugate q)
    (x y : QHilbert)
    (hx : Summable fun k => positiveQWeight k * |qSequence x k| ^ p)
    (hy : Summable fun k => positiveQWeight k * |qSequence y k| ^ q) :
    |inner ℝ x y| ≤ (∑' k, positiveQWeight k * |qSequence x k| ^ p) ^ (1 / p) *
      (∑' k, positiveQWeight k * |qSequence y k| ^ q) ^ (1 / q) := by
  let a := fun k => positiveQWeight k ^ (1 / p) * |qSequence x k|
  let b := fun k => positiveQWeight k ^ (1 / q) * |qSequence y k|
  have ha (k : ℕ) : (a k) ^ p = positiveQWeight k * |qSequence x k| ^ p := by
    dsimp only [a]
    rw [Real.mul_rpow (Real.rpow_nonneg (positiveQWeight_nonneg _) _) (abs_nonneg _),
      ← Real.rpow_mul (positiveQWeight_nonneg _)]
    simp [hpq.ne_zero]
  have hb (k : ℕ) : (b k) ^ q = positiveQWeight k * |qSequence y k| ^ q := by
    dsimp only [b]
    rw [Real.mul_rpow (Real.rpow_nonneg (positiveQWeight_nonneg _) _) (abs_nonneg _),
      ← Real.rpow_mul (positiveQWeight_nonneg _)]
    simp [hpq.symm.ne_zero]
  have he : 1 / p + 1 / q = 1 := by simpa only [one_div] using hpq.inv_add_inv_eq_one
  have hab (k : ℕ) : a k * b k = ‖positiveQWeight k * qSequence x k * qSequence y k‖ := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (positiveQWeight_nonneg k)]
    dsimp only [a, b]
    calc
      _ = (positiveQWeight k ^ (1 / p) * positiveQWeight k ^ (1 / q)) *
        |qSequence x k| * |qSequence y k| := by ring
      _ = _ := by
        rw [← Real.rpow_add' (positiveQWeight_nonneg k) (by rw [he]; exact one_ne_zero),
          he, Real.rpow_one]
  have H := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg (f := a) (g := b) hpq
    (fun k => mul_nonneg (Real.rpow_nonneg (positiveQWeight_nonneg _) _) (abs_nonneg _))
    (fun k => mul_nonneg (Real.rpow_nonneg (positiveQWeight_nonneg _) _) (abs_nonneg _))
    (by simpa only [ha] using hx) (by simpa only [hb] using hy)
  simp only [ha, hb, hab] at H
  rw [qInner_weighted, ← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm (qSequence_product_summable x y).norm).trans H

theorem annihilator_mean_zero_of_conjugate_moment {p q : ℝ} (hpq : p.HolderConjugate q)
    (happrox : HasPhysicalApproximationAt p) (w : QHilbert) (hw : w ∈ closureᗮ)
    (hsw : Summable fun n => positiveQWeight n * |qSequence w n| ^ q) :
    inner ℝ qOne w = 0 := by
  obtain ⟨G, hG, hs, ht⟩ := happrox
  let D := (∑' n, positiveQWeight n * |qSequence w n| ^ q) ^ (1 / q)
  have hle (j : ℕ) := weighted_pairing_conjugate hpq (qOne - G j) w (hs j) hsw
  simp only [inner_sub_left, Submodule.inner_right_of_mem_orthogonal (hG _) hw,
    sub_zero] at hle
  have ht' := ht.mul_const D
  rw [zero_mul] at ht'
  exact abs_nonpos_iff.mp (le_of_tendsto_of_tendsto' tendsto_const_nhds ht' hle)

private theorem witness_real_moment {q : ℝ} (hq : 0 ≤ q)
    (hd : Summable (fun n : ℕ => positiveQWeight n * |qSequence displacement n| ^ q)) :
    Summable (fun n : ℕ => positiveQWeight n * |qSequence witness n| ^ q) := by
  obtain ⟨C, hC⟩ := B_physical_bounded pResidual
  have hc := (abs_nonneg _).trans (hC 0)
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (positiveQWeight_nonneg n) (Real.rpow_nonneg (abs_nonneg _) _))
    _ (((positiveQWeight_summable.mul_right (C ^ q)).add hd).mul_left ((2 : ℝ) ^ q))
  intro n
  let a := |qSequence displacement n|
  have ha : 0 ≤ a := abs_nonneg _
  have hw : qSequence witness n = qSequence (B pResidual) n - qSequence displacement n := by
    change qSequenceLinear (B pResidual - displacement) n = _
    rw [map_sub]
    rfl
  have htri : |qSequence witness n| ≤ C + a := by
    rw [hw]
    exact (abs_sub _ _).trans (add_le_add (hC n) le_rfl)
  have hmax : |qSequence witness n| ≤ 2 * max C a := by
    linarith [le_max_left C a, le_max_right C a]
  have hpow : (max C a) ^ q ≤ C ^ q + a ^ q := by
    rcases le_total C a with h | h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (Real.rpow_nonneg hc _)
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right (Real.rpow_nonneg ha _)
  have hh := Real.rpow_le_rpow (abs_nonneg _) hmax hq
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_trans hc (le_max_left C a))] at hh
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by norm_num) _))
  calc
    _ ≤ positiveQWeight n * (2 ^ q * (C ^ q + a ^ q)) :=
      mul_le_mul_of_nonneg_left hh' (positiveQWeight_nonneg n)
    _ = _ := by dsimp [a]; ring

/-- A displacement q-moment suffices when p-approximation is supplied at its conjugate. -/
theorem riemannHypothesis_of_displacement_conjugate_moment {p q : ℝ}
    (hpq : p.HolderConjugate q) (happrox : HasPhysicalApproximationAt p)
    (hd : Summable fun n => positiveQWeight n * |qSequence displacement n| ^ q) :
    RiemannHypothesis := by
  have hmean := annihilator_mean_zero_of_conjugate_moment hpq happrox witness
    witness_mem_orthogonal (witness_real_moment hpq.symm.nonneg hd)
  have hr := residual_eq_zero_of_witness_mean_zero hmean
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr
      (Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm))

end RiemannResearch.RH.QSquarefreeFiniteDisplacement
