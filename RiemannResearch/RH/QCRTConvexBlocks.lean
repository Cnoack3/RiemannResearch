/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QSquarefreeAffineHead
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.QCRTCoprimeApproximation
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.NumberTheory.Primorial
import RiemannResearch.RH.QCRTMinimumEnergy
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual minimum-energy CRT blocks and their fixed-head benchmark

Source: user-provided Minimum_Energy_Exact_Head_Research_Agenda_2026-10-28.md,
priorities 4 and 5. Finite convex blocks preserve the smallest head, and they
are dominated by the full minimum at their common period with that head.
The algebra and head statements also hold for signed affine coefficients.
All energies and mixed products use complete Q; no cofinal bound is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTConvexBlocks
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeLatticePackets QSquarefreeAffineHead
open QResidueHeadSpace QCRTMinimumEnergy QCRTCoprimeApproximation

/-- A finite affine block of the actual minimum-energy family. -/
def finiteBlock {n : ℕ} (a : Fin n → ℝ) (j : Fin n → ℕ) : QHilbert :=
  ∑ i, a i • minimumEnergyApproximant (j i)

theorem finiteBlock_legal {n : ℕ} (a : Fin n → ℝ) (j : Fin n → ℕ) :
    finiteBlock a j ∈ qSquarefreeCRTSpan := by
  exact qSquarefreeCRTSpan.sum_mem fun i _ =>
    qSquarefreeCRTSpan.smul_mem _ (minimumEnergyApproximant_legal (j i))

theorem finiteBlock_exact_head {n : ℕ} (a : Fin n → ℝ) (j : Fin n → ℕ)
    (ha : ∑ i, a i = 1) (k : ℕ) (hj : ∀ i, k ≤ j i)
    (r : ℕ) (hr : 0 < r) (hrk : r ≤ k + 1) :
    qSequence (finiteBlock a j) r = 1 := by
  change qSequenceLinear (∑ i, a i • minimumEnergyApproximant (j i)) r = 1
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ = ∑ i, a i * 1 := by
      apply Finset.sum_congr rfl
      intro i _
      change a i * qSequence (minimumEnergyApproximant (j i)) r = a i * 1
      rw [minimumEnergyApproximant_exact_head (j i) r hr (by have := hj i; omega)]
    _ = 1 := by simpa only [mul_one] using ha

/-- The full signed mixed-term energy; no off-diagonal term is discarded. -/
theorem finiteBlock_energy {n : ℕ} (a : Fin n → ℝ) (j : Fin n → ℕ) :
    ‖finiteBlock a j‖ ^ 2 =
      ∑ i, ∑ l, a i * a l * inner ℝ
        (minimumEnergyApproximant (j i)) (minimumEnergyApproximant (j l)) := by
  rw [← real_inner_self_eq_norm_sq, finiteBlock, sum_inner]
  simp_rw [real_inner_smul_left, inner_sum, real_inner_smul_right, Finset.mul_sum]
  simp only [mul_assoc]

/-- A common larger period contains every summand and their finite block. -/
theorem finiteBlock_mem_stage {n : ℕ} (a : Fin n → ℝ) (j : Fin n → ℕ)
    (M : ℕ) (hM : ∀ i, primorial (j i + 2) ∣ M) :
    finiteBlock a j ∈ divisorStage M := by
  apply (divisorStage M).sum_mem
  intro i _
  apply (divisorStage M).smul_mem
  apply divisorStage_mono (hM i)
  rw [divisorStage_eq_dictionary _ (primorial_pos _)]
  exact minimumEnergyApproximant_mem_dictionary (j i)

/-- The exact remainder shows that the full fixed-head minimum dominates any block.
This compares a block to a genuinely larger-period, slower-head schedule. -/
theorem finiteBlock_fixed_head_completion {n : ℕ} (a : Fin n → ℝ)
    (j : Fin n → ℕ) (ha : ∑ i, a i = 1) (k m : ℕ)
    (hkm : k ≤ m) (hj : ∀ i, k ≤ j i)
    (hM : ∀ i, j i ≤ m) :
    ‖finiteBlock a j‖ ^ 2 =
      ‖exactHeadAdjustment (conductors (primorial (m + 2))) (k + 1) (approximant m)‖ ^ 2 +
      ‖finiteBlock a j -
        exactHeadAdjustment (conductors (primorial (m + 2))) (k + 1) (approximant m)‖ ^ 2 := by
  apply exactHeadAdjustment_completion _ _ _ _ (seed_mem_dictionary m)
  · rw [← divisorStage_eq_dictionary _ (primorial_pos _)]
    exact finiteBlock_mem_stage a j _
      (fun i => primorial_dvd_primorial (Nat.add_le_add_right (hM i) 2))
  · intro r hr hrk
    rw [finiteBlock_exact_head a j ha k hj r hr hrk,
      approximant_exact_head m r hr (by omega)]

theorem fixed_head_minimum_le_finiteBlock {n : ℕ} (a : Fin n → ℝ)
    (j : Fin n → ℕ) (ha : ∑ i, a i = 1) (k m : ℕ)
    (hkm : k ≤ m) (hj : ∀ i, k ≤ j i)
    (hM : ∀ i, j i ≤ m) :
    ‖exactHeadAdjustment (conductors (primorial (m + 2))) (k + 1) (approximant m)‖ ^ 2 ≤
      ‖finiteBlock a j‖ ^ 2 := by
  rw [finiteBlock_fixed_head_completion a j ha k m hkm hj hM]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Exact two-stage variance identity, including the improvement term. -/
theorem two_stage_variance (i j : ℕ) (t : ℝ) :
    ‖(1 - t) • minimumEnergyApproximant i + t • minimumEnergyApproximant j‖ ^ 2 =
      (1 - t) * ‖minimumEnergyApproximant i‖ ^ 2 +
        t * ‖minimumEnergyApproximant j‖ ^ 2 -
        t * (1 - t) * ‖minimumEnergyApproximant i - minimumEnergyApproximant j‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real]
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- Across a plateau of the primorial period, mixing a later exact head into an
 earlier one adds exactly a nonnegative squared distance. Period growth is needed
 for any improvement beyond the earliest head minimum. -/
theorem same_period_two_stage_energy (i j : ℕ) (t : ℝ) (hij : i ≤ j)
    (hperiod : primorial (i + 2) = primorial (j + 2)) :
    ‖(1 - t) • minimumEnergyApproximant i + t • minimumEnergyApproximant j‖ ^ 2 =
      ‖minimumEnergyApproximant i‖ ^ 2 +
        t ^ 2 * ‖minimumEnergyApproximant j - minimumEnergyApproximant i‖ ^ 2 := by
  have hm : minimumEnergyApproximant j ∈ divisorStage (primorial (i + 2)) := by
    rw [hperiod, divisorStage_eq_dictionary _ (primorial_pos _)]
    exact minimumEnergyApproximant_mem_dictionary j
  have hh : ∀ r, 0 < r → r ≤ i + 1 → qSequence (minimumEnergyApproximant j) r = 1 := by
    intro r hr hri
    exact minimumEnergyApproximant_exact_head j r hr (by omega)
  have hc := minimumEnergyApproximant_completion i (minimumEnergyApproximant j) hm hh
  rw [two_stage_variance, hc, norm_sub_rev (minimumEnergyApproximant i)
    (minimumEnergyApproximant j)]
  ring

end RiemannResearch.RH.QCRTConvexBlocks
