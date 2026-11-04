/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QLegalResidueDPP
import RiemannResearch.RH.QParityProjectionDefect
import RiemannResearch.RH.QSquarefreeJumpDistance
import RiemannResearch.RH.QInitialResponseImprovement
import RiemannResearch.RH.QDivisorModeLegality
import RiemannResearch.RH.QDivisorHilbertBasis
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact divisor-mode correlation budget for the squarefree residue DPP

Source: the user's residue-basis and DPP research request, 4 November 2026.
The projection-DPP terminology follows Hough, Krishnapur, Peres and Virag,
https://arxiv.org/abs/math/0503110. The complete divisor basis and the
squarefree stage, parity, and strict conductor-3 results are reused.

Parseval gives the whole squared kernel row. Removing the constant and parity
sites gives the exact energy D(1-4D), and strict improvement from g_3 makes
its vanishing equivalent to D tending to zero. The final RH theorem is
conditional on that explicitly displayed limit; no such limit is proved.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
open RiemannResearch.RH
open ZetaTwoHilbert QDivisorHilbert QDivisorProjectionDPP
open RiemannResearch.Analysis.ProjectionDPP
open RiemannResearch.Analysis.ExhaustiveWalk

namespace RiemannResearch.RH.QBasisDPPBridge
variable (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]

theorem row_energy (i : ℕ+) :
    (∑' j : ℕ+, (modeKernel S i j) ^ 2) = modeKernel S i i := by
  have hcoeff (j : ℕ+) :
      inner ℝ (S.starProjection (normalizedDivisorWavelet i)) (normalizedDivisorWavelet j) =
        modeKernel S i j := by
    have ho : inner ℝ (S.starProjection (normalizedDivisorWavelet i))
        (normalizedDivisorWavelet j - S.starProjection (normalizedDivisorWavelet j)) = 0 :=
      (S.mem_orthogonal _).mp
        (Submodule.sub_starProjection_mem_orthogonal (normalizedDivisorWavelet j)) _
        (S.starProjection_apply_mem (normalizedDivisorWavelet i))
    simp only [inner_sub_right] at ho
    change inner ℝ (S.starProjection (normalizedDivisorWavelet i)) (normalizedDivisorWavelet j) =
      inner ℝ (S.starProjection (normalizedDivisorWavelet i))
        (S.starProjection (normalizedDivisorWavelet j))
    linarith
  have h := divisorHilbertBasis.tsum_inner_mul_inner
    (S.starProjection (normalizedDivisorWavelet i))
    (S.starProjection (normalizedDivisorWavelet i))
  calc
    (∑' j : ℕ+, (modeKernel S i j) ^ 2) =
        ∑' j : ℕ+, inner ℝ (S.starProjection (normalizedDivisorWavelet i))
          (divisorHilbertBasis j) * inner ℝ (divisorHilbertBasis j)
          (S.starProjection (normalizedDivisorWavelet i)) := by
      apply tsum_congr
      intro j
      have he : inner ℝ (normalizedDivisorWavelet j)
          (S.starProjection (normalizedDivisorWavelet i)) = modeKernel S i j := by
        rw [real_inner_comm]
        exact hcoeff j
      simp only [divisorHilbertBasis_apply, hcoeff, he, pow_two]
    _ = inner ℝ (S.starProjection (normalizedDivisorWavelet i))
      (S.starProjection (normalizedDivisorWavelet i)) := h
    _ = modeKernel S i i := rfl

theorem row_off_diagonal_energy :
    (∑' j : ℕ+, (modeKernel S 1 j) ^ 2) - (modeKernel S 1 1) ^ 2 =
      modeKernel S 1 1 * (1 - modeKernel S 1 1) := by
  rw [row_energy]
  ring

theorem row_after_parity_energy (h2 : qResidue 2 ∈ S) :
    (∑' j : ℕ+, (modeKernel S 1 j) ^ 2) - (modeKernel S 1 1) ^ 2 -
      (modeKernel S 1 2) ^ 2 =
      (1 - modeKernel S 1 1) * (4 * modeKernel S 1 1 - 3) := by
  rw [row_energy, constant_parity_kernel S h2, mul_pow, neg_sq,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

theorem other_mode_energy_zero_iff (h2 : qResidue 2 ∈ S) (h3 : qResidue 3 ∈ S) :
    ((∑' j : ℕ+, (modeKernel S 1 j) ^ 2) - (modeKernel S 1 1) ^ 2 -
      (modeKernel S 1 2) ^ 2 = 0) ↔ qOne ∈ S := by
  rw [row_after_parity_energy S h2]
  have hd : 1 - modeKernel S 1 1 = ‖qOne - S.starProjection qOne‖ ^ 2 := by
    simpa only [normalized_one] using modeKernel_vacancy_energy S 1
  have ht := QParityProjectionDefect.error_lt_quarter S h2 h3
  rw [← hd] at ht
  have hf : 0 < 4 * modeKernel S 1 1 - 3 := by linarith
  constructor
  · intro h
    have hz := (mul_eq_zero.mp h).resolve_right (ne_of_gt hf)
    have hk : modeKernel S 1 1 = 1 := by linarith
    apply (constant_occupation_one_iff S).mp
    rw [modeLaw_occupation]
    exact hk
  · intro h
    have hk : modeKernel S 1 1 = 1 := by
      have he := (constant_occupation_one_iff S).mpr h
      rwa [modeLaw_occupation] at he
    rw [hk]
    ring

/-- The kernel row is square summable in the full divisor-wavelet basis. -/
theorem row_summable (i : ℕ+) : Summable (fun j : ℕ+ => (modeKernel S i j) ^ 2) := by
  have hc (j : ℕ+) :
      inner ℝ (normalizedDivisorWavelet j)
        (S.starProjection (normalizedDivisorWavelet i)) = modeKernel S i j := by
    have ho : inner ℝ (S.starProjection (normalizedDivisorWavelet i))
        (normalizedDivisorWavelet j - S.starProjection (normalizedDivisorWavelet j)) = 0 :=
      (S.mem_orthogonal _).mp
        (Submodule.sub_starProjection_mem_orthogonal (normalizedDivisorWavelet j)) _
        (S.starProjection_apply_mem (normalizedDivisorWavelet i))
    simp only [inner_sub_right] at ho
    rw [real_inner_comm]
    change _ = inner ℝ (S.starProjection (normalizedDivisorWavelet i))
      (S.starProjection (normalizedDivisorWavelet j))
    linarith
  have hs := Orthonormal.inner_products_summable
    (S.starProjection (normalizedDivisorWavelet i)) normalizedDivisorWavelet_orthonormal
  simpa only [hc, Real.norm_eq_abs, sq_abs] using hs

def otherModeEnergy : ℝ :=
  ∑' j : {j : ℕ+ // j ∉ ({1, 2} : Finset ℕ+)}, (modeKernel S 1 j.val) ^ 2

theorem otherModeEnergy_eq_sub :
    otherModeEnergy S = (∑' j : ℕ+, (modeKernel S 1 j) ^ 2) -
      (modeKernel S 1 1) ^ 2 - (modeKernel S 1 2) ^ 2 := by
  classical
  have h := (row_summable S 1).sum_add_tsum_subtype_compl ({1, 2} : Finset ℕ+)
  have hf : (∑ j ∈ ({1, 2} : Finset ℕ+), (modeKernel S 1 j) ^ 2) =
      (modeKernel S 1 1) ^ 2 + (modeKernel S 1 2) ^ 2 := by simp
  rw [hf] at h
  dsimp only [otherModeEnergy]
  linarith

theorem otherModeEnergy_exact (h2 : qResidue 2 ∈ S) :
    otherModeEnergy S =
      (1 - modeKernel S 1 1) * (4 * modeKernel S 1 1 - 3) := by
  rw [otherModeEnergy_eq_sub, row_after_parity_energy S h2]

theorem otherModeEnergy_zero_iff (h2 : qResidue 2 ∈ S) (h3 : qResidue 3 ∈ S) :
    otherModeEnergy S = 0 ↔ qOne ∈ S := by
  rw [otherModeEnergy_eq_sub]
  exact other_mode_energy_zero_iff S h2 h3

theorem squarefree_stage_le_arithmetic_span (n : ℕ) :
    ZetaTwoOptimizerStage.stage n ≤ ZetaTwoProbability.qSquarefreeCRTSpan := by
  unfold ZetaTwoOptimizerStage.stage walkSpan ZetaTwoProbability.qSquarefreeCRTSpan
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  by_cases hs : Squarefree ((i : ℕ) + 2)
  · simp only [ZetaTwoOptimizerStage.squarefreeAtom, id_eq, if_pos hs]
    exact Submodule.subset_span ⟨⟨i.val + 2, by omega, hs⟩, rfl⟩
  · simp [ZetaTwoOptimizerStage.squarefreeAtom, hs]

theorem squarefree_mode_three_vacancy_lower (n : ℕ) :
    27 / (80 * ZetaTwoProbability.zetaTwo) ≤
      (modeLaw (ZetaTwoOptimizerStage.stage n)).real {x | x 3 = false} := by
  rw [modeLaw_vacancy_energy]
  have hm : (ZetaTwoOptimizerStage.stage n).starProjection (normalizedDivisorWavelet 3) ∈
      ZetaTwoProbability.qSquarefreeCRTSpan.topologicalClosure :=
    ZetaTwoProbability.qSquarefreeCRTSpan.le_topologicalClosure
      (squarefree_stage_le_arithmetic_span n
        ((ZetaTwoOptimizerStage.stage n).starProjection_apply_mem (normalizedDivisorWavelet 3)))
  have h := QSquarefreeJumpDistance.squarefree_error_sq_lower_bound 2 (by decide)
    (normalizedDivisorWavelet 3) _ hm
  rw [QDivisorModeLegality.divisor_mode_three_squareJump] at h
  have hsq : Real.sqrt (8 : ℝ) ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have hs8 : (-9 / Real.sqrt (8 : ℝ)) ^ 2 = (81 / 8 : ℝ) := by
    rw [div_pow, neg_sq, hsq]
    norm_num
  rw [hs8] at h
  norm_num only [Nat.cast_ofNat] at h
  have he : (81 / 8 : ℝ) /
      (2 * ZetaTwoProbability.zetaTwo * 15) =
      27 / (80 * ZetaTwoProbability.zetaTwo) := by
    have hz : ZetaTwoProbability.zetaTwo ≠ 0 :=
      ne_of_gt ZetaTwoProbability.zetaTwo_pos
    field_simp [hz]
    ring
  rw [he] at h
  exact h

theorem squarefree_otherModeEnergy_exact (n : ℕ) (hn : 0 < n) :
    otherModeEnergy (ZetaTwoOptimizerStage.stage n) =
      ZetaTwoOptimizerStage.error n * (1 - 4 * ZetaTwoOptimizerStage.error n) := by
  rw [otherModeEnergy_exact _ (QLegalResidueDPP.qResidue_two_mem_squarefree_stage n hn)]
  have he : 1 - modeKernel (ZetaTwoOptimizerStage.stage n) 1 1 =
      ZetaTwoOptimizerStage.error n := by
    simpa only [normalized_one, ZetaTwoOptimizerStage.error,
      ZetaTwoOptimizerStage.residual, ZetaTwoOptimizerStage.optimizer] using
        modeKernel_vacancy_energy (ZetaTwoOptimizerStage.stage n) 1
  rw [← he]
  ring

theorem squarefree_otherModeEnergy_lower (n : ℕ) (hn : 2 ≤ n) :
    (1 - 4 * ZetaTwoOptimizerStage.error 2) * ZetaTwoOptimizerStage.error n ≤
      otherModeEnergy (ZetaTwoOptimizerStage.stage n) := by
  rw [squarefree_otherModeEnergy_exact n (by omega)]
  have hle : ZetaTwoOptimizerStage.error n ≤ ZetaTwoOptimizerStage.error 2 := by
    exact walkError_antitone ZetaTwoOptimizerStage.squarefreeAtom id qOne hn
  have hn0 : 0 ≤ ZetaTwoOptimizerStage.error n :=
    sq_nonneg ‖ZetaTwoOptimizerStage.residual n‖
  nlinarith

theorem squarefree_otherModeEnergy_tendsto_zero_iff :
    Tendsto (fun n => otherModeEnergy (ZetaTwoOptimizerStage.stage n)) atTop (𝓝 0) ↔
      Tendsto ZetaTwoOptimizerStage.error atTop (𝓝 0) := by
  have hc : 0 < 1 - 4 * ZetaTwoOptimizerStage.error 2 := by
    have h := QCanonicalInnovation.error_two_lt_quarter
    linarith
  constructor
  · intro h
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall (fun n => sq_nonneg ‖ZetaTwoOptimizerStage.residual n‖)
    · filter_upwards [eventually_ge_atTop 2] with n hn
      apply (le_div_iff₀ hc).mpr
      simpa only [mul_comm] using squarefree_otherModeEnergy_lower n hn
    · simpa only [zero_div] using h.div_const (1 - 4 * ZetaTwoOptimizerStage.error 2)
  · intro h
    have heq : (fun n => otherModeEnergy (ZetaTwoOptimizerStage.stage n)) =ᶠ[atTop]
        (fun n => ZetaTwoOptimizerStage.error n *
          (1 - 4 * ZetaTwoOptimizerStage.error n)) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact squarefree_otherModeEnergy_exact n (by omega)
    rw [tendsto_congr' heq]
    have hfactor : Tendsto (fun n => 1 - 4 * ZetaTwoOptimizerStage.error n) atTop (𝓝 1) := by
      simpa only [mul_zero, sub_zero] using
        (tendsto_const_nhds.sub (h.const_mul 4))
    simpa only [zero_mul] using h.mul hfactor

theorem riemannHypothesis_of_squarefree_otherModeEnergy_tendsto_zero
    (h : Tendsto (fun n => otherModeEnergy (ZetaTwoOptimizerStage.stage n)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply QLegalResidueDPP.riemannHypothesis_of_squarefreeOccupation_tendsto_one
  apply QLegalResidueDPP.squarefreeOccupation_tendsto_one_iff.mpr
  apply ZetaTwoOptimizerStage.error_tendsto_zero_iff_mem_closure.mp
  exact squarefree_otherModeEnergy_tendsto_zero_iff.mp h

end RiemannResearch.RH.QBasisDPPBridge
