/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDivisorProjectionDPP
import RiemannResearch.RH.QOptimizerParity
import RiemannResearch.Probability.DeterminantalEntry
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The constant-parity block of a legal Q projection DPP

Source: user-provided legal-residue DPP proposal, 14 October 2026.
The exact parity wavelet identity is reused from QOptimizerParity.
Containing the conductor-2 residue forces a rank-one complementary block:
K(1,2) = -sqrt(3)(1-K(1,1)), K(2,2) = 3K(1,1)-2.
The actual joint occupation law is 4K(1,1)-3. These exact finite identities
give a lower bound of 3/4, without assuming a zero vacancy limit.
-/

noncomputable section
open MeasureTheory
namespace RiemannResearch.RH.QDivisorHilbert
open ZetaTwoHilbert

theorem normalized_two :
    normalizedDivisorWavelet 2 =
      (Real.sqrt 3)⁻¹ • ((3 : ℝ) • qOne - (8 : ℝ) • qResidue 2) := by
  have hJ : qJordanTwo 2 = 3 := by
    norm_num [qJordanTwo, ZetaTwoProbability.valuationWaveletWeight]
  simp only [normalizedDivisorWavelet, show ((2 : ℕ+) : ℕ) = 2 by rfl,
    hJ, divisorWavelet_two]

end RiemannResearch.RH.QDivisorHilbert

namespace RiemannResearch.RH.QDivisorProjectionDPP
open ZetaTwoHilbert QDivisorHilbert
variable (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]

theorem parity_residual (h2 : qResidue 2 ∈ S) :
    normalizedDivisorWavelet 2 - S.starProjection (normalizedDivisorWavelet 2) =
      Real.sqrt 3 • (qOne - S.starProjection qOne) := by
  have hs : (Real.sqrt 3)⁻¹ * 3 = Real.sqrt 3 := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have hn : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp [hn]
    nlinarith
  rw [normalized_two, map_smul, map_sub, map_smul, map_smul,
    Submodule.starProjection_eq_self_iff.mpr h2]
  calc
    _ = ((Real.sqrt 3)⁻¹ * 3) • (qOne - S.starProjection qOne) := by
      simp only [smul_smul, smul_sub]
      abel
    _ = _ := by rw [hs]

theorem constant_parity_kernel (h2 : qResidue 2 ∈ S) :
    modeKernel S 1 2 = -Real.sqrt 3 * (1 - modeKernel S 1 1) := by
  have h := RiemannResearch.Analysis.ProjectionDPP.holeKernel_eq
    S normalizedDivisorWavelet 1 2
  have he := modeKernel_vacancy_energy S 1
  rw [normalized_one] at he
  rw [RiemannResearch.Analysis.ProjectionDPP.holeKernel, normalized_one,
    parity_residual S h2, inner_smul_right, real_inner_self_eq_norm_sq,
    ] at h
  have hi : inner ℝ qOne (normalizedDivisorWavelet 2) = 0 := by
    rw [← normalized_one, mode_inner]
    norm_num
  rw [hi, zero_sub] at h
  change Real.sqrt 3 * ‖qOne - S.starProjection qOne‖ ^ 2 = -modeKernel S 1 2 at h
  rw [← he] at h
  linarith

theorem parity_diagonal (h2 : qResidue 2 ∈ S) :
    modeKernel S 2 2 = 3 * modeKernel S 1 1 - 2 := by
  have h := modeKernel_vacancy_energy S 2
  rw [parity_residual S h2, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at h
  have he := modeKernel_vacancy_energy S 1
  rw [normalized_one] at he
  rw [← he] at h
  linarith

theorem constant_parity_both (h2 : qResidue 2 ∈ S) :
    (modeLaw S).real {x | x 1 = true ∧ x 2 = true} =
      4 * modeKernel S 1 1 - 3 := by
  have h := (modeLaw_isDPP S).two_point (i := 1) (j := 2) (by norm_num)
  change (modeLaw S).real {x | x 1 = true ∧ x 2 = true} = _ at h
  have hsym : modeKernel S 2 1 = modeKernel S 1 2 :=
    RiemannResearch.Analysis.ProjectionDPP.kernel_symmetric S normalizedDivisorWavelet 2 1
  rw [parity_diagonal S h2, hsym, constant_parity_kernel S h2,
    ← pow_two, mul_pow, neg_sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at h
  calc
    _ = _ := h
    _ = _ := by ring

theorem constant_occupation_lower (h2 : qResidue 2 ∈ S) :
    (3 / 4 : ℝ) ≤ (modeLaw S).real {x | x 1 = true} := by
  have hn : 0 ≤ (modeLaw S).real {x | x 1 = true ∧ x 2 = true} := measureReal_nonneg
  rw [constant_parity_both S h2, ← modeLaw_occupation] at hn
  linarith
end RiemannResearch.RH.QDivisorProjectionDPP
