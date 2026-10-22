/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCovarianceInverse
import RiemannResearch.RH.QCovarianceInvertibility
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Tactic.Linarith
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QDivisorWaveletFactorization
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

/-!
# An exact parity coordinate of the actual Q optimizer

Source: the user's Q approximation program, 13 October 2026. The single
parity coordinate is three times the complete residual energy. This is an
exact identity for the actual finite projections, and does not supply an
unconditional zero limit for that coordinate.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.QDivisorHilbert
open ZetaTwoHilbert

/-- The parity wavelet already lies in the affine span of one legal atom. -/
theorem divisorWavelet_two :
    divisorWavelet 2 = (3 : ℝ) • qOne - (8 : ℝ) • qResidue 2 := by
  have htwo (n : ℕ) : qDivisorWavelet 2 n =
      4 * (if 2 ∣ n then (1 : ℝ) else 0) - 1 := by
    have h := divisorWaveletAF_prime_pow_succ 2 0 n Nat.prime_two
    norm_num [divisorWaveletAF_apply, scaledDivisorAF] at h
    by_cases hd : 2 ∣ n <;> simpa [hd] using h
  apply qSequence_injective
  funext n
  cases n with
  | zero => simp
  | succ n =>
    change qSequenceLinear (divisorWavelet 2) (n + 1) =
      qSequenceLinear ((3 : ℝ) • qOne - (8 : ℝ) • qResidue 2) (n + 1)
    rw [map_sub, map_smul, map_smul]
    change qSequence (divisorWavelet 2) (n + 1) =
      3 * qSequence qOne (n + 1) - 8 * qSequence (qResidue 2) (n + 1)
    rw [qSequence_divisorWavelet_succ, htwo, qSequence_qOne, qSequence_qResidue]
    have hcases : (n + 1) % 2 = 0 ∨ (n + 1) % 2 = 1 := by omega
    rcases hcases with h | h
    · have hd : 2 ∣ n + 1 := Nat.dvd_of_mod_eq_zero h
      norm_num [qOneSequence, ArithmeticCumulative.residueFraction, h, hd]
    · have hd : ¬ 2 ∣ n + 1 := by
        intro hd
        have hz := Nat.mod_eq_zero_of_dvd hd
        omega
      norm_num [qOneSequence, ArithmeticCumulative.residueFraction, h, hd]

end RiemannResearch.RH.QDivisorHilbert

namespace RiemannResearch.RH.QFullResidueProjection
open ZetaTwoHilbert QDivisorHilbert
open RiemannResearch.Analysis.ExhaustiveWalk

/-- Orthogonality of the literal inverse-Gram candidate to its stage. -/
theorem residual_inner_stage (n : ℕ) (v : QHilbert) (hv : v ∈ stage n) :
    inner ℝ (qOne - candidate n) v = 0 := by
  rw [candidate_eq_projection, real_inner_comm]
  exact ((stage n).mem_orthogonal _).mp
    (Submodule.sub_starProjection_mem_orthogonal qOne) v hv

/-- For an actual optimizer, the residual mean equals its full energy. -/
theorem residual_inner_qOne (n : ℕ) :
    inner ℝ (qOne - candidate n) qOne = ‖qOne - candidate n‖ ^ 2 := by
  have ho := residual_inner_stage n (candidate n) (candidate_mem_stage n)
  calc
    inner ℝ (qOne - candidate n) qOne =
        inner ℝ (qOne - candidate n) (qOne - candidate n) := by
      rw [inner_sub_right, ho, sub_zero]
    _ = ‖qOne - candidate n‖ ^ 2 := real_inner_self_eq_norm_sq _

theorem qResidue_two_mem_stage (n : ℕ) (hn : 0 < n) : qResidue 2 ∈ stage n := by
  change qResidue 2 ∈ Submodule.span ℝ
    (Set.range (fun i : Fin n => qResidue (id (i : ℕ) + 2)))
  exact Submodule.subset_span ⟨⟨0, hn⟩, rfl⟩

/-- All other modes are retained: a single mode equals three times their
complete Parseval energy, because this residual comes from the optimizer. -/
theorem residual_parity_coordinate (n : ℕ) (hn : 0 < n) :
    inner ℝ (qOne - candidate n) (divisorWavelet 2) =
      3 * ‖qOne - candidate n‖ ^ 2 := by
  rw [divisorWavelet_two, inner_sub_right, inner_smul_right, inner_smul_right,
    residual_inner_qOne, residual_inner_stage n (qResidue 2)
      (qResidue_two_mem_stage n hn), mul_zero, sub_zero]

/-- Explicit arithmetic spelling of the single parity coordinate. -/
theorem residue_parity_sum (n : ℕ) (hn : 0 < n) :
    -(∑ i : Fin n, coefficients n i * qResidueDivisorCoefficient (conductor n i) 2) =
      3 * ‖qOne - candidate n‖ ^ 2 := by
  have h := residual_parity_coordinate n hn
  have hone : inner ℝ qOne (divisorWavelet 2) = 0 := by
    simpa using qOne_divisorWavelet_inner (2 : ℕ+)
  simpa only [inner_sub_left, hone, candidate, QCovarianceInverse.qSynthesis,
    sum_inner, real_inner_smul_left, qResidue_divisorWavelet_inner, zero_sub] using h

/-- Every finite candidate vanishes at a positive common-period coordinate. -/
theorem candidate_ne_qOne (n : ℕ) : candidate n ≠ qOne := by
  intro h
  have he : QCovarianceInverse.qSynthesis (conductor n) (coefficients n) =
      (1 : ℝ) • qOne := by
    simpa only [candidate, one_smul] using h
  have hz := QCovarianceInvertibility.qSynthesis_eq_const_forces_zero
    (conductor n) (conductor_gt_one n) (coefficients n) 1 he
  norm_num at hz

theorem residual_energy_pos (n : ℕ) : 0 < ‖qOne - candidate n‖ ^ 2 := by
  exact pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm (candidate_ne_qOne n)))) 2

/-- Exact finite cancellation of this coordinate is impossible for an optimizer;
the desired result must be a limiting estimate. -/
theorem residual_parity_coordinate_pos (n : ℕ) (hn : 0 < n) :
    0 < inner ℝ (qOne - candidate n) (divisorWavelet 2) := by
  rw [residual_parity_coordinate n hn]
  exact mul_pos (by norm_num) (residual_energy_pos n)

/-- The exact zero-energy target is still membership in the legal closure. -/
theorem residual_energy_tendsto_zero_iff :
    Tendsto (fun n => ‖qOne - candidate n‖ ^ 2) atTop (𝓝 0) ↔
      qOne ∈ closure := by
  have h := walkError_tendsto_zero_iff (fun i => qResidue (i + 2))
    id Function.surjective_id qOne
  change Tendsto (fun n => ‖qOne - (stage n).starProjection qOne‖ ^ 2)
    atTop (𝓝 0) ↔ qOne ∈ closure at h
  simpa only [← candidate_eq_projection] using h

/-- The single parity coordinate tends to zero exactly when the target
belongs to the legal residue closure. No zero-limit estimate is assumed. -/
theorem residual_parity_tendsto_zero_iff :
    Tendsto (fun n => inner ℝ (qOne - candidate n) (divisorWavelet 2))
      atTop (𝓝 0) ↔ qOne ∈ closure := by
  have heq :
      (fun n => inner ℝ (qOne - candidate n) (divisorWavelet 2)) =ᶠ[atTop]
        (fun n => 3 * ‖qOne - candidate n‖ ^ 2) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact residual_parity_coordinate n (by omega)
  rw [tendsto_congr' heq]
  constructor
  · intro h
    apply residual_energy_tendsto_zero_iff.mp
    have hh := h.const_mul (1 / 3 : ℝ)
    simpa only [← mul_assoc, show (1 / 3 : ℝ) * 3 = 1 by norm_num,
      one_mul, mul_zero] using hh
  · intro h
    simpa only [mul_zero] using
      (residual_energy_tendsto_zero_iff.mpr h).const_mul (3 : ℝ)

end RiemannResearch.RH.QFullResidueProjection
