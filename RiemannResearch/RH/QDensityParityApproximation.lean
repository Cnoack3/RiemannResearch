/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import RiemannResearch.RH.QDensityMetric
import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QOptimizerParity
import RiemannResearch.RH.QCovarianceInverse
import RiemannResearch.RH.QCovarianceInvertibility
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QDivisibilityResidueCoefficients
import RiemannResearch.RH.QDivisorWaveletFactorization
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Exact finite residue fits for the single density image B g₂

Source: the user's request to approximate B g₂ by the original residue
family, 12 November 2026. Here B is the Pareto-to-Q density multiplier
QDensityMetric.B, not the shifted reciprocal operator.

The new part of B g₂ is D g₂, whose physical sequence is 1/(2n) on odd
positive integers and zero on even integers. Its actual complete
inverse-Gram fits give finite legal fits for B g₂. The matrix error and
full Parseval error are exact. Their unconditional limit is the energy
of the remaining closed-span residual, not an asserted zero.

The zero-limit criterion remains equivalent to membership of B g₂ in the
legal closure. The explicit three-coordinate interpolant supplies no
unproved tail estimate or unconditional membership assertion.
-/

noncomputable section
open Filter
open scoped BigOperators Topology Matrix

namespace RiemannResearch.RH.QDensityParityApproximation
open ZetaTwoHilbert ZetaTwoProbability QDensityMetric QReciprocalMetric
open QFullResidueProjection QCovarianceInverse QCovarianceInvertibility
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.ExhaustiveWalk

def oddReciprocal : QHilbert := D (qResidue 2)

theorem oddReciprocal_sequence (n : ℕ) :
    qSequence oddReciprocal n =
      if n % 2 = 1 then 1 / (2 * (n : ℝ)) else 0 := by
  rw [oddReciprocal, qSequence_D, qSequence_qResidue]
  unfold ArithmeticCumulative.residueFraction
  have hcases : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hcases with h | h
  · simp [h]
  · simp [h, div_eq_mul_inv, mul_comm]

theorem density_two_eq :
    B (qResidue 2) = (1 / zetaTwo) • (qResidue 2 + oddReciprocal) := by
  rfl

theorem oddReciprocal_eq_density :
    oddReciprocal = zetaTwo • B (qResidue 2) - qResidue 2 := by
  rw [density_two_eq, smul_smul]
  have hz : zetaTwo * (1 / zetaTwo) = 1 := by
    field_simp [ne_of_gt zetaTwo_pos]
  rw [hz, one_smul, add_sub_cancel_left]

theorem residue_two_mem_legalSpan : qResidue 2 ∈ legalSpan := by
  exact Submodule.subset_span ⟨0, rfl⟩

theorem density_two_mem_closure_iff :
    B (qResidue 2) ∈ closure ↔ oddReciprocal ∈ closure := by
  have hg : qResidue 2 ∈ closure :=
    legalSpan.le_topologicalClosure residue_two_mem_legalSpan
  constructor
  · intro h
    rw [oddReciprocal_eq_density]
    exact closure.sub_mem (closure.smul_mem zetaTwo h) hg
  · intro h
    rw [density_two_eq]
    exact closure.smul_mem _ (closure.add_mem hg h)

def targetCross (n : ℕ) : Fin n → ℝ :=
  fun i => inner ℝ (qResidue (conductor n i)) oddReciprocal

def targetCoefficients (n : ℕ) : Fin n → ℝ :=
  (residueGramMatrix (conductor n))⁻¹.mulVec (targetCross n)

def reciprocalFit (n : ℕ) : QHilbert :=
  qSynthesis (conductor n) (targetCoefficients n)

def densityFit (n : ℕ) : QHilbert :=
  (1 / zetaTwo) • (qResidue 2 + reciprocalFit n)

theorem reciprocalFit_eq_projection (n : ℕ) :
    reciprocalFit n = (stage n).starProjection oddReciprocal := by
  have h := synthesis_inverseCoeff_eq_projection
    (qResidue_linearIndependent (conductor n)
      (conductor_gt_one n) (conductor_injective n)) oddReciprocal
  rw [inverseCoeff_eq_inv_mulVec] at h
  exact h

theorem densityFit_mem_legalSpan (n : ℕ) : densityFit n ∈ legalSpan := by
  apply legalSpan.smul_mem
  apply legalSpan.add_mem residue_two_mem_legalSpan
  rw [reciprocalFit_eq_projection]
  exact walkSpan_le (fun i => qResidue (i + 2)) id n
    ((stage n).starProjection_apply_mem oddReciprocal)

theorem densityFit_eq_projection (n : ℕ) (hn : 0 < n) :
    densityFit n = (stage n).starProjection (B (qResidue 2)) := by
  rw [density_two_eq, map_smul, map_add,
    Submodule.starProjection_eq_self_iff.mpr (qResidue_two_mem_stage n hn)]
  rw [densityFit, reciprocalFit_eq_projection]

theorem reciprocal_error_matrix (n : ℕ) :
    ‖oddReciprocal - reciprocalFit n‖ ^ 2 =
      ‖oddReciprocal‖ ^ 2 -
        dotProduct (targetCross n) (targetCoefficients n) := by
  exact residual_matrix_value
    (qResidue_linearIndependent (conductor n)
      (conductor_gt_one n) (conductor_injective n)) oddReciprocal

theorem density_error_vector (n : ℕ) :
    B (qResidue 2) - densityFit n =
      (1 / zetaTwo) • (oddReciprocal - reciprocalFit n) := by
  rw [density_two_eq, densityFit, ← smul_sub]
  congr 1
  abel

theorem density_error_matrix (n : ℕ) :
    ‖B (qResidue 2) - densityFit n‖ ^ 2 =
      (1 / zetaTwo) ^ 2 *
        (‖oddReciprocal‖ ^ 2 -
          dotProduct (targetCross n) (targetCoefficients n)) := by
  rw [density_error_vector, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, reciprocal_error_matrix]

theorem reciprocalFit_tendsto :
    Tendsto reciprocalFit atTop (𝓝 (closure.starProjection oddReciprocal)) := by
  have h : Tendsto (fun n => (stage n).starProjection oddReciprocal) atTop
      (𝓝 (closure.starProjection oddReciprocal)) :=
    walkProjection_tendsto (fun i => qResidue (i + 2))
      id Function.surjective_id oddReciprocal
  simpa only [← reciprocalFit_eq_projection] using h

theorem reciprocal_error_matrix_tendsto :
    Tendsto (fun n => ‖oddReciprocal‖ ^ 2 -
      dotProduct (targetCross n) (targetCoefficients n)) atTop
      (𝓝 (‖oddReciprocal - closure.starProjection oddReciprocal‖ ^ 2)) := by
  have h := ((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => oddReciprocal) atTop (𝓝 oddReciprocal)).sub
      reciprocalFit_tendsto).norm.pow 2
  simpa only [reciprocal_error_matrix] using h

theorem density_error_tendsto :
    Tendsto (fun n => ‖B (qResidue 2) - densityFit n‖ ^ 2) atTop
      (𝓝 ((1 / zetaTwo) ^ 2 *
        ‖oddReciprocal - closure.starProjection oddReciprocal‖ ^ 2)) := by
  simpa only [density_error_matrix] using
    reciprocal_error_matrix_tendsto.const_mul ((1 / zetaTwo) ^ 2)

theorem reciprocal_matrix_zero_iff_density_mem :
    Tendsto (fun n => ‖oddReciprocal‖ ^ 2 -
      dotProduct (targetCross n) (targetCoefficients n)) atTop (𝓝 0) ↔
      B (qResidue 2) ∈ closure := by
  rw [density_two_mem_closure_iff]
  have h := walkError_tendsto_zero_iff (fun i => qResidue (i + 2))
    id Function.surjective_id oddReciprocal
  change Tendsto (fun n => ‖oddReciprocal - (stage n).starProjection
    oddReciprocal‖ ^ 2) atTop (𝓝 0) ↔ oddReciprocal ∈ closure at h
  simpa only [← reciprocalFit_eq_projection, reciprocal_error_matrix] using h


/-- The exact target norm, retaining every positive odd coordinate. -/
theorem oddReciprocal_norm_series :
    ‖oddReciprocal‖ ^ 2 =
      ∑' m : ℕ, if m % 2 = 1 then
        1 / (4 * zetaTwo * (m : ℝ) ^ 4) else 0 := by
  rw [qNorm_weighted_sq]
  apply tsum_congr
  intro m
  rw [oddReciprocal_sequence]
  by_cases hm : m % 2 = 1
  · simp only [hm, if_true]
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    unfold positiveQWeight
    field_simp [hmR, ne_of_gt zetaTwo_pos]
    ring
  · simp [hm]

/-- Literal right-hand side of the complete inverse-Gram system for D g₂. -/
theorem targetCross_series (n : ℕ) (i : Fin n) :
    targetCross n i =
      ∑' m : ℕ, if m % 2 = 1 then
        ((m % conductor n i : ℕ) : ℝ) /
          (2 * zetaTwo * (conductor n i : ℝ) * (m : ℝ) ^ 3) else 0 := by
  rw [targetCross, qInner_weighted]
  apply tsum_congr
  intro m
  rw [qSequence_qResidue, oddReciprocal_sequence]
  by_cases hm : m % 2 = 1
  · simp only [hm, if_true]
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hkR : (conductor n i : ℝ) ≠ 0 := by
      exact_mod_cast (show conductor n i ≠ 0 by have h := conductor_gt_one n i; omega)
    unfold positiveQWeight ArithmeticCumulative.residueFraction
    field_simp [hmR, hkR, ne_of_gt zetaTwo_pos]
  · simp [hm]

/-- The same full error in the complete natural Q divisor-wavelet coordinates. -/
theorem density_error_parseval (n : ℕ) :
    ‖B (qResidue 2) - densityFit n‖ ^ 2 =
      (1 / zetaTwo) ^ 2 *
        ∑' r : ℕ+, (inner ℝ oddReciprocal (QDivisorHilbert.divisorWavelet r) -
          ∑ i : Fin n, targetCoefficients n i *
            qResidueDivisorCoefficient (conductor n i) r) ^ 2 / qJordanTwo r := by
  rw [density_error_vector, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    ← QDivisorHilbert.divisorWavelet_parseval_norm]
  congr 1
  apply tsum_congr
  intro r
  rw [inner_sub_left]
  simp only [reciprocalFit, qSynthesis, sum_inner, real_inner_smul_left,
    QDivisorHilbert.qResidue_divisorWavelet_inner]

def threeCoordinateFit : QHilbert :=
  qResidue 2 + (1 / 3 : ℝ) • qResidue 3 - (4 / 9 : ℝ) • qResidue 4

theorem threeCoordinateFit_exact (n : ℕ) (hn : 0 < n) (hn3 : n ≤ 3) :
    qSequence threeCoordinateFit n = qSequence oddReciprocal n := by
  change qSequenceLinear threeCoordinateFit n = _
  unfold threeCoordinateFit
  rw [map_sub, map_add, map_smul, map_smul]
  change qSequence (qResidue 2) n + (1 / 3 : ℝ) * qSequence (qResidue 3) n -
    (4 / 9 : ℝ) * qSequence (qResidue 4) n = _
  rw [oddReciprocal_sequence]
  simp only [qSequence_qResidue, ArithmeticCumulative.residueFraction]
  interval_cases n <;> norm_num

/-- info: 'RiemannResearch.RH.QDensityParityApproximation.density_error_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms density_error_matrix
/-- info: 'RiemannResearch.RH.QDensityParityApproximation.reciprocal_matrix_zero_iff_density_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reciprocal_matrix_zero_iff_density_mem


def threeCoordinateDensityFit : QHilbert :=
  (1 / zetaTwo) • (qResidue 2 + threeCoordinateFit)

theorem threeCoordinateDensityFit_exact (n : ℕ)
    (hn : 0 < n) (hn3 : n ≤ 3) :
    qSequence threeCoordinateDensityFit n = qSequence (B (qResidue 2)) n := by
  rw [density_two_eq]
  change qSequenceLinear ((1 / zetaTwo) • (qResidue 2 + threeCoordinateFit)) n =
    qSequenceLinear ((1 / zetaTwo) • (qResidue 2 + oddReciprocal)) n
  simp only [map_smul, map_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [show qSequenceLinear threeCoordinateFit n =
    qSequenceLinear oddReciprocal n from threeCoordinateFit_exact n hn hn3]

/-- info: 'RiemannResearch.RH.QDensityParityApproximation.density_error_parseval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms density_error_parseval

/-!
The exact normalization below uses Mathlib's checked zeta(2) and zeta(4)
series evaluations:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ZetaValues.html

The resulting numeric saturation criterion is still conditional on the
single target's legal-span membership; the residual is retained in the
unconditional monotone limit.
-/

set_option maxHeartbeats 800000 in
private theorem odd_fourth_sum :
    (∑' m : ℕ, if m % 2 = 1 then 1 / (m : ℝ) ^ 4 else 0) =
      Real.pi ^ 4 / 96 := by
  have hs : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 4) :=
    hasSum_zeta_four.summable
  have he : Function.Injective (fun m : ℕ => 2 * m) := by
    intro i j h
    change 2 * i = 2 * j at h
    omega
  have ho : Function.Injective (fun m : ℕ => 2 * m + 1) := by
    intro i j h
    change 2 * i + 1 = 2 * j + 1 at h
    omega
  have hsplit := tsum_even_add_odd
    (f := fun m : ℕ => 1 / (m : ℝ) ^ 4)
    (hs.comp_injective he) (hs.comp_injective ho)
  have heven :
      (∑' m : ℕ, 1 / ((2 * m : ℕ) : ℝ) ^ 4) =
        (1 / 16 : ℝ) * (Real.pi ^ 4 / 90) := by
    rw [← hasSum_zeta_four.tsum_eq, ← tsum_mul_left]
    apply tsum_congr
    intro m
    simp only [Nat.cast_mul, Nat.cast_ofNat, mul_pow, one_div, mul_inv_rev]
    norm_num
    ring
  rw [hasSum_zeta_four.tsum_eq, heven] at hsplit
  have hodd :
      (∑' m : ℕ, 1 / ((2 * m + 1 : ℕ) : ℝ) ^ 4) = Real.pi ^ 4 / 96 := by
    linarith
  have hd : Summable (fun m : ℕ =>
      if m % 2 = 1 then 1 / (m : ℝ) ^ 4 else 0) := by
    apply Summable.of_nonneg_of_le (fun m => by split_ifs <;> positivity) _ hs
    intro m
    split_ifs
    · exact le_rfl
    · positivity
  have hdsplit := tsum_even_add_odd
    (f := fun m : ℕ => if m % 2 = 1 then 1 / (m : ℝ) ^ 4 else 0)
    (hd.comp_injective he) (hd.comp_injective ho)
  have hdeq :
      (∑' m : ℕ, 1 / ((2 * m + 1 : ℕ) : ℝ) ^ 4) =
        ∑' m : ℕ, if m % 2 = 1 then 1 / (m : ℝ) ^ 4 else 0 := by
    simpa [Nat.add_mod, Nat.mul_mod] using hdsplit
  exact hdeq.symm.trans hodd

theorem oddReciprocal_norm_sq :
    ‖oddReciprocal‖ ^ 2 = Real.pi ^ 2 / 64 := by
  have hz : zetaTwo = Real.pi ^ 2 / 6 := by
    rw [zetaTwo_eq_nat_sum]
    exact hasSum_zeta_two.tsum_eq
  rw [oddReciprocal_norm_series]
  calc
    _ = (1 / (4 * zetaTwo)) *
        ∑' m : ℕ, if m % 2 = 1 then 1 / (m : ℝ) ^ 4 else 0 := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      split_ifs <;> simp [one_div, mul_inv_rev, mul_left_comm, mul_comm]
    _ = Real.pi ^ 2 / 64 := by
      rw [odd_fourth_sum, hz]
      field_simp [Real.pi_ne_zero]
      ring

def targetInformation (n : ℕ) : ℝ :=
  dotProduct (targetCross n) (targetCoefficients n)

theorem targetInformation_eq_norm_sq (n : ℕ) :
    targetInformation n = ‖reciprocalFit n‖ ^ 2 := by
  rw [reciprocalFit_eq_projection]
  have h := projection_inner_eq_inverseGram
    (qResidue_linearIndependent (conductor n)
      (conductor_gt_one n) (conductor_injective n)) oddReciprocal oddReciprocal
  rw [real_inner_self_eq_norm_sq] at h
  exact h.symm

theorem targetInformation_nonneg (n : ℕ) : 0 ≤ targetInformation n := by
  rw [targetInformation_eq_norm_sq]
  exact sq_nonneg _

theorem targetInformation_le (n : ℕ) :
    targetInformation n ≤ Real.pi ^ 2 / 64 := by
  have h := reciprocal_error_matrix n
  rw [oddReciprocal_norm_sq] at h
  change ‖oddReciprocal - reciprocalFit n‖ ^ 2 =
    Real.pi ^ 2 / 64 - targetInformation n at h
  nlinarith [sq_nonneg ‖oddReciprocal - reciprocalFit n‖]

theorem targetInformation_monotone : Monotone targetInformation := by
  intro m n hmn
  have h := walkError_antitone (fun i => qResidue (i + 2))
    id oddReciprocal hmn
  change ‖oddReciprocal - (stage n).starProjection oddReciprocal‖ ^ 2 ≤
    ‖oddReciprocal - (stage m).starProjection oddReciprocal‖ ^ 2 at h
  rw [← reciprocalFit_eq_projection, ← reciprocalFit_eq_projection,
    reciprocal_error_matrix, reciprocal_error_matrix] at h
  change ‖oddReciprocal‖ ^ 2 - targetInformation n ≤
    ‖oddReciprocal‖ ^ 2 - targetInformation m at h
  linarith

/-- The unconditional limit retains the full closed-span residual. -/
theorem targetInformation_tendsto :
    Tendsto targetInformation atTop
      (𝓝 (Real.pi ^ 2 / 64 -
        ‖oddReciprocal - closure.starProjection oddReciprocal‖ ^ 2)) := by
  change Tendsto (fun n => dotProduct (targetCross n) (targetCoefficients n))
    atTop _
  have h := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => ‖oddReciprocal‖ ^ 2) atTop
      (𝓝 (‖oddReciprocal‖ ^ 2))).sub reciprocal_error_matrix_tendsto
  simpa only [sub_sub_cancel, oddReciprocal_norm_sq, targetInformation] using h

/-- The requested numeric saturation limit still requires Bg₂ membership. -/
theorem targetInformation_tendsto_pi_iff :
    Tendsto targetInformation atTop (𝓝 (Real.pi ^ 2 / 64)) ↔
      B (qResidue 2) ∈ closure := by
  change Tendsto (fun n => dotProduct (targetCross n) (targetCoefficients n))
    atTop (𝓝 (Real.pi ^ 2 / 64)) ↔ B (qResidue 2) ∈ closure
  constructor
  · intro h
    apply reciprocal_matrix_zero_iff_density_mem.mp
    have ht := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => Real.pi ^ 2 / 64) atTop
        (𝓝 (Real.pi ^ 2 / 64))).sub h
    simpa only [sub_self, ← oddReciprocal_norm_sq, targetInformation] using ht
  · intro h
    have ht := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => ‖oddReciprocal‖ ^ 2) atTop
        (𝓝 (‖oddReciprocal‖ ^ 2))).sub
      (reciprocal_matrix_zero_iff_density_mem.mpr h)
    simpa only [sub_sub_cancel, sub_zero, oddReciprocal_norm_sq,
      targetInformation] using ht

/-- info: 'RiemannResearch.RH.QDensityParityApproximation.oddReciprocal_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms oddReciprocal_norm_sq
/-- info: 'RiemannResearch.RH.QDensityParityApproximation.targetInformation_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms targetInformation_tendsto
/-- info: 'RiemannResearch.RH.QDensityParityApproximation.targetInformation_tendsto_pi_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms targetInformation_tendsto_pi_iff

end RiemannResearch.RH.QDensityParityApproximation
