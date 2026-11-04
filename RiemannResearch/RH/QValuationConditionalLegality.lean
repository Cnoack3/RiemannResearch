/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimeValuationFactorLegality
import RiemannResearch.RH.PrimeValuationHilbertBasis
import RiemannResearch.RH.QDivisibilityHilbertMoments
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Valuation-coordinate conditioning does not preserve legality

The orthogonal projection onto the actual closed valuation subspace is the
L2 conditional expectation onto one prime coordinate. The legal input g_p
has nonzero mean and vanishes on every positive valuation level. If its
projection were legal, valuation-factor rigidity would force a constant;
level one forces that constant to vanish, contradicting preservation of mean.

Source: elementary consequence of the repository's complete valuation basis,
the new arbitrary-factor rigidity theorem, and standard orthogonal projection.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QValuationConditionalLegality
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open QDivisibilityDensity PrimeValuationBasis QPrimeValuationFactorLegality

theorem qResidue_mean_pos (d : ℕ) (hd : 2 ≤ d) :
    0 < inner ℝ qOne (qResidue d) := by
  rw [qInner_weighted]
  refine (qSequence_product_summable qOne (qResidue d)).tsum_pos ?_ 1 ?_
  · intro n
    rw [qSequence_qOne, qSequence_qResidue]
    unfold qOneSequence residueFraction
    split_ifs <;> positivity [positiveQWeight_nonneg n]
  · rw [qSequence_qOne, qSequence_qResidue]
    have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    norm_num [qOneSequence, residueFraction, Nat.mod_eq_of_lt (show 1 < d by omega)]
    unfold positiveQWeight
    positivity [zetaTwo_pos]

theorem residue_inner_positive_level_zero (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    inner ℝ (qResidue p) (valuationLevel p k) = 0 := by
  rw [valuationLevel, inner_sub_right,
    qResidue_inner_qDivisor_eq_zero p (p ^ k) (pow_pos hp.pos _) (dvd_pow_self p hk),
    qResidue_inner_qDivisor_eq_zero p (p ^ (k+1)) (pow_pos hp.pos _)
      (dvd_pow_self p (by omega)), sub_self]

/-- Actual valuation-coordinate orthogonal projection of a legal atom is illegal
at every odd prime. No RH premise or numerical moment is used. -/
theorem valuation_projection_residue_not_legal (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    (valuationSpace p).starProjection (qResidue p) ∉
      qSquarefreeCRTSpan.topologicalClosure := by
  intro hlegal
  let y := (valuationSpace p).starProjection (qResidue p)
  have hy : y ∈ valuationSpace p := (valuationSpace p).starProjection_apply_mem _
  have hc := valuationSpace_legal_constant p hp hp3 y hy hlegal
  have hlevel := (valuationSpace p).starProjection_inner_eq_zero
    (qResidue p) (valuationLevel p 1) (valuationLevel_mem p 1 hp)
  change inner ℝ (qResidue p - y) (valuationLevel p 1) = 0 at hlevel
  rw [inner_sub_left, residue_inner_positive_level_zero p 1 hp (by decide), hc,
    real_inner_smul_left, qOne_inner_valuationLevel p 1 hp] at hlevel
  have hzero : qSequence y 1 = 0 := by
    have hmass := ne_of_gt (valuationMass_pos p 1 hp)
    have hz : qSequence y 1 * valuationMass p 1 = 0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_right hmass
  have hyzero : y = 0 := by simpa only [hzero, zero_smul] using hc
  have hmean := (valuationSpace p).starProjection_inner_eq_zero
    (qResidue p) qOne (qOne_mem_valuationSpace p hp)
  change inner ℝ (qResidue p - y) qOne = 0 at hmean
  rw [hyzero, sub_zero, real_inner_comm] at hmean
  exact (ne_of_gt (qResidue_mean_pos p hp.two_le)) hmean

end RiemannResearch.RH.QValuationConditionalLegality
