/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QDivisorWaveletDensity
import RiemannResearch.RH.QDivisorWaveletFactorization
import RiemannResearch.RH.QPrimePowerOrthogonal
import RiemannResearch.RH.PrimePowerTwoTargetCriterion
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.QPrimePowerHilbertFrame
import RiemannResearch.RH.QSquarefreeLegalBasis
import RiemannResearch.RH.QSquarefreeDilationObstruction
import RiemannResearch.RH.QSquarefreeJumpDistance
import RiemannResearch.RH.QDivisibilityHilbertMoments
import RiemannResearch.RH.QDivisibilityDensity
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Ring

/-!
# A concrete failure of ambient divisor-mode projection to preserve legality

Source: user-provided comparison of the complete ambient divisor basis with
the legal squarefree dictionary, 22 October 2026. The exact arithmetic
calculation uses the existing four-site square-jump functional.
The legal atom g_3 has nonzero coefficient along B_3, and its orthogonal
projection onto that single ambient mode violates the legal jump equation.

RH consumer: selecting ambient modes cannot be assumed to preserve the
actual legal closure, even after constants are adjoined. This counterexample
concerns a single-mode projection; it makes no assertion about target
membership or a cutoff onto an entire infinite conductor family.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.QDivisorModeLegality
open ZetaTwoHilbert ZetaTwoProbability QDivisorHilbert QDivisibilityDensity
open PrimePowerTarget QSquarefreeJumpDistance SquarefreeRadicalDifference ArithmeticCumulative

/-- Orthogonal projection onto one unit ambient divisor wavelet. -/
def singleDivisorMode (t : ℕ+) (f : QHilbert) : QHilbert :=
  inner ℝ f (normalizedDivisorWavelet t) • normalizedDivisorWavelet t

theorem divisorWavelet_three_explicit :
    divisorWavelet 3 = (9 : ℝ) • qDivisor 3 - qOne := by
  have hone : qDivisor 1 = qOne := by
    apply qSequence_injective
    funext n
    simp [qSequence_qDivisor, positiveDivisor, qSequence_qOne, qOneSequence]
  have h := divisorWavelet_prime_pow_succ 3 0 (by norm_num)
  norm_num at h
  simpa [hone] using h

theorem normalizedDivisorWavelet_three_explicit :
    normalizedDivisorWavelet (3 : ℕ+) =
      (Real.sqrt 8)⁻¹ • ((9 : ℝ) • qDivisor 3 - qOne) := by
  have hj : qJordanTwo 3 = 8 := by norm_num [qJordanTwo, valuationWaveletWeight]
  change (Real.sqrt (qJordanTwo 3))⁻¹ • divisorWavelet 3 = _
  rw [hj, divisorWavelet_three_explicit]

theorem residue_three_mode_coefficient :
    inner ℝ (qResidue 3) (normalizedDivisorWavelet (3 : ℕ+)) =
      -inner ℝ (qResidue 3) qOne / Real.sqrt 8 := by
  rw [normalizedDivisorWavelet_three_explicit, real_inner_smul_right,
    inner_sub_right, real_inner_smul_right,
    qResidue_inner_qDivisor_eq_zero 3 3 (by norm_num) (dvd_refl 3)]
  ring

theorem divisor_mode_three_squareJump :
    squareJumpFunctional 2 (normalizedDivisorWavelet (3 : ℕ+)) =
      -9 / Real.sqrt 8 := by
  have hdiv : squareJumpFunctional 2 (qDivisor 3) = -1 := by
    rw [squareJumpFunctional_apply 2 (by norm_num)]
    simp only [qDifference, qSequence_qDivisor]
    norm_num [positiveDivisor]
  have hone : squareJumpFunctional 2 qOne = 0 :=
    squareJumpFunctional_zero_on_closureWithConstants 2 (by norm_num)
      qOne_mem_closureWithConstants
  rw [normalizedDivisorWavelet_three_explicit, map_smul, map_sub, map_smul, hdiv, hone]
  simp only [smul_eq_mul]
  ring

/-- Exact positive legal defect, retaining its complete-Q mean factor. -/
theorem residue_three_single_mode_defect :
    squareJumpFunctional 2 (singleDivisorMode (3 : ℕ+) (qResidue 3)) =
      9 * inner ℝ (qResidue 3) qOne / 8 := by
  rw [singleDivisorMode, map_smul, residue_three_mode_coefficient,
    divisor_mode_three_squareJump]
  simp only [smul_eq_mul]
  rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
  ring

theorem residue_three_mean_pos : 0 < inner ℝ (qResidue 3) qOne := by
  have hs := qSequence_product_summable (qResidue 3) qOne
  have hn (n : ℕ) :
      0 ≤ positiveQWeight n * qSequence (qResidue 3) n * qSequence qOne n := by
    rw [qSequence_qResidue, qSequence_qOne]
    by_cases h : n = 0
    · simp [h, qOneSequence]
    · simp only [qOneSequence, if_neg h, mul_one]
      exact mul_nonneg (positiveQWeight_nonneg n) (by unfold residueFraction; positivity)
  have ht : 0 < positiveQWeight 1 * qSequence (qResidue 3) 1 * qSequence qOne 1 := by
    have hw : 0 < positiveQWeight 1 := by
      have hZ := zetaTwo_pos
      unfold positiveQWeight
      positivity
    rw [qSequence_qResidue, qSequence_qOne]
    simpa [residueFraction, qOneSequence] using
      mul_pos hw (by norm_num : (0 : ℝ) < 1 / 3)
  rw [qInner_weighted]
  exact ht.trans_le (hs.le_tsum 1 (fun j _ => hn j))

theorem residue_three_single_mode_not_mem :
    singleDivisorMode (3 : ℕ+) (qResidue 3) ∉ closureWithConstants := by
  intro h
  have hz := squareJumpFunctional_zero_on_closureWithConstants 2 (by norm_num) h
  rw [residue_three_single_mode_defect] at hz
  have hp := residue_three_mean_pos
  linarith

/-- A legal squarefree atom whose single-mode ambient projection is outside C. -/
theorem ambient_single_mode_not_legal_preserving :
    ∃ f : QHilbert, f ∈ closureWithConstants ∧
      singleDivisorMode (3 : ℕ+) f ∉ closureWithConstants := by
  exact ⟨qResidue 3, QSquarefreeLegalBasis.qResidue_mem_closureWithConstants 3
    (by norm_num) Nat.prime_three.squarefree, residue_three_single_mode_not_mem⟩

end RiemannResearch.RH.QDivisorModeLegality
