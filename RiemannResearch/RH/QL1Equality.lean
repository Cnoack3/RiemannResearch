/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.UnitVectorVariance
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact L1/L2 equality cases for the inverse-square probability law

Source: the user's norm convergence and equality-case discussion, 25 October
2026. The exact centered squares precede their vanishing criteria. Equality
of L1 and L2 norms means constant magnitude; no positivity is assumed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.Analysis.UnitVectorVariance

theorem q_eq_const_iff (f : QHilbert) (c : ℝ) :
    f = c • qOne ↔ ∀ n : ℕ, 0 < n → qSequence f n = c := by
  have hs (n : ℕ) : qSequence (c • qOne) n = c * qOneSequence n := by
    change qSequenceLinear (c • qOne) n = _
    rw [map_smul]
    change c * qSequence qOne n = _
    rw [qSequence_qOne]
  constructor
  · intro hf n hn
    rw [hf, hs]
    simp [qOneSequence, Nat.ne_of_gt hn]
  · intro hf
    apply qSequence_injective
    funext n
    by_cases hn : n = 0
    · subst n
      simp
    · rw [hf n (Nat.pos_of_ne_zero hn), hs]
      simp [qOneSequence, hn]

theorem qMean_abs_le_qL1 (f : QHilbert) : |inner ℝ qOne f| ≤ qL1 f := by
  rw [qOne_inner_weighted]
  apply abs_le.mpr
  constructor
  · have h := Summable.tsum_le_tsum
      (fun k => show -(positiveQWeight k * |qSequence f k|) ≤
          positiveQWeight k * qSequence f k by
        simpa only [mul_neg] using mul_le_mul_of_nonneg_left
          (neg_abs_le (qSequence f k)) (positiveQWeight_nonneg k))
      (qL1_summable f).neg (qFirstMoment_summable f)
    simpa only [tsum_neg, qL1] using h
  · exact Summable.tsum_le_tsum
      (fun k => mul_le_mul_of_nonneg_left (le_abs_self (qSequence f k))
        (positiveQWeight_nonneg k))
      (qFirstMoment_summable f) (qL1_summable f)

/-- Exact variance, retaining the complete weighted squared distance. -/
theorem qCentered_norm_sq (f : QHilbert) :
    ‖f - (inner ℝ qOne f) • qOne‖ ^ 2 =
      ‖f‖ ^ 2 - (inner ℝ qOne f) ^ 2 :=
  centered_norm_sq qOne f qOne_norm_sq

/-- The L1/L2 gap is the variance of the absolute value. -/
theorem qAbs_centered_norm_sq (f : QHilbert) :
    ‖qAbs f - qL1 f • qOne‖ ^ 2 = ‖f‖ ^ 2 - qL1 f ^ 2 := by
  simpa only [← qL1_eq_inner, qAbs_norm] using
    centered_norm_sq qOne (qAbs f) qOne_norm_sq

theorem qL1_eq_norm_iff_vector (f : QHilbert) :
    qL1 f = ‖f‖ ↔ qAbs f = qL1 f • qOne := by
  simpa only [← qL1_eq_inner, qAbs_norm, abs_of_nonneg (qL1_nonneg f)] using
    abs_inner_eq_norm_iff qOne (qAbs f) qOne_norm_sq

theorem qL1_eq_norm_iff_abs_value (f : QHilbert) :
    qL1 f = ‖f‖ ↔ ∀ n : ℕ, 0 < n → |qSequence f n| = qL1 f := by
  rw [qL1_eq_norm_iff_vector, q_eq_const_iff]
  simp only [qAbs_sequence]

theorem qL1_eq_norm_iff_abs_constant (f : QHilbert) :
    qL1 f = ‖f‖ ↔ ∃ c : ℝ, 0 ≤ c ∧
      ∀ n : ℕ, 0 < n → |qSequence f n| = c := by
  constructor
  · intro h
    exact ⟨qL1 f, qL1_nonneg f, (qL1_eq_norm_iff_abs_value f).mp h⟩
  · rintro ⟨c, _hc, hf⟩
    have he : qAbs f = c • qOne := (q_eq_const_iff (qAbs f) c).mpr (by
      simpa only [qAbs_sequence] using hf)
    have hm : qL1 f = c := by
      rw [qL1_eq_inner, he, real_inner_smul_right,
        real_inner_self_eq_norm_sq, qOne_norm_sq, mul_one]
    apply (qL1_eq_norm_iff_abs_value f).mpr
    simpa only [hm] using hf

theorem qMean_abs_eq_norm_iff_constant (f : QHilbert) :
    |inner ℝ qOne f| = ‖f‖ ↔
      ∃ c : ℝ, ∀ n : ℕ, 0 < n → qSequence f n = c := by
  rw [abs_inner_eq_norm_iff_exists_smul qOne f qOne_norm_sq]
  simp_rw [q_eq_const_iff]

/-- A signed function of constant magnitude, not an assertion of squarefree legality. -/
def qParitySign : QHilbert := qOne - (4 : ℝ) • qResidue 2

theorem qParitySign_sequence (n : ℕ) (hn : 0 < n) :
    qSequence qParitySign n = 1 - 2 * (n % 2 : ℕ) := by
  change qSequenceLinear (qOne - (4 : ℝ) • qResidue 2) n = _
  rw [map_sub, map_smul]
  change qSequence qOne n - 4 * qSequence (qResidue 2) n = _
  rw [qSequence_qOne, qSequence_qResidue]
  simp only [qOneSequence, if_neg (Nat.ne_of_gt hn), ArithmeticCumulative.residueFraction]
  norm_num
  ring

theorem qParitySign_abs (n : ℕ) (hn : 0 < n) :
    |qSequence qParitySign n| = 1 := by
  rw [qParitySign_sequence n hn]
  have hm : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hm with h | h <;> rw [h] <;> norm_num

theorem qParitySign_not_constant :
    ¬ ∃ c : ℝ, ∀ n : ℕ, 0 < n → qSequence qParitySign n = c := by
  rintro ⟨c, hc⟩
  have h1 := hc 1 (by decide)
  have h2 := hc 2 (by decide)
  rw [qParitySign_sequence 1 (by decide)] at h1
  rw [qParitySign_sequence 2 (by decide)] at h2
  norm_num at h1 h2
  linarith

/-- Explicit counterexample to replacing constant absolute value by constant value. -/
theorem qL1_equality_nonconstant_example :
    qL1 qParitySign = ‖qParitySign‖ ∧
      ¬ ∃ c : ℝ, ∀ n : ℕ, 0 < n → qSequence qParitySign n = c := by
  exact ⟨(qL1_eq_norm_iff_abs_constant qParitySign).mpr
    ⟨1, by norm_num, qParitySign_abs⟩, qParitySign_not_constant⟩

end RiemannResearch.RH.ZetaTwoHilbert
