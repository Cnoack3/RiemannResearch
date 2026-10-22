/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroPhaseOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual finite bad-copy correction in the Euclidean operator norm

The signed bad operator is first identified with its full finite sum of cosh
correction operators, including all actual zero copies and their original
normalizer. Every rank-one moment is positive and admits midpoint centering;
its even commutator series gives the sharp factor d/(2N) in the cosh budget.
The exponential budget consequently has factor d/(4N).

No zero-density, Landau, simplicity or RH hypothesis occurs here. The only
support hypothesis is d >= 1. Source: the user-provided phase-Gram argument and
RH/GrowingPhaseGramBootstrapAudit20261005.md.
-/

noncomputable section
open Complex Zeta23
open scoped BigOperators InnerProductSpace Matrix

namespace ContinuousLinearMap

open RiemannResearch.Analysis.HorizontalEuclideanMoments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A direct consequence of actual finite positive rank-one centering. -/
theorem rankOne_real_smul_center_norm_le (v : E) (b : ℝ) (hb : 0 ≤ b) :
    ‖b • InnerProductSpace.rankOne ℂ v v -
      (b * ‖InnerProductSpace.rankOne ℂ v v‖ / 2) • (1 : E →L[ℂ] E)‖ ≤
      b * ‖InnerProductSpace.rankOne ℂ v v‖ / 2 := by
  have h := weightedCopyGram_center_norm_le
    (Finset.univ : Finset Unit) (1 : ℝ) b (fun _ => b) (fun _ => v)
    (by norm_num) hb (fun _ _ => ⟨hb, le_rfl⟩)
  simpa only [copyGram, weightedCopyGram, Finset.sum_const, Finset.card_univ,
    Fintype.card_unit, one_nsmul, one_smul] using h

end ContinuousLinearMap

namespace Real

theorem cosh_sub_one_le_half_exp (x : ℝ) (hx : 0 ≤ x) :
    Real.cosh x - 1 ≤ Real.exp x / 2 := by
  have hn : Real.exp (-x) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonpos.mpr hx)
  rw [Real.cosh_eq]
  linarith

end Real

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments

open ActualZeroOrdinate HorizontalEuclideanMoments HorizontalPhaseBootstrap
open ZeroOrdinate ContinuousLinearMap

def badRealWeight (δ : ℝ) (ρ : ℂ) : ℝ :=
  if |ρ.re - 1 / 2| ≤ δ then 0 else 1

theorem badRealWeight_nonneg (δ : ℝ) (ρ : ℂ) : 0 ≤ badRealWeight δ ρ := by
  unfold badRealWeight
  split_ifs <;> norm_num

theorem badRealWeight_coe (δ : ℝ) (ρ : ℂ) :
    (badRealWeight δ ρ : ℂ) = badWeight δ ρ := by
  by_cases h : |ρ.re - 1 / 2| ≤ δ
  · simp only [badRealWeight, badWeight, goodWeight, if_pos h,
      Complex.ofReal_zero, sub_self]
  · simp only [badRealWeight, badWeight, goodWeight, if_neg h,
      Complex.ofReal_one, sub_zero]

def copyCoshCorrection (d : ℕ) (ρ : ℂ) : Space d →L[ℂ] Space d :=
  Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (fun n m : Fin d =>
    phase (frequencyGap n m) ρ.im *
      ((Real.cosh ((ρ.re - 1 / 2) * frequencyGap n m) : ℂ) - 1))

def copyHorizontalMoment (d : ℕ) (ρ : ℂ) (k : ℕ) : Space d →L[ℂ] Space d :=
  (ρ.re - 1 / 2) ^ (2 * k) •
    InnerProductSpace.rankOne ℂ (copyPhaseVector d ρ) (copyPhaseVector d ρ)

@[simp] theorem copyCoshCorrection_entry (d : ℕ) (ρ : ℂ) (n m : Fin d) :
    euclideanEntry (copyCoshCorrection d ρ) n m =
      phase (frequencyGap n m) ρ.im *
        ((Real.cosh ((ρ.re - 1 / 2) * frequencyGap n m) : ℂ) - 1) :=
  euclideanEntry_toEuclideanCLM _ _ _

theorem copyPhaseVector_norm_sq (d : ℕ) (ρ : ℂ) :
    ‖copyPhaseVector d ρ‖ ^ 2 = (d : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [copyPhaseVector_apply, phase_norm, one_pow, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem copyRankOne_norm (d : ℕ) (ρ : ℂ) :
    ‖InnerProductSpace.rankOne ℂ (copyPhaseVector d ρ) (copyPhaseVector d ρ)‖ =
      (d : ℝ) := by
  rw [InnerProductSpace.norm_rankOne, ← sq, copyPhaseVector_norm_sq]

theorem copyMomentCorrection_summable_and_norm_le
    (d : ℕ) (hd : 1 ≤ d) (ρ : ℂ) :
    Summable (fun k => ‖evenTerm (logDiagonal d) (copyHorizontalMoment d ρ) k‖) ∧
      Summable (evenTerm (logDiagonal d) (copyHorizontalMoment d ρ)) ∧
      ‖∑' k, evenTerm (logDiagonal d) (copyHorizontalMoment d ρ) k‖ ≤
        ((d : ℝ) / 2) *
          (Real.cosh (|ρ.re - 1 / 2| * Real.log (d : ℝ)) - 1) := by
  let P := InnerProductSpace.rankOne ℂ (copyPhaseVector d ρ) (copyPhaseVector d ρ)
  have hm : ∀ k, ‖copyHorizontalMoment d ρ (k + 1) -
      (|ρ.re - 1 / 2| ^ (2 * (k + 1)) * ‖P‖ / 2) •
        (1 : Space d →L[ℂ] Space d)‖ ≤
      |ρ.re - 1 / 2| ^ (2 * (k + 1)) * ‖P‖ / 2 := by
    intro k
    have hp : |ρ.re - 1 / 2| ^ (2 * (k + 1)) =
        (ρ.re - 1 / 2) ^ (2 * (k + 1)) := by
      rw [pow_mul, pow_mul, sq_abs]
    rw [hp]
    exact rankOne_real_smul_center_norm_le _ _ (by rw [pow_mul]; positivity)
  have h := evenCorrection_summable_and_norm_le
    (logDiagonal d) (copyHorizontalMoment d ρ) (Real.log (d : ℝ))
    |ρ.re - 1 / 2| ‖P‖ (two_mul_logDiagonal_norm_le d hd) hm
  simpa only [P, copyRankOne_norm] using h

private theorem complex_cosh_even_tail (q : ℝ) :
    (∑' k : ℕ, ((Nat.factorial (2 * (k + 1)) : ℂ)⁻¹) *
      (q : ℂ) ^ (2 * (k + 1))) = (Real.cosh q : ℂ) - 1 := by
  have h := congrArg (fun r : ℝ => (r : ℂ)) (cosh_tail_tsum q)
  rw [Complex.ofReal_tsum] at h
  simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_natCast] at h
  simpa only [div_eq_mul_inv, mul_comm] using h

theorem copyEvenTerm_entry (d : ℕ) (ρ : ℂ) (k : ℕ) (n m : Fin d) :
    euclideanEntry (evenTerm (logDiagonal d) (copyHorizontalMoment d ρ) k) n m =
      ((Nat.factorial (2 * (k + 1)) : ℂ)⁻¹) *
        (((ρ.re - 1 / 2) * frequencyGap n m : ℝ) : ℂ) ^ (2 * (k + 1)) *
          phase (frequencyGap n m) ρ.im := by
  have hi : euclideanEntry
      (iterComm (logDiagonal d) (2 * (k + 1)) (copyHorizontalMoment d ρ (k + 1))) n m =
      (frequencyGap n m : ℂ) ^ (2 * (k + 1)) *
        euclideanEntry (copyHorizontalMoment d ρ (k + 1)) n m := by
    simpa only [euclideanEntry, frequencyGap, logFrequency] using
      iterComm_logDiagonal_apply_single d (copyHorizontalMoment d ρ (k + 1))
        (2 * (k + 1)) n m
  rw [evenTerm, euclideanEntry_real_smul, hi, copyHorizontalMoment,
    euclideanEntry_real_smul, euclideanEntry_rankOne, copyPhaseVector_kernel]
  push_cast
  rw [mul_pow]
  ring

/-- Exact pointwise correction operator before any norm is taken. -/
theorem copyCoshCorrection_eq_tsum (d : ℕ) (hd : 1 ≤ d) (ρ : ℂ) :
    copyCoshCorrection d ρ =
      ∑' k, evenTerm (logDiagonal d) (copyHorizontalMoment d ρ) k := by
  apply euclideanEntry_ext
  intro n m
  have hs := (copyMomentCorrection_summable_and_norm_le d hd ρ).2.1
  rw [copyCoshCorrection_entry, euclideanEntry_tsum _ hs]
  simp_rw [copyEvenTerm_entry]
  rw [tsum_mul_right, complex_cosh_even_tail]
  ring

theorem copyCoshCorrection_norm_le (d : ℕ) (hd : 1 ≤ d) (ρ : ℂ) :
    ‖copyCoshCorrection d ρ‖ ≤
      ((d : ℝ) / 2) * (Real.cosh (|ρ.re - 1 / 2| * Real.log (d : ℝ)) - 1) := by
  rw [copyCoshCorrection_eq_tsum d hd ρ]
  exact (copyMomentCorrection_summable_and_norm_le d hd ρ).2.2

/-- Exact finite-copy bad remainder. The original normalizer and every copy,
including all multiplicities and the good/bad boundary convention, are present. -/
theorem badCorrection_eq_copy_sum (T : ℝ) (d : ℕ) (δ : ℝ) :
    badCorrection T d δ = (Ncount 0 T : ℝ)⁻¹ •
      ∑ c : Copies T, badRealWeight δ c.1.1 • copyCoshCorrection d c.1.1 := by
  apply euclideanEntry_ext
  intro n m
  rw [badCorrection_entry, euclideanEntry_real_smul, ← euclideanEntryCLM_apply, map_sum]
  simp_rw [euclideanEntryCLM_apply, euclideanEntry_real_smul,
    copyCoshCorrection_entry, badRealWeight_coe]
  unfold weightedCoshCorrection
  rw [sum_eq_copies]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  rw [mul_comm (frequencyGap n m : ℂ) ((c.1.1.re : ℂ) - 1 / 2)]
  ring

/-- Sharp per-copy half factor, with the full signed correction retained in
the preceding exact equality. No zero-density premise is present. -/
theorem badCorrection_norm_le_cosh (T : ℝ) (d : ℕ) (hd : 1 ≤ d) (δ : ℝ) :
    ‖badCorrection T d δ‖ ≤
      (d : ℝ) / (2 * (Ncount 0 T : ℝ)) *
        realSum T (fun ρ => badRealWeight δ ρ *
          (Real.cosh (|ρ.re - 1 / 2| * Real.log (d : ℝ)) - 1)) := by
  let κ : ℝ := (Ncount 0 T : ℝ)⁻¹
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  rw [badCorrection_eq_copy_sum, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ (Ncount 0 T : ℝ)⁻¹ by positivity)]
  change κ * ‖∑ c : Copies T, badRealWeight δ c.1.1 • copyCoshCorrection d c.1.1‖ ≤ _
  calc
    _ ≤ κ * ∑ c : Copies T,
        ‖badRealWeight δ c.1.1 • copyCoshCorrection d c.1.1‖ :=
      mul_le_mul_of_nonneg_left (_root_.norm_sum_le _ _) hκ
    _ = κ * ∑ c : Copies T, badRealWeight δ c.1.1 * ‖copyCoshCorrection d c.1.1‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro c hc
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (badRealWeight_nonneg _ _)]
    _ ≤ κ * ∑ c : Copies T, badRealWeight δ c.1.1 *
        (((d : ℝ) / 2) *
          (Real.cosh (|c.1.1.re - 1 / 2| * Real.log (d : ℝ)) - 1)) := by
      apply mul_le_mul_of_nonneg_left _ hκ
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left (copyCoshCorrection_norm_le d hd c.1.1)
        (badRealWeight_nonneg _ _)
    _ = _ := by
      rw [realSum_eq_copies]
      simp only [κ, div_eq_mul_inv, mul_inv, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      ring

/-- Exponential tail form with factor d/(4N), ready for a separately proved
actual zero-density estimate. The present statement itself is unconditional. -/
theorem badCorrection_norm_le_exp (T : ℝ) (d : ℕ) (hd : 1 ≤ d) (δ : ℝ) :
    ‖badCorrection T d δ‖ ≤
      (d : ℝ) / (4 * (Ncount 0 T : ℝ)) *
        realSum T (fun ρ => badRealWeight δ ρ *
          Real.exp (|ρ.re - 1 / 2| * Real.log (d : ℝ))) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hdR
  apply (badCorrection_norm_le_cosh T d hd δ).trans
  have hs : realSum T (fun ρ => badRealWeight δ ρ *
      (Real.cosh (|ρ.re - 1 / 2| * Real.log (d : ℝ)) - 1)) ≤
      (1 / 2 : ℝ) * realSum T (fun ρ => badRealWeight δ ρ *
        Real.exp (|ρ.re - 1 / 2| * Real.log (d : ℝ))) := by
    calc
      _ ≤ realSum T (fun ρ => badRealWeight δ ρ *
          (Real.exp (|ρ.re - 1 / 2| * Real.log (d : ℝ)) / 2)) := by
        apply realSum_mono
        intro ρ hρ
        exact mul_le_mul_of_nonneg_left
          (Real.cosh_sub_one_le_half_exp _ (mul_nonneg (abs_nonneg _) hL))
          (badRealWeight_nonneg _ _)
      _ = _ := by
        rw [mul_comm (1 / 2 : ℝ)
          (realSum T (fun ρ => badRealWeight δ ρ *
            Real.exp (|ρ.re - 1 / 2| * Real.log (d : ℝ))))]
        rw [← realSum_mul_const]
        congr 1
        funext ρ
        ring
  calc
    _ ≤ (d : ℝ) / (2 * (Ncount 0 T : ℝ)) *
        ((1 / 2 : ℝ) * realSum T (fun ρ => badRealWeight δ ρ *
          Real.exp (|ρ.re - 1 / 2| * Real.log (d : ℝ)))) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv]; ring

end RiemannResearch.Analysis.ActualZeroPhaseMoments
