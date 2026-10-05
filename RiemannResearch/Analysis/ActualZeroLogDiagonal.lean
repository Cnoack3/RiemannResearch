/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RiemannResearch.Analysis.EuclideanOperatorCoordinates
import RiemannResearch.Analysis.ActualZeroPhaseMoments

/-!
# Actual centered log-frequency operator

The integer frequencies 1,...,d define a Euclidean diagonal operator centered
at log d / 2. Its norm is exactly log d / 2 for d >= 1, attained at frequency 1.
Centering cancels exactly in every iterated commutator entry. The sharp width
provider closes the ordinary diagonal-norm premise in the actual-zero even
moment series; no spectral, Landau, density, or RH hypothesis is introduced.

Source: the user-provided research argument in
Prime_Phases_Agenda_Proof_Attempts.tex. The Euclidean norm and coordinate proof
strategy is formalized in the imported EuclideanOperatorCoordinates module.
-/

noncomputable section
open scoped BigOperators Matrix

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments

/-- Integer frequencies 1,...,d have logarithmic coordinates. -/
def logFrequency (d : ℕ) (n : Fin d) : ℝ :=
  Real.log ((n.val + 1 : ℕ) : ℝ)

/-- Midpoint centering gives the sharp width budget log d. -/
def logDiagonal (d : ℕ) : Space d →L[ℂ] Space d :=
  EuclideanSpace.diagonalCLM fun n : Fin d =>
    ((logFrequency d n - Real.log (d : ℝ) / 2 : ℝ) : ℂ)

@[simp] theorem logDiagonal_apply (d : ℕ) (x : Space d) (n : Fin d) :
    logDiagonal d x n =
      ((logFrequency d n - Real.log (d : ℝ) / 2 : ℝ) : ℂ) * x n :=
  EuclideanSpace.diagonalCLM_apply _ _ _

theorem logFrequency_bounds (d : ℕ) (n : Fin d) :
    0 ≤ logFrequency d n ∧ logFrequency d n ≤ Real.log (d : ℝ) := by
  have hn1 : (1 : ℝ) ≤ ((n.val + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n.val)
  have hnd : ((n.val + 1 : ℕ) : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt n.isLt
  exact ⟨Real.log_nonneg hn1, Real.log_le_log (by positivity) hnd⟩

/-- Actual centered log-frequency norm provider: no spectral or analytic premise. -/
theorem logDiagonal_norm_le (d : ℕ) (hd : 1 ≤ d) :
    ‖logDiagonal d‖ ≤ Real.log (d : ℝ) / 2 := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hdR
  apply EuclideanSpace.norm_diagonalCLM_le _ _ (by positivity)
  intro n
  have hn := logFrequency_bounds d n
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

theorem two_mul_logDiagonal_norm_le (d : ℕ) (hd : 1 ≤ d) :
    2 * ‖logDiagonal d‖ ≤ Real.log (d : ℝ) := by
  have h := logDiagonal_norm_le d hd
  linarith

/-- The midpoint width budget is exact, attained at frequency 1. -/
theorem logDiagonal_norm_eq (d : ℕ) (hd : 1 ≤ d) :
    ‖logDiagonal d‖ = Real.log (d : ℝ) / 2 := by
  apply le_antisymm (logDiagonal_norm_le d hd)
  let n0 : Fin d := ⟨0, Nat.succ_le_iff.mp hd⟩
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hdR
  have hf : logFrequency d n0 = 0 := by simp [logFrequency, n0]
  have hs : logDiagonal d (EuclideanSpace.single n0 1) =
      ((-(Real.log (d : ℝ) / 2) : ℝ) : ℂ) • EuclideanSpace.single n0 1 := by
    rw [logDiagonal, EuclideanSpace.diagonalCLM_single, hf]
    simp only [zero_sub]
  have h := (logDiagonal d).le_opNorm (EuclideanSpace.single n0 1)
  rw [hs, norm_smul, PiLp.norm_single, norm_one, mul_one, mul_one] at h
  rw [Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ Real.log (d : ℝ) / 2)] at h
  exact h

/-- Centering cancels exactly in entries, retaining every integer conductor. -/
theorem iterComm_logDiagonal_apply_single
    (d : ℕ) (M : Space d →L[ℂ] Space d) (j : ℕ) (n m : Fin d) :
    (HorizontalPhaseBootstrap.iterComm (logDiagonal d) j M
      (EuclideanSpace.single m 1)) n =
      ((logFrequency d n - logFrequency d m : ℝ) : ℂ) ^ j *
        (M (EuclideanSpace.single m 1)) n := by
  have h := EuclideanSpace.iterComm_diagonalCLM_apply_single
    (fun i : Fin d => ((logFrequency d i - Real.log (d : ℝ) / 2 : ℝ) : ℂ))
    M j n m
  have hc :
      ((logFrequency d n - Real.log (d : ℝ) / 2 : ℝ) : ℂ) -
        ((logFrequency d m - Real.log (d : ℝ) / 2 : ℝ) : ℂ) =
      ((logFrequency d n - logFrequency d m : ℝ) : ℂ) := by
    push_cast
    ring
  simpa only [logDiagonal, hc] using h

/-- Close the last ordinary diagonal-width premise in the actual moment provider. -/
theorem logEvenMomentCorrection_summable_and_norm_le
    (T : ℝ) (d : ℕ) (hd : 1 ≤ d) (δ : ℝ) (hδ : 0 ≤ δ) :
    Summable (fun k => ‖HorizontalPhaseBootstrap.evenTerm
      (logDiagonal d) (goodMoment T d δ) k‖) ∧
      Summable (HorizontalPhaseBootstrap.evenTerm (logDiagonal d) (goodMoment T d δ)) ∧
      ‖∑' k, HorizontalPhaseBootstrap.evenTerm (logDiagonal d) (goodMoment T d δ) k‖ ≤
        (‖phaseGram T d‖ / 2) * (Real.cosh (δ * Real.log (d : ℝ)) - 1) :=
  evenMomentCorrection_summable_and_norm_le T d (logDiagonal d)
    (Real.log (d : ℝ)) δ hδ (two_mul_logDiagonal_norm_le d hd)

end RiemannResearch.Analysis.ActualZeroPhaseMoments
