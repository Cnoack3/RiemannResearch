/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PrimePowerHilbertTarget
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ParetoMellinDilation
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual Q logarithmic targets and their exact Mellin transform

Source: the user-provided RH/CRT continuation agenda, 20 October 2026,
Priority 4. The target is constructed unconditionally; its squarefree
closure membership remains the explicit Open hypothesis of the RH consumer.
The exact transform follows from the actual Hilbert contraction equation.
-/

noncomputable section
namespace RiemannResearch.RH.PrimePowerTarget
open Pareto Pareto.CoefficientStabilization
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer

theorem primePower_q_square_summable (p : ℕ) (hp : 1 < p) :
    Summable (fun n : ℕ => positiveQWeight n * (Nat.log p n : ℝ) ^ 2) := by
  have hs := ((hilbertSequence_square_summable (paretoTarget p hp)).mul_left 2).div_const zetaTwo
  simp_rw [paretoTarget_sequence] at hs
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _)) _ hs
  intro n
  apply (le_div_iff₀ zetaTwo_pos).2
  have hb := mul_le_mul_of_nonneg_right
    (zetaTwo_mul_QWeight_le_two_mul_paretoWeight n) (sq_nonneg (Nat.log p n : ℝ))
  nlinarith

def qTarget (p : ℕ) (hp : 1 < p) : QHilbert :=
  encodeQ (fun n => (Nat.log p n : ℝ)) (primePower_q_square_summable p hp)

@[simp] theorem qTarget_sequence (p : ℕ) (hp : 1 < p) :
    qSequence (qTarget p hp) = fun n => (Nat.log p n : ℝ) := by
  exact qSequence_encodeQ _ _ (by simp)

@[simp] theorem toPareto_qTarget (p : ℕ) (hp : 1 < p) :
    toPareto (qTarget p hp) = paretoTarget p hp := by
  apply hilbertSequence_injective
  rw [toPareto_sequence, qTarget_sequence]
  funext n
  exact (paretoTarget_sequence p hp n).symm

theorem qTarget_norm_sq_bound (p : ℕ) (hp : 1 < p) :
    ‖qTarget p hp‖ ^ 2 ≤
      (2 * ((p : ℝ) + 1)) / (zetaTwo * ((p : ℝ) - 1) ^ 2) := by
  have hb := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq (qTarget p hp)
  rw [toPareto_qTarget, paretoTarget_norm_sq] at hb
  apply (le_div_iff₀ (mul_pos zetaTwo_pos (sq_pos_of_ne_zero (by
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp
    linarith : (p : ℝ) - 1 ≠ 0)))).2
  have hpd : 0 < ((p : ℝ) - 1) ^ 2 := sq_pos_of_ne_zero (by
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp
    linarith)
  have hh := (le_div_iff₀ hpd).mp (show zetaTwo * ‖qTarget p hp‖ ^ 2 ≤
    (2 * ((p : ℝ) + 1)) / ((p : ℝ) - 1) ^ 2 by simpa [mul_div_assoc] using hb)
  nlinarith

theorem unscaledDilation_mellin (p : ℕ) (hp : 0 < p)
    (f : ThresholdHilbert) (s : ℂ) :
    paretoMellin (unscaledDilation p hp f) s = (p : ℂ) ^ (-s) * paretoMellin f s := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  change paretoMellin ((1 / (p : ℝ)) • hilbertDilation p hp f) s = _
  rw [paretoMellin_smul, paretoMellin_dilation]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_natCast]
  rw [show (1 : ℂ) - s = 1 + (-s) by ring, Complex.cpow_add _ _ hpC,
    Complex.cpow_one]
  field_simp

theorem paretoTarget_mellin_equation (p : ℕ) (hp : 1 < p)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    paretoMellin (paretoTarget p hp) s =
      (p : ℂ) ^ (-s) * (paretoMellin (paretoTarget p hp) s + 1 / s) := by
  conv_lhs => rw [← paretoTarget_fixed p hp]
  rw [unscaledDilation_mellin, paretoMellin_add _ _ s hs, paretoMellin_one s hs]

/-- Exact normalized Mellin identity, proved from the actual contraction equation.
No exchange of an unproved infinite series with an integral is used. -/
theorem paretoTarget_mellin_exact (p : ℕ) (hp : 1 < p)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    s * paretoMellin (paretoTarget p hp) s = 1 / ((p : ℂ) ^ s - 1) := by
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hq : (p : ℂ) ^ s ≠ 0 := by simp [Complex.cpow_def, hpC]
  have h := paretoTarget_mellin_equation p hp s hs
  rw [Complex.cpow_neg] at h
  have he : (s * paretoMellin (paretoTarget p hp) s) * ((p : ℂ) ^ s - 1) = 1 := by
    field_simp [hq, hs0] at h
    linear_combination h
  have hd : (p : ℂ) ^ s - 1 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at he
    exact zero_ne_one he
  exact (eq_div_iff hd).2 he

theorem paretoTarget_mellin_ne_zero (p : ℕ) (hp : 1 < p)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    paretoMellin (paretoTarget p hp) s ≠ 0 := by
  intro hz
  have h := paretoTarget_mellin_equation p hp s hs
  rw [hz, zero_add] at h
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hpow : (p : ℂ) ^ (-s) ≠ 0 := by simp [Complex.cpow_def, hpC]
  exact (mul_ne_zero hpow (div_ne_zero one_ne_zero hs0)) h.symm

/-- Conditional RH consumer. The complete Hilbert vector and its nonzero
Mellin transform are proved; its squarefree closure membership remains Open. -/
theorem riemannHypothesis_of_qTarget_mem (p : ℕ) (hp : 1 < p)
    (hmem : qTarget p hp ∈ ZetaTwoOptimizerStage.closure) : RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hslt hz
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hslt
  have hm := toPareto_mem_closedSpace hmem
  rw [toPareto_qTarget] at hm
  apply paretoTarget_mellin_ne_zero p hp s hs
  exact paretoMellin_zero_on_legalClosure_of_zeta {n : ℕ | 0 < n}
    (fun _ hn => hn) s hs hs1 hz (closedSpace_le_legalClosure hm)


end RiemannResearch.RH.PrimePowerTarget
