/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.Analysis.EvenPeriodicSquareJump
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact parity geometry in the Q-Hilbert space

A physical sequence that is two-periodic on positive indices is exactly
its even value times qOne plus twice its odd-even difference times qResidue 2.
The auxiliary zero coordinate is kept separate.

Source: direct parity decomposition in the user-directed research continuation,
16 October 2026. No RH or legal-closure assumption is used.
-/

noncomputable section
namespace RiemannResearch.RH.ZetaTwoHilbert

open RiemannResearch.Analysis.EvenPeriodicSquareJump

/-- Exact Hilbert-vector reconstruction from the two physical parity values. -/
theorem qHilbert_eq_parity_of_two_periodic (x : QHilbert)
    (hx : ∀ n : ℕ, 0 < n → qSequence x (n + 2) = qSequence x n) :
    x = (qSequence x 2) • qOne +
      (2 * (qSequence x 1 - qSequence x 2)) • qResidue 2 := by
  apply qSequence_injective
  funext n
  change qSequence x n = qSequenceLinear
    ((qSequence x 2) • qOne +
      (2 * (qSequence x 1 - qSequence x 2)) • qResidue 2) n
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change qSequence x n = qSequence x 2 * qSequence qOne n +
    (2 * (qSequence x 1 - qSequence x 2)) * qSequence (qResidue 2) n
  rw [qSequence_qOne, qSequence_qResidue]
  by_cases hn : n = 0
  · subst n
    simp [qSequence_zero, qOneSequence, ArithmeticCumulative.residueFraction]
  · rw [values_of_two_periodic (qSequence x) hx n (by omega)]
    rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
    · have hd : 2 ∣ n := Nat.dvd_of_mod_eq_zero hmod
      simp [hd, qOneSequence, ArithmeticCumulative.residueFraction, hn, hmod]
    · have hd : ¬ 2 ∣ n := by
        intro hd
        have := Nat.mod_eq_zero_of_dvd hd
        omega
      simp [hd, qOneSequence, ArithmeticCumulative.residueFraction, hn, hmod]
      ring


end RiemannResearch.RH.ZetaTwoHilbert
