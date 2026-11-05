/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QMellinTransfer
import RiemannResearch.RH.RiemannHypothesisStrip
import RiemannResearch.RH.QRecursiveDigitBounds
import RiemannResearch.RH.NymanConductorContinuation
import RiemannResearch.RH.ParetoBoundedMellin

/-! # The tree edge as a Mellin detector of actual zeta zeros

The multiplier for one radix edge consists of a nonvanishing dilation and
the ordinary one-conductor symbol. The symbol has additional zeros only
on the line of real part one. The physical input is the integer quotient
digit, embedded as a step function on [1,∞). Sources: the repository's
physical atom transform and CRT radix identity, and the Mellin transform of
fractional parts in L. Báez-Duarte, Rend. Accad. Naz. Lincei 14 (2003), 5–11.
-/

noncomputable section
open MeasureTheory Set
namespace RiemannResearch.RH.QTreeDigitMellin
open ZetaTwoHilbert ZetaTwoParetoTransfer QMellinTransfer CRTCarryArithmetic
open ArithmeticCumulative ArithmeticConductorCommonZeros

/-- The zeros of any one physical atom recover every zeta zero in the open
critical strip; more generally this holds off the line of real part one. -/
theorem atom_zero_iff (d : ℕ) (hd : 1 < d) (s : ℂ)
    (hs : 0 < s.re) (hline : s.re ≠ 1) :
    qMellin (qResidue d) s = 0 ↔ riemannZeta s = 0 := by
  have hd' : 0 < d := by omega
  have hs0 : s ≠ 0 := by intro e; simp [e] at hs
  have hs1 : s ≠ 1 := by rintro rfl; simp at hline
  rw [qMellin_residue_zeta d hd' s hs hs1, ← conductorSymbol_eq_cpow d hd' s]
  simp [conductorSymbol_ne_zero_of_re_ne_one d hd s hline, hs0]

private theorem atom_step_integrable (d : ℕ) (hd : 0 < d) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (residueFraction d ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
  have hi := Pareto.paretoMellin_step_integrable_of_bounded (toPareto (qResidue d)) 1
    (by
      intro n
      rw [toPareto_sequence, qSequence_qResidue]
      exact Pareto.normalizedAtom_abs_le_one d n hd)
    s hs
  simpa only [toPareto_sequence, qSequence_qResidue] using hi

/-- Exact Mellin transform of one normalized quotient digit. Primality and
coprimality are unnecessary. The formula applies even on the critical line. -/
theorem digit_integral (D p : ℕ) (hD : 0 < D) (hp : 0 < p) (s : ℂ)
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (∫ x in Ioi (1 : ℝ), (quotientDigit D p ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1)) =
      (riemannZeta s / s) * (D : ℂ) ^ (-s) * conductorSymbol p s := by
  let f (d : ℕ) (x : ℝ) := (residueFraction d ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1)
  have hm (d : ℕ) : (∫ x in Ioi (1 : ℝ), f d x) = qMellin (qResidue d) s := by
    rw [qMellin_eq_step_integral, qSequence_qResidue]
  have hdigit (x : ℝ) : (quotientDigit D p ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1) =
      f (D * p) x - (p : ℂ)⁻¹ * f D x := by
    have h := residueFraction_eq_parent_add_digit D p ⌊x⌋₊ hD hp
    have he : quotientDigit D p ⌊x⌋₊ =
        residueFraction (D * p) ⌊x⌋₊ - residueFraction D ⌊x⌋₊ / (p : ℝ) := by linarith
    rw [he]
    push_cast
    dsimp [f]
    ring
  have hprod : ((D : ℂ) * (p : ℂ)) ^ (-s) = (D : ℂ) ^ (-s) * (p : ℂ) ^ (-s) := by
    simpa only [Complex.ofReal_natCast] using
      Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg D) (Nat.cast_nonneg p) (-s)
  simp_rw [hdigit]
  rw [integral_sub (atom_step_integrable _ (Nat.mul_pos hD hp) s hs)
      ((atom_step_integrable _ hD s hs).const_mul _),
    integral_const_mul, hm, hm, qMellin_residue_zeta _ (Nat.mul_pos hD hp) s hs hs1,
    qMellin_residue_zeta _ hD s hs hs1, conductorSymbol_eq_cpow p hp s, Nat.cast_mul,
    hprod, one_div, mul_inv_rev]
  ring

theorem digit_zero_iff (D p : ℕ) (hD : 0 < D) (hp : 1 < p) (s : ℂ)
    (hs : 0 < s.re) (hline : s.re ≠ 1) :
    (∫ x in Ioi (1 : ℝ), (quotientDigit D p ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1)) = 0 ↔
      riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by intro e; simp [e] at hs
  have hs1 : s ≠ 1 := by rintro rfl; simp at hline
  have hDn : (D : ℂ) ^ (-s) ≠ 0 := Complex.cpow_ne_zero_iff.mpr
    (Or.inl (by exact_mod_cast hD.ne'))
  rw [digit_integral D p hD (by omega) s hs hs1]
  simp [hDn, conductorSymbol_ne_zero_of_re_ne_one p hp s hline, hs0]

/-- The Hilbert vector on this actual tree edge has the preceding step integral. -/
theorem qMellin_edge_eq_digit (D p : ℕ) (hD : 0 < D) (hp : 0 < p) (s : ℂ) :
    qMellin (qResidue (D * p) - (p : ℝ)⁻¹ • qResidue D) s =
      ∫ x in Ioi (1 : ℝ), (quotientDigit D p ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1) := by
  have he (n : ℕ) : qSequence (qResidue (D * p) - (p : ℝ)⁻¹ • qResidue D) n =
      quotientDigit D p n := by
    change qSequenceLinear (qResidue (D * p) - (p : ℝ)⁻¹ • qResidue D) n = _
    rw [map_sub, map_smul]
    change qSequence (qResidue (D * p)) n - (p : ℝ)⁻¹ * qSequence (qResidue D) n = _
    rw [qSequence_qResidue, qSequence_qResidue, residueFraction_eq_parent_add_digit D p n hD hp]
    ring
  rw [qMellin_eq_step_integral]
  simp_rw [he]

/-- An individual Hilbert-space edge detects exactly the zeta zeros in the strip. -/
theorem qMellin_edge_zero_iff (D p : ℕ) (hD : 0 < D) (hp : 1 < p) (s : ℂ)
    (hs : 0 < s.re) (hline : s.re ≠ 1) :
    qMellin (qResidue (D * p) - (p : ℝ)⁻¹ • qResidue D) s = 0 ↔ riemannZeta s = 0 := by
  rw [qMellin_edge_eq_digit D p hD (by omega), digit_zero_iff D p hD hp s hs hline]

/-- RH reformulated entirely in terms of the physical observations of any
fixed edge, using only the usual open-strip formulation of RH. -/
theorem riemannHypothesis_iff_digit_zeros_on_line (D p : ℕ) (hD : 0 < D) (hp : 1 < p) :
    RiemannHypothesis ↔ ∀ s : ℂ, 0 < s.re → s.re < 1 →
      (∫ x in Ioi (1 : ℝ), (quotientDigit D p ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1)) = 0 →
      s.re = 1 / 2 := by
  rw [riemannHypothesis_iff_strip_zeros_on_line]
  constructor
  · intro h s hpos hlt hz
    exact h s ((digit_zero_iff D p hD hp s hpos hlt.ne).mp hz) hpos hlt
  · intro h s hz hpos hlt
    exact h s hpos hlt ((digit_zero_iff D p hD hp s hpos hlt.ne).mpr hz)

end RiemannResearch.RH.QTreeDigitMellin
