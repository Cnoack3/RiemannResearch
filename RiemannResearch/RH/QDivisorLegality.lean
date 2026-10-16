/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.QDivisibilityDensity
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Divisibility indicators and squarefree residue legality

The positive-coordinate indicator `qDivisor m` is the actual Q-Hilbert
realization of `1_{m ∣ n}`. It belongs to no finite legal residue span
for any positive conductor. For every `m ≥ 3` it does not even belong to
the closed squarefree residue span.

The exact obstruction is the signed square-jump defect. Squarefree
conductors divide a site exactly when they divide its square, so the
closed squarefree span satisfies `Δf(a²) = Δf(a)`. The indicator has
defect exactly `-1` at `a = m - 1`. No coefficient signs or conductor
sizes are restricted, and no RH assumption is used.

At conductor two the exact identity is `qDivisor 2 = qOne - 2 • qResidue 2`.
Thus its squarefree closure membership is equivalent to that of `qOne`.
This file does not formalize the external RH-to-squarefree-density
implication and does not assert either closure membership.

Source: the argument developed in the user's research conversation,
15–16 October 2026, for the statements and proof strategy.
-/

noncomputable section
namespace RiemannResearch.RH.QDivisorLegality
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity
open SquarefreeRadicalDifference ArithmeticCumulative

/-- Every finite squarefree legal combination has the same jump at a site and its square. -/
theorem squarefree_span_difference_square (a : ℕ) (ha : 2 ≤ a)
    (x : QHilbert) (hx : x ∈ qSquarefreeCRTSpan) :
    qDifference x (a ^ 2) = qDifference x a := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨d, rfl⟩ := hx
      unfold qDifference
      simp only [qSequence_qResidue]
      exact residueFraction_difference_eq_of_dvd_iff d.val (a ^ 2) a
        d.property.1 (by nlinarith) (by omega)
        (d.property.2.dvd_pow_iff_dvd (by decide : (2 : ℕ) ≠ 0))
  | zero => rw [qDifference_zero, qDifference_zero]
  | add x y hx hy ihx ihy =>
      rw [qDifference_add, qDifference_add, ihx, ihy]
  | smul c x hx ih =>
      rw [qDifference_smul, qDifference_smul, ih]

/-- The square-jump identity holds throughout the actual closed squarefree residue span. -/
theorem squarefree_closure_difference_square (a : ℕ) (ha : 2 ≤ a)
    (x : QHilbert) (hx : x ∈ qSquarefreeCRTSpan.topologicalClosure) :
    qDifference x (a ^ 2) = qDifference x a := by
  exact closure_minimal
    (fun y hy => squarefree_span_difference_square a ha y hy)
    (isClosed_eq (continuous_qDifference (a ^ 2)) (continuous_qDifference a)) hx

/-- The divisor indicator violates the square-jump relation by exactly minus one. -/
theorem qDivisor_square_jump_defect (m : ℕ) (hm : 3 ≤ m) :
    qDifference (qDivisor m) ((m - 1) ^ 2) -
      qDifference (qDivisor m) (m - 1) = -1 := by
  have ha : 2 ≤ m - 1 := by omega
  have ha2 : 4 ≤ (m - 1) ^ 2 := by nlinarith
  have he : (m - 1) ^ 2 = m * (m - 2) + 1 := by
    have h1 : m - 1 + 1 = m := by omega
    have h2 : m - 2 + 2 = m := by omega
    nlinarith
  have hp : (m - 1) ^ 2 - 1 = m * (m - 2) := by omega
  have hd : m ∣ (m - 1) ^ 2 - 1 := by
    rw [hp]
    exact ⟨m - 2, rfl⟩
  have hnd : ¬ m ∣ (m - 1) ^ 2 := by
    intro h
    have hsub := Nat.dvd_sub h hd
    have hone : (m - 1) ^ 2 - ((m - 1) ^ 2 - 1) = 1 := by omega
    rw [hone] at hsub
    have := Nat.le_of_dvd (by decide : 0 < 1) hsub
    omega
  have hna : ¬ m ∣ m - 1 := by
    intro h
    have := Nat.le_of_dvd (by omega : 0 < m - 1) h
    omega
  have hnap : ¬ m ∣ m - 1 - 1 := by
    intro h
    have := Nat.le_of_dvd (by omega : 0 < m - 1 - 1) h
    omega
  simp [qDifference, qSequence_qDivisor, positiveDivisor,
    show (m - 1) ^ 2 - 1 ≠ 0 by omega,
    show m - 1 ≠ 0 by omega,
    show m - 1 - 1 ≠ 0 by omega, hd, hnd, hna, hnap]

/-- No divisor indicator with conductor at least three lies in the closed squarefree legal span. -/
theorem qDivisor_not_mem_squarefreeClosure (m : ℕ) (hm : 3 ≤ m) :
    qDivisor m ∉ qSquarefreeCRTSpan.topologicalClosure := by
  intro hx
  have hidentity := squarefree_closure_difference_square (m - 1)
    (by omega) (qDivisor m) hx
  have hdefect := qDivisor_square_jump_defect m hm
  rw [hidentity, sub_self] at hdefect
  norm_num at hdefect

/-- Exact conductor-two identity; the positive zero-coordinate convention is retained. -/
theorem qDivisor_two_eq :
    qDivisor 2 = qOne - (2 : ℝ) • qResidue 2 := by
  apply qSequence_injective
  funext n
  have hsub : qSequence (qOne - (2 : ℝ) • qResidue 2) n =
      qSequence qOne n - qSequence ((2 : ℝ) • qResidue 2) n :=
    congrFun (qSequenceLinear.map_sub qOne ((2 : ℝ) • qResidue 2)) n
  have hsmul : qSequence ((2 : ℝ) • qResidue 2) n =
      (2 : ℝ) * qSequence (qResidue 2) n :=
    congrFun (qSequenceLinear.map_smul (2 : ℝ) (qResidue 2)) n
  change qSequence (qDivisor 2) n = qSequence (qOne - (2 : ℝ) • qResidue 2) n
  rw [hsub, hsmul]
  simp only [qSequence_qDivisor, qSequence_qOne, qSequence_qResidue]
  by_cases hn : n = 0
  · subst n
    norm_num [positiveDivisor, qOneSequence, residueFraction]
  · rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
    · have hdiv : 2 ∣ n := Nat.dvd_of_mod_eq_zero hmod
      norm_num [positiveDivisor, qOneSequence, residueFraction, hn, hdiv, hmod]
    · have hdiv : ¬ 2 ∣ n := by
        intro h
        have := Nat.mod_eq_zero_of_dvd h
        omega
      norm_num [positiveDivisor, qOneSequence, residueFraction, hn, hdiv, hmod]

/-- The conductor-two indicator has the same squarefree closure obligation as the constant. -/
theorem qDivisor_two_mem_squarefreeClosure_iff :
    qDivisor 2 ∈ qSquarefreeCRTSpan.topologicalClosure ↔
      qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
  have hg : qResidue 2 ∈ qSquarefreeCRTSpan := by
    exact Submodule.subset_span ⟨⟨2, ⟨by decide, Nat.prime_two.squarefree⟩⟩, rfl⟩
  have h2g := qSquarefreeCRTSpan.topologicalClosure.smul_mem (2 : ℝ)
    (qSquarefreeCRTSpan.le_topologicalClosure hg)
  rw [qDivisor_two_eq]
  constructor
  · intro h
    simpa only [sub_add_cancel] using
      qSquarefreeCRTSpan.topologicalClosure.add_mem h h2g
  · intro h
    exact qSquarefreeCRTSpan.topologicalClosure.sub_mem h h2g

/-- A finite residue combination vanishes at every multiple of a suitable positive period. -/
theorem residueSpan_vanishes_at_common_multiple
    (S : Set ℕ) (hS : ∀ d ∈ S, 2 ≤ d)
    (x : QHilbert) (hx : x ∈ Submodule.span ℝ (qResidue '' S)) :
    ∃ L : ℕ, 0 < L ∧ ∀ n : ℕ, L ∣ n → qSequence x n = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨d, hd, rfl⟩ := hx
      refine ⟨d, by have := hS d hd; omega, ?_⟩
      intro n hn
      simp [qSequence_qResidue, residueFraction, Nat.mod_eq_zero_of_dvd hn]
  | zero =>
      refine ⟨1, by decide, ?_⟩
      intro n _
      exact congrFun (map_zero qSequenceLinear) n
  | add x y hx hy ihx ihy =>
      obtain ⟨L, hL, hxL⟩ := ihx
      obtain ⟨K, hK, hyK⟩ := ihy
      refine ⟨L * K, Nat.mul_pos hL hK, ?_⟩
      intro n hn
      have hLn : L ∣ n := dvd_trans (show L ∣ L * K from ⟨K, rfl⟩) hn
      have hKn : K ∣ n :=
        dvd_trans (show K ∣ L * K from ⟨L, Nat.mul_comm L K⟩) hn
      have hadd : qSequence (x + y) n = qSequence x n + qSequence y n :=
        congrFun (qSequenceLinear.map_add x y) n
      rw [hadd, hxL n hLn, hyK n hKn, add_zero]
  | smul c x hx ih =>
      obtain ⟨L, hL, hxL⟩ := ih
      refine ⟨L, hL, ?_⟩
      intro n hn
      have hsmul : qSequence (c • x) n = c * qSequence x n :=
        congrFun (qSequenceLinear.map_smul c x) n
      rw [hsmul, hxL n hn, mul_zero]

/-- No positive-conductor divisibility indicator is any finite legal residue combination. -/
theorem qDivisor_not_mem_residueSpan
    (m : ℕ) (hm : 0 < m) (S : Set ℕ) (hS : ∀ d ∈ S, 2 ≤ d) :
    qDivisor m ∉ Submodule.span ℝ (qResidue '' S) := by
  intro hx
  obtain ⟨L, hL, hvanish⟩ := residueSpan_vanishes_at_common_multiple S hS (qDivisor m) hx
  have hz := hvanish (m * L) ⟨m, Nat.mul_comm m L⟩
  have hnonzero : m * L ≠ 0 := Nat.ne_of_gt (Nat.mul_pos hm hL)
  have hd : m ∣ m * L := ⟨L, rfl⟩
  simp [qSequence_qDivisor, positiveDivisor, hnonzero, hd] at hz

/-- In particular no divisor indicator is a finite squarefree legal combination. -/
theorem qDivisor_not_mem_squarefreeSpan (m : ℕ) (hm : 0 < m) :
    qDivisor m ∉ qSquarefreeCRTSpan := by
  intro hx
  have hs : qSquarefreeCRTSpan ≤
      Submodule.span ℝ (qResidue '' {d : ℕ | 2 ≤ d}) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    exact Submodule.subset_span ⟨d.val, d.property.1, rfl⟩
  exact qDivisor_not_mem_residueSpan m hm {d : ℕ | 2 ≤ d}
    (fun _ hd => hd) (hs hx)

end RiemannResearch.RH.QDivisorLegality
