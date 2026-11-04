/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeFiniteDualClosure
import RiemannResearch.RH.QDivisibilityDensity
import RiemannResearch.NumberTheory.RadicalFiberSeparation
import Mathlib.Tactic.NormNum
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
/-!
# Concrete ambient tensor functions that are not legal

Source: elementary three-class arithmetic and the continuous four-site
annihilator, developed in the 4 November 2026 tensor discussion.
The general radical constraint is reused from QSquarefreeFiniteDualClosure.
Von Neumann, On infinite direct products, Compositio 6 (1939), Section 4.1,
supports only the ambient tensor interpretation explained in the paper.

This module checks the actual Hilbert vectors, their physical sequences,
their decomposition of g_3, and their nonmembership in the squarefree
closure. It does not formalize the infinite tensor identification or
convergence of prime-truncated character products.
-/
noncomputable section
namespace RiemannResearch.RH.QModThreeTensorLegality
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open SquarefreeRadicalDifference QSquarefreeFiniteDualClosure QDivisibilityDensity
open UniqueFactorizationMonoid
def fourSite (f : QHilbert) : ℝ := qDifference f 4 - qDifference f 2
def coprimeThree : QHilbert := qOne - qDivisor 3
def characterThree : QHilbert := (3 : ℝ) • coprimeThree - (6 : ℝ) • qResidue 3
theorem fourSite_add (f g : QHilbert) :
    fourSite (f + g) = fourSite f + fourSite g := by
  simp only [fourSite, qDifference_add]; ring
theorem fourSite_sub (f g : QHilbert) :
    fourSite (f - g) = fourSite f - fourSite g := by
  simp only [fourSite, qDifference_sub]; ring
theorem fourSite_smul (c : ℝ) (f : QHilbert) :
    fourSite (c • f) = c * fourSite f := by
  simp only [fourSite, qDifference_smul]; ring
theorem fourSite_legal {f : QHilbert}
    (hf : f ∈ qSquarefreeCRTSpan.topologicalClosure) : fourSite f = 0 := by
  have hrad : radical (4 : ℕ) = 2 := by
    simpa using Nat.radical_pow_eq_of_squarefree (d := 2) (k := 2)
      (by norm_num) Nat.prime_two.squarefree (by decide)
  have h := legalClosure_le_radicalCompatible hf 4 (by norm_num)
  rw [hrad] at h
  exact sub_eq_zero.mpr h
theorem fourSite_one : fourSite qOne = 0 := by
  simp only [fourSite, qDifference, qSequence_qOne]
  norm_num [qOneSequence]
theorem fourSite_residue_three : fourSite (qResidue 3) = 0 := by
  simp only [fourSite, qDifference, qSequence_qResidue]
  norm_num [residueFraction]
theorem fourSite_residue_four : fourSite (qResidue 4) = -1 := by
  simp only [fourSite, qDifference, qSequence_qResidue]
  norm_num [residueFraction]
theorem fourSite_coprimeThree : fourSite coprimeThree = 1 := by
  rw [coprimeThree, fourSite_sub, fourSite_one]
  simp only [fourSite, qDifference, qSequence_qDivisor]
  norm_num [positiveDivisor]
theorem fourSite_characterThree : fourSite characterThree = 3 := by
  rw [characterThree, fourSite_sub, fourSite_smul, fourSite_smul,
    fourSite_coprimeThree, fourSite_residue_three]
  norm_num
theorem residue_three_decomposition :
    qResidue 3 = (1 / 2 : ℝ) • coprimeThree - (1 / 6 : ℝ) • characterThree := by
  unfold characterThree
  module
theorem coprimeThree_not_mem :
    coprimeThree ∉ qSquarefreeCRTSpan.topologicalClosure := by
  intro h
  have hz := fourSite_legal h
  rw [fourSite_coprimeThree] at hz
  norm_num at hz
theorem characterThree_not_mem :
    characterThree ∉ qSquarefreeCRTSpan.topologicalClosure := by
  intro h
  have hz := fourSite_legal h
  rw [fourSite_characterThree] at hz
  norm_num at hz
theorem residue_four_not_mem :
    qResidue 4 ∉ qSquarefreeCRTSpan.topologicalClosure := by
  intro h
  have hz := fourSite_legal h
  rw [fourSite_residue_four] at hz
  norm_num at hz
theorem legalClosure_ne_top : qSquarefreeCRTSpan.topologicalClosure ≠ ⊤ := by
  intro h
  apply residue_four_not_mem
  rw [h]
  trivial
theorem coprimeThree_sequence (n : ℕ) :
    qSequence coprimeThree n =
      if n = 0 then 0 else if 3 ∣ n then 0 else 1 := by
  have h := congrFun (qSequenceLinear.map_sub qOne (qDivisor 3)) n
  change qSequence coprimeThree n = qSequence qOne n - qSequence (qDivisor 3) n at h
  rw [h, qSequence_qOne, qSequence_qDivisor]
  by_cases hn : n = 0 <;> by_cases hd : 3 ∣ n <;>
    simp [qOneSequence, positiveDivisor, hn, hd]
theorem characterThree_sequence (n : ℕ) :
    qSequence characterThree n =
      if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0 := by
  have hsub := congrFun (qSequenceLinear.map_sub
    ((3 : ℝ) • coprimeThree) ((6 : ℝ) • qResidue 3)) n
  have h3 := congrFun (qSequenceLinear.map_smul (3 : ℝ) coprimeThree) n
  have h6 := congrFun (qSequenceLinear.map_smul (6 : ℝ) (qResidue 3)) n
  change qSequence characterThree n =
    qSequence ((3 : ℝ) • coprimeThree) n -
    qSequence ((6 : ℝ) • qResidue 3) n at hsub
  change qSequence ((3 : ℝ) • coprimeThree) n = 3 * qSequence coprimeThree n at h3
  change qSequence ((6 : ℝ) • qResidue 3) n = 6 * qSequence (qResidue 3) n at h6
  rw [hsub, h3, h6, coprimeThree_sequence, qSequence_qResidue]
  by_cases hn : n = 0
  · subst n
    norm_num [residueFraction]
  · have hm : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hm with hm | hm | hm <;>
      simp [residueFraction, hn, Nat.dvd_iff_mod_eq_zero, hm] <;> norm_num
end RiemannResearch.RH.QModThreeTensorLegality
