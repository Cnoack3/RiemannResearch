/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QSquarefreeCoordinates
import RiemannResearch.RH.SquarefreeRadicalDifference
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Necessary squarefree legality constraints

Source: the user-directed squarefree-coordinate discussion and the existing
`SquarefreeRadicalDifference` arithmetic identities. Continuous physical
evaluations pass the radical difference relation to the literal closed squarefree
span. A four-point relation excludes `qResidue 4`, and hence proves that the
legal coordinate image is proper. These necessary relations are not asserted
to characterize that image.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeCoordinateLegality
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeCoordinates
open SquarefreeRadicalDifference UniqueFactorizationMonoid

theorem closure_difference_radical {f : QHilbert}
    (hf : f ∈ qSquarefreeCRTSpan.topologicalClosure)
    (m : ℕ) (hm : 2 ≤ m) :
    qDifference f m = qDifference f (radical m) := by
  have hspan : (qSquarefreeCRTSpan : Set QHilbert) ⊆
      {x | qDifference x m = qDifference x (radical m)} := by
    intro x hx
    change qDifference x m = qDifference x (radical m)
    change x ∈ Submodule.span ℝ
      (Set.range (fun d : {d : ℕ // 2 ≤ d ∧ Squarefree d} => qResidue d.val)) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨d, rfl⟩
        simpa only [qDifference, qSequence_qResidue] using
          residueFraction_difference_radical d.val m d.property.1 d.property.2 hm
    | zero => simp only [qDifference_zero]
    | add x y hx hy ihx ihy =>
        rw [qDifference_add, qDifference_add, ihx, ihy]
    | smul c x hx ih =>
        rw [qDifference_smul, qDifference_smul, ih]
  have hclosed : IsClosed
      {x : QHilbert | qDifference x m = qDifference x (radical m)} :=
    isClosed_eq (continuous_qDifference m) (continuous_qDifference (radical m))
  change f ∈ _root_.closure (qSquarefreeCRTSpan : Set QHilbert) at hf
  exact (closure_minimal hspan hclosed) hf

private theorem sf_atom_difference_four (d : ℕ)
    (hd : 2 ≤ d) (hs : Squarefree d) :
    qDifference (qResidue d) 4 = qDifference (qResidue d) 2 := by
  by_cases hsmall : d ≤ 4
  · have hcases : d = 2 ∨ d = 3 ∨ d = 4 := by omega
    rcases hcases with rfl | rfl | rfl
    · simp only [qDifference, qSequence_qResidue]
      norm_num [ArithmeticCumulative.residueFraction]
    · simp only [qDifference, qSequence_qResidue]
      norm_num [ArithmeticCumulative.residueFraction]
    · exact False.elim ((by decide : ¬ Squarefree (4 : ℕ)) hs)
  · have h1 : 1 < d := by omega
    have h2 : 2 < d := by omega
    have h3 : 3 < d := by omega
    have h4 : 4 < d := by omega
    simp only [qDifference, qSequence_qResidue]
    norm_num [ArithmeticCumulative.residueFraction,
      Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
      Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4]
    ring

theorem closure_difference_four {f : QHilbert}
    (hf : f ∈ qSquarefreeCRTSpan.topologicalClosure) :
    qDifference f 4 = qDifference f 2 := by
  have hspan : (qSquarefreeCRTSpan : Set QHilbert) ⊆
      {x | qDifference x 4 = qDifference x 2} := by
    intro x hx
    change qDifference x 4 = qDifference x 2
    change x ∈ Submodule.span ℝ
      (Set.range (fun d : {d : ℕ // 2 ≤ d ∧ Squarefree d} => qResidue d.val)) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨d, rfl⟩
        exact sf_atom_difference_four d.val d.property.1 d.property.2
    | zero => simp only [qDifference_zero]
    | add x y hx hy ihx ihy =>
        rw [qDifference_add, qDifference_add, ihx, ihy]
    | smul c x hx ih =>
        rw [qDifference_smul, qDifference_smul, ih]
  have hclosed : IsClosed {x : QHilbert | qDifference x 4 = qDifference x 2} :=
    isClosed_eq (continuous_qDifference 4) (continuous_qDifference 2)
  change f ∈ _root_.closure (qSquarefreeCRTSpan : Set QHilbert) at hf
  exact (closure_minimal hspan hclosed) hf

theorem closure_four_point {f : QHilbert}
    (hf : f ∈ qSquarefreeCRTSpan.topologicalClosure) :
    qSequence f 4 - qSequence f 3 - qSequence f 2 + qSequence f 1 = 0 := by
  have h := closure_difference_four hf
  change qSequence f 4 - qSequence f 3 = qSequence f 2 - qSequence f 1 at h
  linarith

theorem qResidue_four_not_mem_closure :
    qResidue 4 ∉ qSquarefreeCRTSpan.topologicalClosure := by
  intro hf
  have h := closure_four_point hf
  simp only [qSequence_qResidue] at h
  norm_num [ArithmeticCumulative.residueFraction] at h

theorem residue_four_coordinates_not_legal :
    fullCoordinates (qResidue 4) ∉ coordinateSpace := by
  intro hz
  have hf := (mem_coordinateSpace _).mp hz
  rw [fullCoordinates.symm_apply_apply] at hf
  exact qResidue_four_not_mem_closure hf

theorem coordinateSpace_ne_top : coordinateSpace ≠ ⊤ := by
  intro heq
  apply residue_four_coordinates_not_legal
  rw [heq]
  exact Submodule.mem_top

end RiemannResearch.RH.QSquarefreeCoordinateLegality
