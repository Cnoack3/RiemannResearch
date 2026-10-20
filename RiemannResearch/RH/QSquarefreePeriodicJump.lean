/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDivisorLegality

/-!
# Power-invariant jumps throughout the squarefree Q closure

Every physical jump of a squarefree residue atom depends only on its
squarefree divisor events. The same statement survives linear combination
and complete-Q closure because every physical coordinate is continuous.
In particular, replacing a positive site by any positive power preserves
the jump. This supplies the closure input for the finite-cylinder rigidity
argument; it does not assert that the constant belongs to the legal closure.

Source: the cylinder-intersection question in
`RH_CRT_Profinite_Research_Handoff_Verified_2100`, Section 10, and the
existing `SquarefreeRadicalDifference` and `QDivisorLegality` arguments.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreePeriodicJump
open ZetaTwoHilbert ZetaTwoProbability SquarefreeRadicalDifference QDivisorLegality

/-- The actual legal span respects all equal squarefree-divisor events. -/
theorem squarefree_span_difference_eq_of_same_divisors
    (m a : ℕ) (hm : 1 ≤ m) (ha : 1 ≤ a)
    (hdiv : ∀ d : ℕ, Squarefree d → 2 ≤ d → (d ∣ m ↔ d ∣ a))
    (x : QHilbert) (hx : x ∈ qSquarefreeCRTSpan) :
    qDifference x m = qDifference x a := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨d, rfl⟩ := hx
      unfold qDifference
      simp only [qSequence_qResidue]
      exact residueFraction_difference_eq_of_dvd_iff d.val m a
        d.property.1 hm ha (hdiv d.val d.property.2 d.property.1)
  | zero => rw [qDifference_zero, qDifference_zero]
  | add x y hx hy ihx ihy =>
      rw [qDifference_add, qDifference_add, ihx, ihy]
  | smul c x hx ih =>
      rw [qDifference_smul, qDifference_smul, ih]

/-- The complete-Q legal closure preserves the same finite-coordinate relation. -/
theorem squarefree_closure_difference_eq_of_same_divisors
    (m a : ℕ) (hm : 1 ≤ m) (ha : 1 ≤ a)
    (hdiv : ∀ d : ℕ, Squarefree d → 2 ≤ d → (d ∣ m ↔ d ∣ a))
    (x : QHilbert) (hx : x ∈ qSquarefreeCRTSpan.topologicalClosure) :
    qDifference x m = qDifference x a := by
  exact closure_minimal
    (fun y hy => squarefree_span_difference_eq_of_same_divisors m a hm ha hdiv y hy)
    (isClosed_eq (continuous_qDifference m) (continuous_qDifference a)) hx

/-- Arbitrary positive powers, rather than only squares, preserve legal jumps. -/
theorem squarefree_closure_difference_pow
    (a k : ℕ) (ha : 1 ≤ a) (hk : k ≠ 0)
    (x : QHilbert) (hx : x ∈ qSquarefreeCRTSpan.topologicalClosure) :
    qDifference x (a ^ k) = qDifference x a := by
  apply squarefree_closure_difference_eq_of_same_divisors (a ^ k) a
    (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero k (by omega))) ha ?_ x hx
  intro d hd _
  exact hd.dvd_pow_iff_dvd hk

end RiemannResearch.RH.QSquarefreePeriodicJump
