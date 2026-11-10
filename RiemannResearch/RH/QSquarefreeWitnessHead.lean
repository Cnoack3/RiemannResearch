/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QSquarefreeExactHeadResidualBarrier
import RiemannResearch.RH.QSquarefreeCompatibleHeads
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# The signed witness pairing for squarefree exact-head trials

Source: *Squarefree projection displacement and infinite CRT carries*,
9 November 2026, Section 12.5. The exact head removes the entire head from
the witness pairing. Smallness of the remaining complete tail is an open
arithmetic condition.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QSquarefreeWitnessHead

open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QSquarefreeDisplacementRigidity QSquarefreeExactHeadResidualBarrier
open QSquarefreeCompatibleHeads QFiniteSupportDualCriterion QAnnihilatorTailEscape
open UniqueFactorizationMonoid

theorem annihilator_tail_identity (H : ℕ) (u F : QHilbert)
    (hu : u ∈ ZetaTwoOptimizerStage.closureᗮ) (hF : F ∈ qSquarefreeCRTSpan)
    (hh : ∀ k, 0 < k → k ≤ H → qSequence F k = 1) :
    inner ℝ qOne u = inner ℝ (qOne - F) (tail H u) := by
  have hzero := Submodule.inner_right_of_mem_orthogonal
    (legal_mem_optimizer_closure F hF) hu
  have hhead : inner ℝ F (finiteHead H u) = inner ℝ qOne (finiteHead H u) := by
    apply inner_finiteHead_eq_of_matching_head
    intro k hk hkH
    rw [hh k hk hkH, qSequence_qOne]
    simp [qOneSequence, Nat.ne_of_gt hk]
  rw [tail, inner_sub_right, inner_sub_left, inner_sub_left, hzero, hhead, sub_self,
    sub_zero, sub_zero]

/-- The explicit charge interpolant with any prime anchor above the head is
legal and agrees with one on every positive site of that head. -/
theorem prime_anchor_exact (H p : ℕ) (hp : p.Prime) (hHp : H < p) :
    headInterpolant (qSequence qOne) H p ∈ qSquarefreeCRTSpan ∧
      ∀ k, 0 < k → k ≤ H → qSequence (headInterpolant (qSequence qOne) H p) k = 1 := by
  have hrad : ∀ n, 2 ≤ n → n ≤ H →
      qSequence qOne n - qSequence qOne (n - 1) =
        qSequence qOne (radical n) - qSequence qOne (radical n - 1) := by
    intro n hn _
    have hr := Nat.two_le_radical_iff.mpr hn
    rw [qSequence_qOne]
    simp [qOneSequence, show n ≠ 0 by omega, show n - 1 ≠ 0 by omega,
      show radical n ≠ 0 by omega, show radical n - 1 ≠ 0 by omega]
  have h := headInterpolant_legal_exact (qSequence qOne) H p
    (qSequence_zero qOne) hp hHp hrad
  refine ⟨h.1, fun k hk hkH => ?_⟩
  rw [h.2 k hkH, qSequence_qOne]
  simp [qOneSequence, Nat.ne_of_gt hk]

theorem prime_anchor_witness_tail (H p : ℕ) (hp : p.Prime) (hHp : H < p) :
    inner ℝ qOne witness =
      inner ℝ (qOne - headInterpolant (qSequence qOne) H p) (tail H witness) :=
  annihilator_tail_identity H witness _ witness_mem_orthogonal
    (prime_anchor_exact H p hp hHp).1 (prime_anchor_exact H p hp hHp).2

/-- A sufficient complete-norm certificate on the explicit prime-anchor trials. -/
theorem residual_zero_of_prime_anchor_witness_tail (p : ℕ → ℕ)
    (hp : ∀ H, (p H).Prime ∧ H < p H)
    (hbound : Tendsto (fun H =>
      ‖qOne - headInterpolant (qSequence qOne) H (p H)‖ * ‖tail H witness‖)
        atTop (𝓝 0)) :
    limitingResidual = 0 := by
  have h : |inner ℝ qOne witness| ≤ 0 := by
    apply le_of_tendsto_of_tendsto' tendsto_const_nhds hbound
    intro H
    rw [prime_anchor_witness_tail H (p H) (hp H).1 (hp H).2]
    exact abs_real_inner_le_norm _ _
  exact residual_eq_zero_of_witness_mean_zero (abs_eq_zero.mp
    (le_antisymm h (abs_nonneg _)))

end RiemannResearch.RH.QSquarefreeWitnessHead
