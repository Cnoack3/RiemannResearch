/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QMobiusExactHead
import RiemannResearch.RH.QBoundedCoordinateClosure
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith

/-!
# Closure criteria for the original Möbius exact heads

Source: the user's original exact-head construction and request to formalize
the complete-Q epsilon criterion, 22 October 2026.

The weighted-tail identity is unconditional. The RH endpoints are conditional
research reductions: neither a cofinal bounded-energy provider nor a vanishing
full-tail provider is proved here. Exact agreement on each finite head alone
does not imply either hypothesis; see `QExactHeadEscape`.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.QMobiusHeadClosure
open ZetaTwoHilbert QMobiusExactHead

/-- All error lies beyond the exact head, but the entire infinite tail remains. -/
theorem error_sq_eq_weighted_tail (M : ℕ) :
    ‖qOne - exactHead M‖ ^ 2 =
      ∑' n : ℕ, if M < n then
        positiveQWeight n * (1 - qSequence (exactHead M) n) ^ 2 else 0 := by
  rw [qNorm_weighted_sq]
  apply tsum_congr
  intro n
  have hsub : qSequence (qOne - exactHead M) n =
      qSequence qOne n - qSequence (exactHead M) n :=
    congrFun (qSequenceLinear.map_sub qOne (exactHead M)) n
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [hsub, qSequence_qOne]
    simp only [qOneSequence, if_neg hn]
    by_cases hMn : M < n
    · simp only [if_pos hMn]
    · rw [if_neg hMn, exactHead_exact M n hnpos (Nat.le_of_not_gt hMn)]
      simp

/-- Bounded full energy at arbitrarily large head sizes is sufficient.
There is no claim that the original sequence itself converges strongly. -/
theorem qOne_mem_closure_of_cofinal_energy_bound
    (hbound : ∃ B : ℝ, ∀ N : ℕ, ∃ M : ℕ,
      N ≤ M ∧ ‖exactHead M‖ ^ 2 ≤ B) :
    qOne ∈ QFullResidueProjection.legalSpan.topologicalClosure := by
  classical
  obtain ⟨B, hB⟩ := hbound
  choose H hHlarge hHbound using hB
  have hH : Tendsto H atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N] with j hj
    exact hj.trans (hHlarge j)
  apply QBoundedCoordinateClosure.mem_closure_of_eventually_bounded_cofinal_heads
    QFullResidueProjection.legalSpan (fun j => exactHead (H j)) qOne H hH
    (fun j => exactHead_mem_legalSpan (H j)) _ (Eventually.of_forall hHbound)
  intro j k hk hkH
  simpa only [qSequence_qOne, qOneSequence, if_neg (Nat.ne_of_gt hk)] using
    exactHead_exact (H j) k hk hkH

/-- Conditional RH endpoint for the original exact heads and a cofinal budget.
The full-energy bound is an Open arithmetic obligation. -/
theorem riemannHypothesis_of_cofinal_energy_bound
    (hbound : ∃ B : ℝ, ∀ N : ℕ, ∃ M : ℕ,
      N ≤ M ∧ ‖exactHead M‖ ^ 2 ≤ B) : RiemannHypothesis :=
  QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
    (qOne_mem_closure_of_cofinal_energy_bound hbound)

/-- The user's positive-epsilon criterion gives strong convergence of the
original family. Epsilon zero is deliberately excluded. -/
theorem exactHead_tendsto_of_error_epsilon
    (herror : ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ‖qOne - exactHead M‖ ^ 2 ≤ ε) :
    Tendsto exactHead atTop (𝓝 qOne) := by
  have hsquare : Tendsto (fun M => ‖qOne - exactHead M‖ ^ 2) atTop (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro x hx
      exact Eventually.of_forall (fun M => hx.trans_le (sq_nonneg _))
    · intro ε hε
      obtain ⟨M₀, hM₀⟩ := herror (ε / 2) (by linarith)
      filter_upwards [eventually_ge_atTop M₀] with M hM
      exact (hM₀ M hM).trans_lt (by linarith)
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  have hn' : Tendsto (fun M => ‖qOne - exactHead M‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_zero] using hn
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_sub_rev] using hn'

/-- The complete squared-error epsilon estimate implies RH. Its proof uses
only the epsilon-one case to supply the weaker cofinal full-energy bound. -/
theorem riemannHypothesis_of_error_epsilon
    (herror : ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ‖qOne - exactHead M‖ ^ 2 ≤ ε) : RiemannHypothesis := by
  obtain ⟨M₀, hM₀⟩ := herror 1 zero_lt_one
  apply riemannHypothesis_of_cofinal_energy_bound
  refine ⟨4, ?_⟩
  intro N
  refine ⟨max N M₀, le_max_left _ _, ?_⟩
  have he := hM₀ (max N M₀) (le_max_right _ _)
  have ht : ‖exactHead (max N M₀)‖ ≤
      ‖qOne‖ + ‖qOne - exactHead (max N M₀)‖ := by
    simpa only [sub_sub_cancel] using
      norm_sub_le qOne (qOne - exactHead (max N M₀))
  rw [qOne_norm] at ht
  have he' : ‖qOne - exactHead (max N M₀)‖ ≤ 1 := by
    nlinarith [norm_nonneg (qOne - exactHead (max N M₀))]
  nlinarith [norm_nonneg (exactHead (max N M₀))]

/-- Arithmetic full-tail form of the user's epsilon criterion; still conditional
on the estimate for the infinite weighted tail. -/
theorem riemannHypothesis_of_tail_epsilon
    (htail : ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      (∑' n : ℕ, if M < n then
        positiveQWeight n * (1 - qSequence (exactHead M) n) ^ 2 else 0) ≤ ε) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_error_epsilon
  simpa only [error_sq_eq_weighted_tail] using htail

end RiemannResearch.RH.QMobiusHeadClosure
