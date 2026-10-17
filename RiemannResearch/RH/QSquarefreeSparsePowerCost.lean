/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeSublinearHeads
import RiemannResearch.RH.QExactHeadSubpolynomial
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# The established and open ranges of sparse squarefree power costs

Source: the user's 17 October 2026 research request and the localized Mellin
obstruction already formalized in QExactHeadSubpolynomial.lean.

The full signed Q error is retained throughout. The exponent-one case and all
larger exponents are unconditional. A fixed exponent a excludes zeros with
2*Re(s)-1 >= a, and exponents tending to zero imply actual Mathlib RH.
The latter consumers are conditional research reductions: no provider for
any exponent in (0,1) is established here.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeSparsePowerCost
open ZetaTwoHilbert ZetaTwoProbability

/-- Complete error, exact physical heads, and independent finite legal choices. -/
def SparsePowerCost (a : ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ N : ℕ,
    ∃ (n : ℕ) (F : QHilbert), 1 ≤ n ∧ N ≤ n ∧ F ∈ qSquarefreeCRTSpan ∧
      (∀ k, 0 < k → k < n → qSequence F k = 1) ∧
        ‖qOne - F‖ ^ 2 < c * (n : ℝ) ^ a

theorem sparsePowerCost_one : SparsePowerCost 1 := by
  intro c hc N
  obtain ⟨p, F, _, hp, hN, hF, hh, he⟩ :=
    QSquarefreeSublinearHeads.arbitrarily_small_linear_cost c hc N
  exact ⟨p, F, hp, hN, hF, hh, by simpa only [Real.rpow_one] using he⟩

/-- Unconditionally proved range. This theorem supplies no exponent below one. -/
theorem sparsePowerCost_of_one_le (a : ℝ) (ha : 1 ≤ a) : SparsePowerCost a := by
  intro c hc N
  obtain ⟨n, F, hn, hN, hF, hh, he⟩ := sparsePowerCost_one c hc N
  have hp : (n : ℝ) ^ (1 : ℝ) ≤ (n : ℝ) ^ a :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) ha
  exact ⟨n, F, hn, hN, hF, hh, he.trans_le (mul_le_mul_of_nonneg_left hp hc.le)⟩

/-- A fixed exponent a rules out zeros with 2*Re(s)-1 >= a.
The displayed sparse-cost input remains a substantive arithmetic obligation. -/
theorem zero_free_of_sparsePowerCost (a : ℝ) (hcost : SparsePowerCost a)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (ha : a ≤ 2 * s.re - 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hc : 0 < (2 * s.re - 1) / (zetaTwo * ‖s‖ ^ 2) :=
    div_pos (by linarith) (mul_pos zetaTwo_pos (pow_pos (norm_pos_iff.mpr hs0) 2))
  obtain ⟨n, F, hn, _, hF, hh, he⟩ := hcost _ hc 1
  have hp : (n : ℝ) ^ a ≤ (n : ℝ) ^ (2 * s.re - 1) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) ha
  have hl := QExactHeadSubpolynomial.exact_head_residual_power_lower
    hF n hn hh s hs hs1 hz
  exact (not_lt_of_ge hl) (he.trans_le (mul_le_mul_of_nonneg_left hp hc.le))

/-- Conditional research reduction: a sequence of sparse-cost exponents
tending to zero suffices; no uniform candidate-energy bound is assumed. -/
theorem riemannHypothesis_of_sparsePowerCost_tendsto_zero
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (hcost : ∀ j, SparsePowerCost (a j)) : RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hslt
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hslt
  have hb : (0 : ℝ) < 2 * s.re - 1 := by linarith
  obtain ⟨j, hj⟩ := (ha.eventually (gt_mem_nhds hb)).exists
  exact zero_free_of_sparsePowerCost (a j) (hcost j) s hs hs1 hj.le

end RiemannResearch.RH.QSquarefreeSparsePowerCost
