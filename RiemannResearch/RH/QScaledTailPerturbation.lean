/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPhysicalTailEnergy
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stability of divergent scaled Q tails under bounded-tail perturbations

Source: the user's measure-change agenda, 25 October 2026, and the exact
Hilbert norm identity. The signed identity is retained before estimating it.
This module has no annihilator, squarefree, or RH hypothesis.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QAnnihilatorTailEscape
open ZetaTwoHilbert QFiniteSupportDualCriterion

theorem tail_sub (N : ℕ) (f g : QHilbert) :
    tail N (f - g) = tail N f - tail N g := by
  apply Subtype.ext
  funext n
  change f n - g n - finiteHead N (f - g) n =
    (f n - finiteHead N f n) - (g n - finiteHead N g n)
  by_cases hn : n < N
  · rw [finiteHead_apply_of_lt N (f - g) n hn,
      finiteHead_apply_of_lt N f n hn, finiteHead_apply_of_lt N g n hn]
    change f n - g n - (f n - g n) = _
    ring
  · have hNn : N ≤ n := Nat.le_of_not_gt hn
    rw [finiteHead_apply_eq_zero N (f - g) n hNn,
      finiteHead_apply_eq_zero N f n hNn, finiteHead_apply_eq_zero N g n hNn]
    ring

/-- Complete signed tail identity, before the upper bound. -/
theorem tail_sub_energy_exact (N : ℕ) (f g : QHilbert) :
    ‖tail N (f - g)‖ ^ 2 = ‖tail N f‖ ^ 2 + ‖tail N g‖ ^ 2 -
      2 * inner ℝ (tail N f) (tail N g) := by
  rw [tail_sub, norm_sub_sq_real]
  ring

/-- A bounded scaled tail cannot cancel a divergent scaled tail. -/
theorem scaled_tail_transfer_sub (f g : QHilbert) (C : ℝ)
    (hf : ∀ N : ℕ, (N : ℝ) * ‖tail N f‖ ^ 2 ≤ C)
    (hfg : Tendsto (fun N : ℕ => (N : ℝ) * ‖tail N (f - g)‖ ^ 2)
      atTop atTop) :
    Tendsto (fun N : ℕ => (N : ℝ) * ‖tail N g‖ ^ 2) atTop atTop := by
  apply tendsto_atTop.2
  intro A
  have ht := hfg.eventually (eventually_ge_atTop (2 * C + 2 * A))
  filter_upwards [ht] with N hN
  have hn : ‖tail N (f - g)‖ ≤ ‖tail N f‖ + ‖tail N g‖ := by
    rw [tail_sub]
    exact norm_sub_le _ _
  have hs : ‖tail N (f - g)‖ ^ 2 ≤
      2 * ‖tail N f‖ ^ 2 + 2 * ‖tail N g‖ ^ 2 := by
    nlinarith [norm_nonneg (tail N (f - g)), norm_nonneg (tail N f),
      norm_nonneg (tail N g), sq_nonneg (‖tail N f‖ - ‖tail N g‖)]
  have hmul := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hb := hf N
  nlinarith


/-- Transfer divergent weighted tails through an eventually bounded perturbation. -/
theorem weighted_tail_transfer_sub (f g : QHilbert) (w : ℕ → ℝ)
    (hw : ∀ᶠ N in atTop, 0 ≤ w N) (C : ℝ)
    (hf : ∀ᶠ N in atTop, w N * ‖tail N f‖ ^ 2 ≤ C)
    (hfg : Tendsto (fun N => w N * ‖tail N (f - g)‖ ^ 2) atTop atTop) :
    Tendsto (fun N => w N * ‖tail N g‖ ^ 2) atTop atTop := by
  apply tendsto_atTop.2
  intro A
  have ht := hfg.eventually (eventually_ge_atTop (2 * C + 2 * A))
  filter_upwards [ht, hw, hf] with N hN hwN hfN
  have hn : ‖tail N (f - g)‖ ≤ ‖tail N f‖ + ‖tail N g‖ := by
    rw [tail_sub]
    exact norm_sub_le _ _
  have hs : ‖tail N (f - g)‖ ^ 2 ≤
      2 * ‖tail N f‖ ^ 2 + 2 * ‖tail N g‖ ^ 2 := by
    nlinarith [norm_nonneg (tail N (f - g)), norm_nonneg (tail N f),
      norm_nonneg (tail N g), sq_nonneg (‖tail N f‖ - ‖tail N g‖)]
  have hmul := mul_le_mul_of_nonneg_left hs hwN
  nlinarith

end RiemannResearch.RH.QAnnihilatorTailEscape
