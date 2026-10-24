/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.Analysis.QuantitativeBlockAverages
import RiemannResearch.Analysis.GeometricHeadSelection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Explicit complete-P pairings for exact physical heads

Source: user-provided `RH_Constructive_Approximants_Research_Agenda_2026-10-24`,
Section 8.2, for the effective tail-selection argument. Existing exact complete
tail identities from `ExactHeadResidualTail` supply the analytic input.

The head-selection inequalities involve only earlier physical amplitude
bounds, the selected head length, and the geometric tolerance. The common
full residual energy bound remains an explicit arithmetic hypothesis.
-/

open scoped BigOperators

namespace RiemannResearch.RH.Pareto

open RiemannResearch.Analysis

/-- Physical vanishing through N is exactly enough to apply the existing
full-tail Cauchy-Schwarz estimate. No tail of either vector is omitted. -/
theorem exact_head_pairing_sq_le
    (r e : ThresholdHilbert) (N : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hr : ∀ n, 0 < n → |hilbertSequence r n| ≤ A)
    (he : ∀ n, 0 < n → n ≤ N → hilbertSequence e n = 0) :
    (inner ℝ r e) ^ 2 ≤ A ^ 2 / ((N : ℝ) + 1) * ‖e‖ ^ 2 := by
  have he' : ∀ n < N, e n = 0 := by
    intro n hn
    have hh := hilbertSequence_weighted_square e n
    rw [he (n + 1) (by omega) (by omega)] at hh
    nlinarith
  exact (hilbertTailShift_inner_sq_le r e N he').trans
    (mul_le_mul_of_nonneg_right
      (hilbertTailShift_norm_sq_le_of_bounded r N A hA hr) (sq_nonneg _))

/-- A purely numerical head-length inequality gives the desired geometric
pairing. The selection inequality does not require the numerical value of C. -/
theorem exact_head_pairing_le_geometric
    (r e : ThresholdHilbert) (N j : ℕ) (A C : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hr : ∀ n, 0 < n → |hilbertSequence r n| ≤ A)
    (he : ∀ n, 0 < n → n ≤ N → hilbertSequence e n = 0)
    (henergy : ‖e‖ ^ 2 ≤ C ^ 2)
    (hselect : A ^ 2 ≤ ((N : ℝ) + 1) * ((1 / 2 : ℝ) ^ (j + 1)) ^ 2) :
    |inner ℝ r e| ≤ C * (1 / 2 : ℝ) ^ (j + 1) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have htail : A ^ 2 / ((N : ℝ) + 1) ≤ ((1 / 2 : ℝ) ^ (j + 1)) ^ 2 := by
    apply (div_le_iff₀ hN).2
    simpa only [mul_comm] using hselect
  have hs : (inner ℝ r e) ^ 2 ≤
      ((1 / 2 : ℝ) ^ (j + 1)) ^ 2 * C ^ 2 :=
    (exact_head_pairing_sq_le r e N A hA hr he).trans
      (mul_le_mul htail henergy (sq_nonneg _) (sq_nonneg _))
  have hs' : |inner ℝ r e| ^ 2 ≤ (C * (1 / 2 : ℝ) ^ (j + 1)) ^ 2 := by
    simpa only [sq_abs, mul_pow, mul_comm] using hs
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC (by positivity))).mp hs'

/-- The explicit selection criterion supplies all pairwise estimates needed by
the block-averaging theorem for an actual complete-P exact-head family. -/
theorem selected_exact_head_pairings
    (r : ℕ → ThresholdHilbert) (N : ℕ → ℕ) (U : ℕ → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hU : ∀ i, 0 ≤ U i)
    (hbound : ∀ i, ‖r i‖ ^ 2 ≤ C ^ 2)
    (hphysical : ∀ i n, 0 < n → |hilbertSequence (r i) n| ≤ U i)
    (hhead : ∀ j n, 0 < n → n ≤ N j → hilbertSequence (r j) n = 0)
    (hselect : ∀ i j, i < j →
      (U i) ^ 2 ≤ ((N j : ℝ) + 1) * ((1 / 2 : ℝ) ^ (j + 1)) ^ 2) :
    ∀ i j, i < j → |inner ℝ (r i) (r j)| ≤ C * (1 / 2 : ℝ) ^ (j + 1) := by
  intro i j hij
  exact exact_head_pairing_le_geometric (r i) (r j) (N j) j (U i) C
    (hU i) hC (hphysical i) (hhead j) (hbound j) (hselect i j hij)

/-- Full complete-P block estimate from effective physical-head selection.
The sole common energy bound is exposed as hbound. -/
theorem selected_exact_head_block_average_bound
    (r : ℕ → ThresholdHilbert) (N : ℕ → ℕ) (U : ℕ → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hU : ∀ i, 0 ≤ U i)
    (hbound : ∀ i, ‖r i‖ ^ 2 ≤ C ^ 2)
    (hphysical : ∀ i n, 0 < n → |hilbertSequence (r i) n| ≤ U i)
    (hhead : ∀ j n, 0 < n → n ≤ N j → hilbertSequence (r j) n = 0)
    (hselect : ∀ i j, i < j →
      (U i) ^ 2 ≤ ((N j : ℝ) + 1) * ((1 / 2 : ℝ) ^ (j + 1)) ^ 2)
    (a : ℕ) {m : ℕ} (hm : 0 < m) :
    ‖((m : ℝ)⁻¹) • (∑ i ∈ Finset.range m, r (a + i))‖ ^ 2 ≤
      C ^ 2 / m + 2 * C * (1 / 2 : ℝ) ^ a / (m : ℝ) ^ 2 := by
  apply norm_sq_block_average_le_simple r hC hbound _ a hm
  intro i j hij
  exact (le_abs_self _).trans
    (selected_exact_head_pairings r N U C hC hU hbound hphysical hhead hselect i j hij)

end RiemannResearch.RH.Pareto

open scoped BigOperators

namespace RiemannResearch.RH.Pareto

open RiemannResearch.Analysis

/-- The online integer recurrence discharges every geometric selection
condition. Only the common complete residual energy bound remains analytic.
For legal exact-head candidates G_N, apply this to r_N = G_N - 1. -/
theorem online_exact_head_block_average_bound
    (r : ℕ → ThresholdHilbert) (U : ℕ → ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ N, ‖r N‖ ^ 2 ≤ C ^ 2)
    (hphysical : ∀ N n, 0 < n → |hilbertSequence (r N) n| ≤ (U N : ℝ))
    (hhead : ∀ N n, 0 < n → n ≤ N → hilbertSequence (r N) n = 0)
    (a : ℕ) {m : ℕ} (hm : 0 < m) :
    ‖((m : ℝ)⁻¹) •
        (∑ i ∈ Finset.range m, r (exactHeadSelection U (a + i)))‖ ^ 2 ≤
      C ^ 2 / m + 2 * C * (1 / 2 : ℝ) ^ a / (m : ℝ) ^ 2 := by
  exact selected_exact_head_block_average_bound
    (fun i => r (exactHeadSelection U i)) (exactHeadSelection U)
    (fun i => (U (exactHeadSelection U i) : ℝ)) C hC
    (fun i => Nat.cast_nonneg _) (fun i => hbound _)
    (fun i => hphysical _) (fun i => hhead _)
    (fun _ _ hij => exactHeadSelection_real_certificate U hij) a hm

end RiemannResearch.RH.Pareto
