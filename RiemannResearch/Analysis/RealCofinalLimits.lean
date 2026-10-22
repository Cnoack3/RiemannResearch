/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Cofinal approximate bounds for convergent real sequences

Elementary order-topology lemmas used by the Pareto first-coordinate criteria.
Source: direct epsilon argument; no novelty claim.
-/

open Filter
open scoped Topology

namespace RiemannResearch.Analysis

/-- A convergent scalar sequence with arbitrarily late epsilon upper bounds
has its limit below the same endpoint. No monotonicity is required. -/
theorem limit_le_of_cofinal_le_add {f : ℕ → ℝ} {a L : ℝ}
    (hf : Tendsto f atTop (𝓝 a))
    (h : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n, N ≤ n ∧ f n ≤ L + ε) :
    a ≤ L := by
  by_contra hnot
  have hLa : L < a := lt_of_not_ge hnot
  have heps : 0 < (a - L) / 2 := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hf.eventually_const_lt (show L + (a - L) / 2 < a by linarith))
  obtain ⟨n, hn, hfn⟩ := h ((a - L) / 2) heps N
  exact (not_lt_of_ge hfn) (hN n hn)

theorem cofinal_le_add_of_tendsto {f : ℕ → ℝ} {a : ℝ}
    (hf : Tendsto f atTop (𝓝 a)) :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n, N ≤ n ∧ f n ≤ a + ε := by
  intro ε hε N
  obtain ⟨K, hK⟩ := eventually_atTop.1
    (hf.eventually_lt_const (show a < a + ε by linarith))
  refine ⟨max N K, le_max_left _ _, ?_⟩
  exact le_of_lt (hK _ (le_max_right _ _))

end RiemannResearch.Analysis
