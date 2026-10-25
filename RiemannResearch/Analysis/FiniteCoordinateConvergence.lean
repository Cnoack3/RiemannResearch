/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Order.Lattice

/-!
# Uniform convergence on finite sets of real coordinates

Source: user-provided argument, 25 October 2026: finitely many pointwise
convergence bounds have a common eventual threshold. This supplies the
finite-head convergence consumers for the Q and Pareto Hilbert spaces.
-/

open Filter
open scoped Topology

namespace RiemannResearch.Analysis

theorem finite_abs_sub_eventually {ι : Type*} {f : ℕ → ι → ℝ} {g : ι → ℝ}
    (h : ∀ i, Tendsto (fun M => f M i) atTop (𝓝 (g i)))
    (s : Finset ι) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M in atTop, ∀ i ∈ s, |f M i - g i| < ε := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have ht : Tendsto (fun M => |f M i - g i|) atTop (𝓝 0) := by
        simpa using ((h i).sub (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => g i) atTop (𝓝 (g i)))).abs
      have he := (tendsto_order.mp ht).2 ε hε
      filter_upwards [he, ih] with M hMi hMs
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hMi
      · exact hMs j hj

theorem finite_max_abs_sub_tendsto {ι : Type*} {f : ℕ → ι → ℝ} {g : ι → ℝ}
    (h : ∀ i, Tendsto (fun M => f M i) atTop (𝓝 (g i)))
    (s : Finset ι) (hs : s.Nonempty) :
    Tendsto (fun M => s.sup' hs (fun i => |f M i - g i|)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (finite_abs_sub_eventually h s hε)
  refine ⟨N, fun M hM => ?_⟩
  have hnonneg : 0 ≤ s.sup' hs (fun i => |f M i - g i|) := by
    obtain ⟨i, hi⟩ := hs
    exact (abs_nonneg _).trans (Finset.le_sup' (fun i => |f M i - g i|) hi)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact (Finset.sup'_lt_iff hs).mpr (hN M hM)

end RiemannResearch.Analysis
