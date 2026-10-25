/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.FiniteCoordinateConvergence
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.ThresholdHilbertSpace
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite-head convergence in the Q and Pareto Hilbert realizations

Source: user-provided projection-limit discussion, 25 October 2026.
Norm convergence gives uniform convergence on every fixed finite positive
head. The Hilbert limits need not equal the constant target. The maximum
uses a nonempty head; the epsilon statements also allow H = 0.
-/

noncomputable section
open Filter
open scoped Topology
open RiemannResearch.Analysis

namespace RiemannResearch.RH.ZetaTwoHilbert

/-- The literal maximum Q-coordinate error on a fixed nonempty head tends to zero. -/
theorem qSequence_head_max_tendsto {u : ℕ → QHilbert} {f : QHilbert}
    (hu : Tendsto u atTop (𝓝 f)) (H : ℕ) (hH : 1 ≤ H) :
    Tendsto (fun M => (Finset.Icc 1 H).sup' (Finset.nonempty_Icc.mpr hH)
      (fun k => |qSequence (u M) k - qSequence f k|)) atTop (𝓝 0) :=
  finite_max_abs_sub_tendsto (qSequence_tendsto_of_tendsto hu) _ _

/-- A common eventual error bound for all positive Q coordinates up to H. -/
theorem qSequence_uniform_on_head {u : ℕ → QHilbert} {f : QHilbert}
    (hu : Tendsto u atTop (𝓝 f)) (H : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M in atTop, ∀ k, 1 ≤ k → k ≤ H →
      |qSequence (u M) k - qSequence f k| < ε := by
  filter_upwards [finite_abs_sub_eventually
    (qSequence_tendsto_of_tendsto hu) (Finset.Icc 1 H) hε] with M hM
  intro k hk hH
  exact hM k (Finset.mem_Icc.mpr ⟨hk, hH⟩)

end RiemannResearch.RH.ZetaTwoHilbert

namespace RiemannResearch.RH.Pareto

/-- Pareto norm convergence gives full-sequence convergence at every physical site. -/
theorem hilbertSequence_tendsto_of_tendsto {u : ℕ → ThresholdHilbert}
    {f : ThresholdHilbert} (hu : Tendsto u atTop (𝓝 f)) (k : ℕ) :
    Tendsto (fun M => hilbertSequence (u M) k) atTop (𝓝 (hilbertSequence f k)) := by
  cases k with
  | zero => simp
  | succ n =>
      have ht := ((lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n).continuous.tendsto f).comp hu
      change Tendsto (fun M => (u M) n) atTop (𝓝 (f n)) at ht
      exact ht.div_const (Real.sqrt (paretoWeight n))

/-- The literal maximum Pareto-coordinate error on a fixed nonempty head tends to zero. -/
theorem hilbertSequence_head_max_tendsto {u : ℕ → ThresholdHilbert}
    {f : ThresholdHilbert} (hu : Tendsto u atTop (𝓝 f)) (H : ℕ) (hH : 1 ≤ H) :
    Tendsto (fun M => (Finset.Icc 1 H).sup' (Finset.nonempty_Icc.mpr hH)
      (fun k => |hilbertSequence (u M) k - hilbertSequence f k|)) atTop (𝓝 0) :=
  finite_max_abs_sub_tendsto (hilbertSequence_tendsto_of_tendsto hu) _ _

/-- A common eventual error bound for all positive Pareto coordinates up to H. -/
theorem hilbertSequence_uniform_on_head {u : ℕ → ThresholdHilbert}
    {f : ThresholdHilbert} (hu : Tendsto u atTop (𝓝 f)) (H : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M in atTop, ∀ k, 1 ≤ k → k ≤ H →
      |hilbertSequence (u M) k - hilbertSequence f k| < ε := by
  filter_upwards [finite_abs_sub_eventually
    (hilbertSequence_tendsto_of_tendsto hu) (Finset.Icc 1 H) hε] with M hM
  intro k hk hH
  exact hM k (Finset.mem_Icc.mpr ⟨hk, hH⟩)

end RiemannResearch.RH.Pareto
