/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Normed.Group.InfiniteSum
/-!
# Exact integration under a finite pushforward

Source: user-provided weighted CRT manuscript, 1 November 2026,
"The exact arithmetic measure on a periodic primitive". The argument
is ordinary absolutely convergent regrouping. The concrete RH consumer
is QWeightedResidues.periodic_cumulative_energy.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteWeightedPushforward
variable {α β : Type*} [Fintype β] [DecidableEq β]
def pushWeight (w : α → ℝ) (π : α → β) (b : β) : ℝ :=
  ∑' a, if π a = b then w a else 0
theorem integral_pushWeight (w : α → ℝ) (π : α → β)
    (hw : Summable w) (F : β → ℝ) :
    (∑ b, pushWeight w π b * F b) = ∑' a, w a * F (π a) := by
  classical
  have hf (b : β) : Summable (fun a => if π a = b then w a else 0) := by
    exact (hw.indicator {a | π a = b}).congr (fun a => by
      by_cases h : π a = b <;> simp [h])
  calc
    _ = ∑ b, ∑' a, (if π a = b then w a else 0) * F b := by
      simp only [pushWeight, tsum_mul_right]
    _ = ∑' a, ∑ b, (if π a = b then w a else 0) * F b :=
      (Summable.tsum_finsetSum (fun b _ => (hf b).mul_right (F b))).symm
    _ = _ := tsum_congr (fun a => by simp [ite_mul])
theorem summable_weighted_comp (w : α → ℝ) (π : α → β)
    (hw : Summable w) (F : β → ℝ) :
    Summable (fun a => w a * F (π a)) := by
  classical
  have hf (b : β) : Summable (fun a => (if π a = b then w a else 0) * F b) := by
    have hs : Summable (fun a => if π a = b then w a else 0) := by
      exact (hw.indicator {a | π a = b}).congr (fun a => by
        by_cases h : π a = b <;> simp [h])
    exact hs.mul_right _
  simpa [ite_mul] using summable_sum (s := Finset.univ) (fun b _ => hf b)

end RiemannResearch.Analysis.FiniteWeightedPushforward
