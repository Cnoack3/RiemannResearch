/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.DyadicWeightedContrast
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Summability from dyadic block budgets

Source: SquarefreeShortHeadSchurResearch20261030.md, section 6. Finite dyadic
accounting is reused from DyadicWeightedContrast. The concrete RH consumer is
QPolylogBlockEnergy: a summable block majorant yields complete weighted energy.
No arithmetic estimate is assumed beyond the displayed block hypothesis.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.DyadicWeightedContrast

/-- The converse direction of finite dyadic grouping, with an arbitrary
summable nonnegative block majorant. -/
theorem summable_of_dyadic_block_majorant (a b : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ j, 0 ≤ b j) (hs : Summable b)
    (hblock : ∀ j, (∑ i ∈ Finset.range (2 ^ j), a (2 ^ j + i)) ≤ b j) :
    Summable a := by
  have hp (J : ℕ) :
      (∑ n ∈ Finset.range (2 ^ J), a n) ≤ a 0 + ∑' j, b j := by
    have h := Finset.sum_le_sum (fun j (_hj : j ∈ Finset.range J) => hblock j)
    rw [dyadic_block_sum_eq] at h
    have ht := hs.sum_le_tsum (Finset.range J) (fun j _ => hb j)
    linarith
  have hpow (M : ℕ) : M ≤ 2 ^ M := by
    induction M with
    | zero => simp
    | succ M ih =>
        have hpos : 0 < (2 : ℕ) ^ M := pow_pos (by norm_num) M
        rw [pow_succ]
        omega
  refine summable_of_sum_range_le (c := a 0 + ∑' j, b j) ha ?_
  intro M
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (hpow M))
    (fun n _ _ => ha n)).trans (hp M)

end RiemannResearch.Analysis.DyadicWeightedContrast
