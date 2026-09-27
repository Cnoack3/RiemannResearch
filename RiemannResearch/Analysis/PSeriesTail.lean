/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Explicit tails of real p-series

The proof specializes Mathlib's formalized integral comparison and improper
power integral. The concrete consumer is the quantitative truncation bound
in `RH/DampedMobiusFiniteEnergy`.
Source for this proof strategy and its checked primitives:
Mathlib.Analysis.SumIntegralComparisons and
Mathlib.Analysis.SpecialFunctions.ImproperIntegrals.
-/

open Set MeasureTheory

namespace Real

/-- The integral-test bound for the tail after `N` of a convergent real p-series. -/
theorem tsum_nat_rpow_tail_le {p : ℝ} (hp : 1 < p) {N : ℕ} (hN : 1 ≤ N) :
    (∑' k : ℕ, ((k + N + 1 : ℕ) : ℝ) ^ (-p)) ≤
      (N : ℝ) ^ (1 - p) / (p - 1) := by
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hexp : -p < -1 := by linarith
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-p)) (Ici (N : ℝ)) := by
    intro x hx y _hy hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hNpos hx) hxy (by linarith)
  calc
    (∑' k : ℕ, ((k + N + 1 : ℕ) : ℝ) ^ (-p)) ≤
        ∫ x : ℝ in Ioi (N : ℝ), x ^ (-p) :=
      AntitoneOn.tsum_comp_add_le_integral N hanti
        (integrableOn_Ioi_rpow_of_lt hexp hNpos)
        (fun x hx => Real.rpow_nonneg (le_of_lt (lt_trans hNpos hx)) _)
    _ = (N : ℝ) ^ (1 - p) / (p - 1) := by
      rw [integral_Ioi_rpow_of_lt hexp hNpos]
      rw [show -p + 1 = 1 - p by ring]
      rw [show 1 - p = -(p - 1) by ring, neg_div_neg_eq]

end Real
