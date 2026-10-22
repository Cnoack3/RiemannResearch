/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoPolygammaResidues
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact all-order reciprocal residue refinement

Source: the residue-class regrouping proof in `QResidueConditional`, extended
from reciprocal squares to every reciprocal order, 20 October 2026.
Mathlib's `Nat.sumByResidueClasses` supplies the complete-series reindexing.
All tails and the positive zero-residue representative are retained.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ZetaTwoProbability

/-- Exact all-order refinement; this is the same residue-class regrouping at order two. -/
theorem residuePowerWeight_refine_order (s L p a : ℕ)
    (hL : 0 < L) (hp : 0 < p) (ha : 0 < a) :
    residuePowerWeight s L a =
      ∑ j : Fin p, residuePowerWeight s (L * p : ℕ) (a + L * j.val : ℕ) := by
  cases p with
  | zero => omega
  | succ p =>
    have hs := residuePowerWeight_summable s
      (show (0 : ℝ) < L by exact_mod_cast hL)
      (show (0 : ℝ) < a by exact_mod_cast ha)
    calc
      residuePowerWeight s L a =
          ∑ j : Fin (p+1), ∑' n : ℕ,
            1 / (zetaTwo * ((a : ℝ) +
              ((j.val + (p+1)*n : ℕ) : ℝ) * (L : ℝ))^(s+2)) :=
        Nat.sumByResidueClasses hs (p+1)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        apply tsum_congr
        intro n
        push_cast
        congr 3
        ring

end RiemannResearch.RH.ZetaTwoProbability
