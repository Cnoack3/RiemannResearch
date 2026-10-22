/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteGramOneStepCapacity
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Bounds for the actual one-vector Schur energy

Source: the user's 15 October 2026 request to specialize the exact one-step
capacity identity. These are elementary Hilbert-space consequences of the
existing screening normal equations. No mathematical novelty is claimed.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.Analysis.FiniteHilbertGram

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Orthogonal screening cannot increase the complete Hilbert energy. -/
theorem screenedVector_energy_le (v : ι → H) (f : H) :
    ‖screenedVector v f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have hp := gram_quadratic v (screeningCoeff v f)
  rw [screeningCoeff_normal] at hp
  rw [screenedVector_energy]
  nlinarith only [hp, sq_nonneg ‖Fintype.linearCombination ℝ v (screeningCoeff v f)‖]

/-- Independence of the enlarged family makes its true Schur energy positive.
This places no condition on the screened source defect. -/
theorem screenedVector_energy_pos_of_linearIndependent
    (v : ι → H) (f : H)
    (hv : LinearIndependent ℝ (Sum.elim v (fun _ : Unit => f))) :
    0 < ‖screenedVector v f‖ ^ 2 := by
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hzero
  let a : ι ⊕ Unit → ℝ :=
    Sum.elim (fun i => -screeningCoeff v f i) (fun _ => 1)
  have ha : Fintype.linearCombination ℝ
      (Sum.elim v (fun _ : Unit => f)) a = screenedVector v f := by
    simp only [Fintype.linearCombination_apply, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique, a, neg_smul,
      one_smul, Finset.sum_neg_distrib, screenedVector]
    abel
  have hcoeff : a = 0 := hv.fintypeLinearCombination_injective (by
    simpa only [map_zero] using ha.trans hzero)
  have hlast := congrFun hcoeff (Sum.inr ())
  norm_num [a] at hlast

end RiemannResearch.Analysis.FiniteHilbertGram
