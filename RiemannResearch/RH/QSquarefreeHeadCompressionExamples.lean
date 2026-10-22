/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeHeadCompression
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Small exact squarefree-head compression examples

Source: user-directed small exact arithmetic investigation, 22 October 2026.
These verify the literal rational observation matrices and physical heads.
No decimal Gram eigenvalue is asserted as a Lean theorem.
-/

noncomputable section
open scoped Matrix
namespace RiemannResearch.RH.QSquarefreeHeadCompressionExamples
open QSquarefreeHeadCompression ZetaTwoHilbert ArithmeticCumulative

/-- F(1), F(2)-F(1), F(3)-F(1), on conductors 2,3,5. -/
def threeByThree : Matrix (Fin 3) (Fin 3) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1/2
  | 0, 1 => 1/3
  | 0, 2 => 1/5
  | 1, 0 => -1/2
  | 1, 1 => 1/3
  | 1, 2 => 1/5
  | 2, 1 => -1/3
  | 2, 2 => 2/5
  | _, _ => 0

theorem threeByThree_det : threeByThree.det = 1/5 := by
  norm_num [threeByThree, Matrix.det_fin_three]

theorem exact_four_head (n : ℕ) (hn : 1 ≤ n) (hn4 : n ≤ 4) :
    residueFraction 2 n + residueFraction 3 n + (5/6 : ℝ) * residueFraction 5 n = 1 := by
  interval_cases n <;> norm_num [residueFraction]

theorem exact_six_head (n : ℕ) (hn : 1 ≤ n) (hn6 : n ≤ 6) :
    residueFraction 2 n + residueFraction 3 n + residueFraction 5 n -
      residueFraction 6 n + (14/15 : ℝ) * residueFraction 7 n = 1 := by
  interval_cases n <;> norm_num [residueFraction]

/-- Four literal rows have precisely rank three in this concrete dictionary. -/
theorem four_site_rank :
    Module.finrank ℝ
      ((physicalMap 4).comp (Fintype.linearCombination ℝ
        (fun d : ({2, 3, 5} : Finset ℕ) => qResidue d))).range = 3 := by
  have hs : ∀ d ∈ ({2, 3, 5} : Finset ℕ), 2 ≤ d ∧ Squarefree d := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact ⟨by decide, (by norm_num : Nat.Prime 2).squarefree⟩
    · exact ⟨by decide, (by norm_num : Nat.Prime 3).squarefree⟩
    · exact ⟨by decide, (by norm_num : Nat.Prime 5).squarefree⟩
  have hsmall : ∀ d, 2 ≤ d → d ≤ 4 → Squarefree d → d ∈ ({2, 3, 5} : Finset ℕ) := by
    intro d hd hd4 hsf
    interval_cases d <;> norm_num [show ¬ Squarefree 4 by decide] at *
  have h := physical_rank {2, 3, 5} hs 4 5 (by decide) (by simp) (by decide) hsmall
  have hsites : sites 4 = {1, 2, 3} := by
    ext n
    simp only [sites, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hn1, hn4⟩, hsf⟩
      interval_cases n <;> simp_all [show ¬ Squarefree 4 by decide]
    · rintro (rfl | rfl | rfl) <;>
        norm_num [Nat.prime_two.squarefree, Nat.prime_three.squarefree]
  have hc : (sites 4).card = 3 := by rw [hsites]; decide
  simpa only [hc] using h

end RiemannResearch.RH.QSquarefreeHeadCompressionExamples
