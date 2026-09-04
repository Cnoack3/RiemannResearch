/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.FiniteDirichletGreenMatrix
import Mathlib.Tactic.Ring

/-!
# Energy of the finite Dirichlet Green matrix

This module proves a finite summation-by-parts identity for the endpoint-zero
Green profile. The quadratic form of finiteDirichletGreenMatrix is exactly
the negative sum of squares of the centered curvature-prefix slopes. It follows
that the form is nonpositive and vanishes exactly at the zero curvature vector,
uniformly including dimension zero.

Source: user-provided argument,
RH_Proof_First_Continuation_2026-09-04.md, Section 5. The source supports the
finite coordinate and gauge strategy; the energy identity is an independent
finite-algebra consequence of those coordinates. This result does not identify
a Weil form, establish dyadic density, or prove RH.
-/

namespace RiemannResearch.RH.PrimeGapCurvature

noncomputable section

open scoped BigOperators

/-- Finite summation by parts, with both endpoint terms retained. -/
theorem finiteSlopeProfile_summation_by_parts
    (n : ℕ) (s : Fin (n + 1) → ℝ) (z : Fin (n + 2) → ℝ) :
    (∑ r : Fin n, (s r.succ - s r.castSucc) * z r.succ.castSucc) =
      -(∑ j : Fin (n + 1), s j * (z j.succ - z j.castSucc)) -
        s 0 * z 0 +
        s (Fin.last n) * z (Fin.last (n + 1)) := by
  simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [Fin.sum_univ_castSucc
    (fun j : Fin (n + 1) => s j * z j.succ)]
  rw [Fin.sum_univ_succ
    (fun j : Fin (n + 1) => s j * z j.castSucc)]
  simp only [Fin.castSucc_succ, Fin.succ_last, Fin.castSucc_zero]
  ring

/-- The Green quadratic form is the negative centered-slope energy. -/
theorem finiteDirichletGreenMatrix_quadraticForm_eq_neg_slopeEnergy
    (n : ℕ) (c : Fin n → ℝ) :
    (∑ r, c r * (finiteDirichletGreenMatrix n).mulVec c r) =
      -(∑ j, (centeredSlopePrefixLinearMap n c j) ^ 2) := by
  let s : Fin (n + 1) → ℝ := centeredSlopePrefixLinearMap n c
  let z : Fin (n + 2) → ℝ := centeredProfileSectionLinearMap n c
  have hdiff (j : Fin (n + 1)) :
      z j.succ - z j.castSucc = s j := by
    change
      slopeProfilePrefix (centeredSlopePrefixLinearMap n c) j.succ -
          slopeProfilePrefix (centeredSlopePrefixLinearMap n c) j.castSucc =
        centeredSlopePrefixLinearMap n c j
    exact slopeProfilePrefix_succ_sub
      (centeredSlopePrefixLinearMap n c) j
  calc
    (∑ r, c r * (finiteDirichletGreenMatrix n).mulVec c r) =
        ∑ r : Fin n,
          (s r.succ - s r.castSucc) * z r.succ.castSucc := by
      apply Finset.sum_congr rfl
      intro r _
      rw [finiteDirichletGreenMatrix_mulVec]
      change c r * z r.succ.castSucc =
        (s r.succ - s r.castSucc) * z r.succ.castSucc
      rw [show s r.succ - s r.castSucc = c r by
        exact finiteSlopeDifference_centeredSlopePrefix_apply n c r]
    _ = -(∑ j : Fin (n + 1),
          s j * (z j.succ - z j.castSucc)) -
          s 0 * z 0 +
          s (Fin.last n) * z (Fin.last (n + 1)) :=
      finiteSlopeProfile_summation_by_parts n s z
    _ = -(∑ j, (centeredSlopePrefixLinearMap n c j) ^ 2) := by
      simp_rw [hdiff]
      simp only [z, centeredProfileSection_zero,
        centeredProfileSection_last, mul_zero, sub_zero, add_zero]
      simp only [s, pow_two]

/-- The finite Dirichlet Green quadratic form is nonpositive. -/
theorem finiteDirichletGreenMatrix_quadraticForm_nonpos
    (n : ℕ) (c : Fin n → ℝ) :
    (∑ r, c r * (finiteDirichletGreenMatrix n).mulVec c r) ≤ 0 := by
  rw [finiteDirichletGreenMatrix_quadraticForm_eq_neg_slopeEnergy]
  exact neg_nonpos.mpr (Finset.sum_nonneg fun j _ => sq_nonneg _)

/-- The finite Dirichlet Green quadratic form vanishes only at zero. -/
theorem finiteDirichletGreenMatrix_quadraticForm_eq_zero_iff
    (n : ℕ) (c : Fin n → ℝ) :
    (∑ r, c r * (finiteDirichletGreenMatrix n).mulVec c r) = 0 ↔
      c = 0 := by
  rw [finiteDirichletGreenMatrix_quadraticForm_eq_neg_slopeEnergy]
  constructor
  · intro h
    have hsum :
        (∑ j, (centeredSlopePrefixLinearMap n c j) ^ 2) = 0 :=
      neg_eq_zero.mp h
    have hsq :
        ∀ j ∈ Finset.univ,
          (centeredSlopePrefixLinearMap n c j) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg
          (centeredSlopePrefixLinearMap n c j))).mp hsum
    have hslope :
        ∀ j, centeredSlopePrefixLinearMap n c j = 0 := by
      intro j
      exact sq_eq_zero_iff.mp (hsq j (Finset.mem_univ j))
    funext r
    rw [← finiteSlopeDifference_centeredSlopePrefix_apply n c r]
    change centeredSlopePrefixLinearMap n c r.succ -
        centeredSlopePrefixLinearMap n c r.castSucc = 0
    rw [hslope, hslope]
    ring
  · intro hc
    subst c
    rw [(centeredSlopePrefixLinearMap n).map_zero]
    simp

end

end RiemannResearch.RH.PrimeGapCurvature
