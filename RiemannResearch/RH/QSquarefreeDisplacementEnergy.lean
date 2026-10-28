/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QShiftedReciprocalBounds
import RiemannResearch.RH.QSquarefreeBoundary
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.QDivisibilityDensity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
/-!
# Arithmetic energy gap for the Q/Pareto squarefree displacement

Source: the user's two-residual measure-change handoff, resumed 28 October 2026,
and the checked four-site functional in QSquarefreeBoundary. The proof strategy
combines that arithmetic relation with an exact parameterized energy identity.

Both the limiting residual and the displacement satisfy the four-site relation.
It lowers the reciprocal quadratic-form bound from 1/2 to 89/180, giving the
unconditional displacement coefficient 65520/7921 instead of 8. All remainder
terms are retained. These Hilbert energy estimates do not establish physical
boundedness, polylogarithmic growth, or vanishing of the residual.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeDisplacementEnergy
open ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal
open QSquarefreeBoundary QSquarefreeDisplacementRigidity
open QSquarefreeResidualTail ZetaTwoOptimizerStage
/-- The first omitted squarefree coefficient excludes concentration at site one. -/
theorem B_inner_le_four_site_coordinates (f : QHilbert)
    (hfour : f 0 - 2 * f 1 - 3 * f 2 + 4 * f 3 = 0) :
    inner ℝ f (B f) ≤ (89 / 180 : ℝ) * ‖f‖ ^ 2 := by
  have hs := qCoordinate_square_summable f
  have hhead := Summable.sum_le_tsum (Finset.range 4)
    (fun n _ => sq_nonneg (f n)) hs
  norm_num [Finset.sum_range_succ] at hhead
  rw [← qNorm_sq f] at hhead
  have hf0 : f 0 = 2 * f 1 + 3 * f 2 - 4 * f 3 := by linarith
  have hcs : (f 0) ^ 2 ≤ 29 * ((f 1) ^ 2 + (f 2) ^ 2 + (f 3) ^ 2) := by
    rw [hf0]
    nlinarith [sq_nonneg (3 * f 1 - 2 * f 2),
      sq_nonneg (4 * f 1 + 2 * f 3), sq_nonneg (4 * f 2 + 3 * f 3)]
  have h0 : 30 * (f 0) ^ 2 ≤ 29 * ‖f‖ ^ 2 := by nlinarith
  have hsB : Summable (fun n : ℕ => (f n) ^ 2 / ((n : ℝ) + 2)) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) _ hs
    intro n
    exact div_le_self (sq_nonneg _) (by
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith)
  have hst : Summable (fun n : ℕ => (f (n + 1)) ^ 2) :=
    (summable_nat_add_iff 1).mpr hs
  have hsBt : Summable (fun n : ℕ => (f (n + 1)) ^ 2 / (((n + 1 : ℕ) : ℝ) + 2)) :=
    (summable_nat_add_iff 1).mpr hsB
  have ht : (∑' n : ℕ, (f (n + 1)) ^ 2 / (((n + 1 : ℕ) : ℝ) + 2)) ≤
      (1 / 3 : ℝ) * ∑' n : ℕ, (f (n + 1)) ^ 2 := by
    rw [← tsum_mul_left]
    apply Summable.tsum_le_tsum _ hsBt (hst.mul_left (1 / 3 : ℝ))
    intro n
    calc
      _ ≤ (f (n + 1)) ^ 2 / 3 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num)
          (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n])
      _ = _ := by ring
  have hsplit := hs.tsum_eq_zero_add
  have hBsplit := hsB.tsum_eq_zero_add
  rw [← qNorm_sq f] at hsplit
  rw [← B_inner_tsum f] at hBsplit
  norm_num only [Nat.cast_zero, zero_add] at hBsplit
  nlinarith

/-- The physical four-site relation in the normalized real l2 coordinates. -/
theorem fourSite_coordinates {f : QHilbert} (hf : fourSiteFunctional f = 0) :
    f 0 - 2 * f 1 - 3 * f 2 + 4 * f 3 = 0 := by
  have hs (n : ℕ) : qSequence f (n + 1) =
      Real.sqrt zetaTwo * ((n + 1 : ℕ) : ℝ) * f n := by
    rw [qSequence_succ]
    apply (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos n)))).mpr
    have hw : (Real.sqrt (qWeight n) * Real.sqrt zetaTwo) *
        ((n + 1 : ℕ) : ℝ) = 1 := by
      rw [QDivisibilityDensity.sqrt_qWeight_mul_sqrt_zetaTwo]
      field_simp
    calc
      f n = f n * ((Real.sqrt (qWeight n) * Real.sqrt zetaTwo) *
        ((n + 1 : ℕ) : ℝ)) := by rw [hw, mul_one]
      _ = _ := by ring
  rw [fourSiteFunctional_apply, hs 3, hs 2, hs 1, hs 0] at hf
  norm_num at hf
  have he : Real.sqrt zetaTwo * (f 0 - 2 * f 1 - 3 * f 2 + 4 * f 3) = 0 := by
    nlinarith [hf]
  exact (mul_eq_zero.mp he).resolve_left (ne_of_gt (Real.sqrt_pos.mpr zetaTwo_pos))

theorem B_inner_le_four_site {f : QHilbert} (hf : fourSiteFunctional f = 0) :
    inner ℝ f (B f) ≤ (89 / 180 : ℝ) * ‖f‖ ^ 2 :=
  B_inner_le_four_site_coordinates f (fourSite_coordinates hf)

theorem residual_fourSite : fourSiteFunctional limitingResidual = 0 := by
  change fourSiteFunctional (qOne - closure.starProjection qOne) = 0
  rw [map_sub, fourSiteFunctional_qOne,
    fourSiteFunctional_zero_on_closure (closure.starProjection_apply_mem qOne), sub_self]

theorem displacement_fourSite : fourSiteFunctional displacement = 0 :=
  fourSiteFunctional_zero_on_closure displacement_mem

theorem residual_displacement_orthogonal : inner ℝ displacement limitingResidual = 0 :=
  Submodule.inner_right_of_mem_orthogonal displacement_mem
    limitingResidual_mem_squarefree_orthogonal

theorem displacement_normal :
    inner ℝ displacement (B (limitingResidual + displacement)) = ‖displacement‖ ^ 2 := by
  have h := Submodule.inner_right_of_mem_orthogonal displacement_mem witness_mem_orthogonal
  rw [witness, inner_sub_right, real_inner_self_eq_norm_sq,
    pResidual_eq_residual_add_displacement] at h
  exact sub_eq_zero.mp h

/-- Exact arithmetic refinement, retaining both nonnegative remainder terms. -/
theorem arithmetic_displacement_energy_exact :
    ‖limitingResidual‖ ^ 2 = (65520 / 7921 : ℝ) * ‖displacement‖ ^ 2 +
      (180 / 89 : ℝ) * inner ℝ
        (limitingResidual - (182 / 89 : ℝ) • displacement)
        (B (limitingResidual - (182 / 89 : ℝ) • displacement)) +
      (‖limitingResidual + (360 / 89 : ℝ) • displacement‖ ^ 2 -
        (180 / 89 : ℝ) * inner ℝ
          (limitingResidual + (360 / 89 : ℝ) • displacement)
          (B (limitingResidual + (360 / 89 : ℝ) • displacement))) := by
  have h := displacement_energy_remainder_param limitingResidual displacement
    (360 / 89 : ℝ) residual_displacement_orthogonal displacement_normal
  norm_num at h
  simpa only [neg_smul, ← sub_eq_add_neg, map_add, map_sub, map_smul] using h

theorem arithmetic_displacement_energy_bound :
    (65520 / 7921 : ℝ) * ‖displacement‖ ^ 2 ≤ ‖limitingResidual‖ ^ 2 := by
  have hf : fourSiteFunctional
      (limitingResidual + (360 / 89 : ℝ) • displacement) = 0 := by
    simp only [map_add, map_smul, residual_fourSite, displacement_fourSite,
      smul_zero, add_zero]
  have hu := B_inner_le_four_site hf
  have hp := B_positive (limitingResidual - (182 / 89 : ℝ) • displacement)
  have he := arithmetic_displacement_energy_exact
  linarith


/-- The improved arithmetic gap is strictly positive on the nonzero-residual branch. -/
theorem arithmetic_displacement_energy_strict (hr : limitingResidual ≠ 0) :
    (65520 / 7921 : ℝ) * ‖displacement‖ ^ 2 < ‖limitingResidual‖ ^ 2 := by
  have hne : limitingResidual - (182 / 89 : ℝ) • displacement ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    have ho := residual_displacement_orthogonal
    rw [he, inner_smul_right, real_inner_self_eq_norm_sq] at ho
    have hd : displacement = 0 := norm_eq_zero.mp
      (by nlinarith [norm_nonneg displacement])
    exact hr (by simpa [hd] using he)
  have hp : 0 < inner ℝ
      (limitingResidual - (182 / 89 : ℝ) • displacement)
      (B (limitingResidual - (182 / 89 : ℝ) • displacement)) :=
    lt_of_le_of_ne (B_positive _) (Ne.symm (fun h => hne (B_faithful _ h)))
  have hf : fourSiteFunctional
      (limitingResidual + (360 / 89 : ℝ) • displacement) = 0 := by
    simp only [map_add, map_smul, residual_fourSite, displacement_fourSite,
      smul_zero, add_zero]
  have hu := B_inner_le_four_site hf
  have he := arithmetic_displacement_energy_exact
  linarith

end RiemannResearch.RH.QSquarefreeDisplacementEnergy
