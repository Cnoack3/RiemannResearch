/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QShiftedReciprocal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Finite-head inversion of the reciprocal multiplier

Source: user-provided Reciprocal_Density_CRT_Nyman_Beurling_2026-11-08.pdf,
Sections 8.2--8.3. These bounds are only on finite physical heads;
no bounded inverse on the complete Hilbert space is claimed.
-/

noncomputable section
open scoped BigOperators Topology
namespace RiemannResearch.RH.QReciprocalFiniteHead
open ZetaTwoHilbert QFiniteSupportDualCriterion QShiftedReciprocal

/-- The head inverse costs exactly its largest reciprocal denominator.
No inverse bound on the complete space is asserted. -/
theorem finiteHead_norm_sq_le_reciprocal (N : ℕ) (f : QHilbert) :
    ‖finiteHead N f‖ ^ 2 ≤ ((N : ℝ) + 1) ^ 2 * ‖B f‖ ^ 2 := by
  rw [qNorm_sq, qNorm_sq, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (qCoordinate_square_summable _)
    ((qCoordinate_square_summable _).mul_left _)
  intro n
  by_cases hn : n < N
  · rw [finiteHead_apply_of_lt N f n hn, B_apply]
    have hd : 0 < (n : ℝ) + 2 := by positivity
    have hdn : (n : ℝ) + 2 ≤ (N : ℝ) + 1 := by
      have hn' : n + 1 ≤ N := by omega
      have hcast : (n : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hn'
      linarith
    have hsq := pow_le_pow_left₀ hd.le hdn 2
    have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg (f n / ((n : ℝ) + 2)))
    have he : ((n : ℝ) + 2) ^ 2 * (f n / ((n : ℝ) + 2)) ^ 2 = (f n) ^ 2 := by
      field_simp [ne_of_gt hd]
    rwa [he] at hmul
  · rw [finiteHead_apply_eq_zero N f n (by omega), zero_pow (by norm_num)]
    positivity

/-- A finite-support inverse of the reciprocal multiplier. -/
def inverseFiniteHead (N : ℕ) (a : QHilbert) : QHilbert :=
  ∑ n ∈ Finset.range N, lp.single 2 n (((n : ℝ) + 2) * a n)

theorem B_single (n : ℕ) (a : ℝ) :
    B (lp.single 2 n a) = lp.single 2 n (a / ((n : ℝ) + 2)) := by
  apply lp.ext
  funext k
  by_cases hk : k = n
  · subst k
    simp [B_apply, lp.single_apply]
  · simp [B_apply, lp.single_apply, hk]

theorem B_inverseFiniteHead (N : ℕ) (a : QHilbert) :
    B (inverseFiniteHead N a) = finiteHead N a := by
  simp only [inverseFiniteHead, finiteHead, map_sum, B_single]
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  have hd : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hd]


end RiemannResearch.RH.QReciprocalFiniteHead
