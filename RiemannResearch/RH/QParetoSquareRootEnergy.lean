/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoIsometricTransport
import RiemannResearch.RH.ThresholdHilbertSpace
import RiemannResearch.RH.ParetoWeights
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.QShiftedReciprocal
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Positive square-root energy and complete correction tails

Source: user-provided Isometric_Transport_Lean_Handoff_2026-11-06.md,
Sections 4--5, for the inverse multiplier and proposed positive bound.
The polarization and shared square-root correction develop that argument.
No mathematical priority claim is made.

inversePhysical is A.symm composed with the same-sequence map I.
It is physical multiplication by sqrt(Z*n/(n+1)), represented in Q.
Its square is Z*(1-R), where R remains named QShiftedReciprocal.B.
rootDefect is 1-inversePhysical/sqrt(Z). The tail estimate includes every
coordinate past the given head and imposes no legal-space invariance.
-/

noncomputable section
open scoped BigOperators Topology

namespace RiemannResearch.RH.QParetoIsometricTransport
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QShiftedReciprocal

/-- Physical inverse square-root multiplier, with input and output encoded in Q. -/
def inversePhysical : QHilbert →L[ℝ] QHilbert :=
  A.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp toParetoCLM

theorem inversePhysical_apply (f : QHilbert) (n : ℕ) :
    (inversePhysical f) n = Real.sqrt (paretoWeight n / qWeight n) * f n := by
  rw [Real.sqrt_div (paretoWeight_pos n).le]
  change Real.sqrt (paretoWeight n) * (f n / Real.sqrt (qWeight n)) = _
  ring

theorem toPareto_A_inner (f g : QHilbert) :
    inner ℝ (toPareto f) (A g) = inner ℝ f (inversePhysical g) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1
  funext n
  change g n * (Real.sqrt (paretoWeight n) * (f n / Real.sqrt (qWeight n))) =
    (Real.sqrt (paretoWeight n) * (g n / Real.sqrt (qWeight n))) * f n
  ring

theorem inversePhysical_symmetric (f g : QHilbert) :
    inner ℝ (inversePhysical f) g = inner ℝ f (inversePhysical g) :=
  toPareto_A_inner f g

theorem inversePhysical_weight_lower (n : ℕ) :
    Real.sqrt (zetaTwo / 2) ≤ Real.sqrt (paretoWeight n / qWeight n) := by
  apply Real.sqrt_le_sqrt
  rw [paretoWeight_div_qWeight]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)+2)).mpr
  nlinarith [mul_nonneg zetaTwo_pos.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

def inverseEnergy (f : QHilbert) : ℝ := inner ℝ f (inversePhysical f)

theorem inverseEnergy_lower (f : QHilbert) :
    Real.sqrt (zetaTwo / 2) * ‖f‖ ^ 2 ≤ inverseEnergy f := by
  rw [inverseEnergy, qNorm_sq, lp.inner_eq_tsum, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _
    ((qCoordinate_square_summable f).mul_left _) (lp.summable_inner f (inversePhysical f))
  intro n
  change Real.sqrt (zetaTwo / 2) * (f n)^2 ≤ (inversePhysical f) n * f n
  rw [inversePhysical_apply]
  nlinarith [mul_le_mul_of_nonneg_right (inversePhysical_weight_lower n) (sq_nonneg (f n))]

theorem inverseEnergy_upper (f : QHilbert) :
    inverseEnergy f ≤ Real.sqrt zetaTwo * ‖f‖ ^ 2 := by
  have h := real_inner_le_norm f (inversePhysical f)
  have hn : ‖inversePhysical f‖ ≤ Real.sqrt zetaTwo * ‖f‖ := toPareto_norm_le f
  unfold inverseEnergy
  nlinarith [mul_le_mul_of_nonneg_left hn (norm_nonneg f)]

theorem inverseEnergy_eq_zero_iff (f : QHilbert) :
    inverseEnergy f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have hl := inverseEnergy_lower f
    have hm : 0 < Real.sqrt (zetaTwo / 2) := Real.sqrt_pos.mpr (div_pos zetaTwo_pos (by norm_num))
    have hz : ‖f‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖f‖]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · rintro rfl
    simp [inverseEnergy]

/-- Exact identity, retaining the nonnegative trial and error energies. -/
theorem inverseEnergy_polarization (f g : QHilbert) :
    inverseEnergy f + inverseEnergy g =
      2 * inner ℝ f (inversePhysical g) + inverseEnergy (f - g) := by
  simp only [inverseEnergy, map_sub, inner_sub_left, inner_sub_right]
  rw [← inversePhysical_symmetric g f, real_inner_comm (inversePhysical g) f]
  ring

/-- Two physical inverse applications give the full metric multiplier. -/
theorem inversePhysical_square (f : QHilbert) :
    inversePhysical (inversePhysical f) = zetaTwo • (f - B f) := by
  apply Subtype.ext
  funext n
  rw [inversePhysical_apply, inversePhysical_apply]
  change Real.sqrt (paretoWeight n / qWeight n) *
      (Real.sqrt (paretoWeight n / qWeight n) * f n) =
    zetaTwo * (f n - f n / ((n : ℝ) + 2))
  rw [← mul_assoc, ← pow_two,
    Real.sq_sqrt (div_nonneg (paretoWeight_pos n).le (qWeight_pos n).le),
    paretoWeight_div_qWeight]
  have hn : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring
/-- Common square-root correction for the two crossed approximation problems. -/
def rootDefect : QHilbert →L[ℝ] QHilbert :=
  ContinuousLinearMap.id ℝ QHilbert - (Real.sqrt zetaTwo)⁻¹ • inversePhysical

theorem rootDefect_scale (f : QHilbert) :
    Real.sqrt zetaTwo • rootDefect f =
      Real.sqrt zetaTwo • f - inversePhysical f := by
  have hz : Real.sqrt zetaTwo ≠ 0 := (Real.sqrt_pos.mpr zetaTwo_pos).ne'
  simp [rootDefect, smul_sub, smul_smul, hz]

theorem rootDefect_apply (f : QHilbert) (n : ℕ) :
    (rootDefect f) n =
      (1 - Real.sqrt (((n : ℝ)+1)/((n : ℝ)+2))) * f n := by
  have hz : Real.sqrt zetaTwo ≠ 0 := (Real.sqrt_pos.mpr zetaTwo_pos).ne'
  change f n - (Real.sqrt zetaTwo)⁻¹ * (inversePhysical f) n = _
  rw [inversePhysical_apply, paretoWeight_div_qWeight,
    show zetaTwo * ((n : ℝ)+1) / ((n : ℝ)+2) =
      zetaTwo * (((n : ℝ)+1)/((n : ℝ)+2)) by ring,
    Real.sqrt_mul zetaTwo_pos.le]
  field_simp

theorem rootDefect_weight_bounds (n : ℕ) :
    0 ≤ 1 - Real.sqrt (((n : ℝ)+1)/((n : ℝ)+2)) ∧
      1 - Real.sqrt (((n : ℝ)+1)/((n : ℝ)+2)) ≤ 1/((n : ℝ)+2) := by
  have hn : (0 : ℝ) < (n : ℝ)+2 := by positivity
  have hp : 0 ≤ ((n : ℝ)+1)/((n : ℝ)+2) := by positivity
  have hu : ((n : ℝ)+1)/((n : ℝ)+2) ≤ 1 := by
    apply (div_le_one hn).mpr
    linarith
  have hs := Real.sqrt_nonneg (((n : ℝ)+1)/((n : ℝ)+2))
  have hs1 := Real.sqrt_le_one.mpr hu
  have he := Real.sq_sqrt hp
  have hx : ((n : ℝ)+1)/((n : ℝ)+2) ≤
      Real.sqrt (((n : ℝ)+1)/((n : ℝ)+2)) := by nlinarith
  have hx' := (div_le_iff₀ hn).mp hx
  exact ⟨sub_nonneg.mpr hs1, (le_div_iff₀ hn).mpr (by nlinarith)⟩

/-- Complete tail estimate: vanishing encoded coordinates below N improve the operator bound. -/
theorem rootDefect_norm_le_of_head_zero (f : QHilbert) (N : ℕ)
    (hhead : ∀ n < N, f n = 0) :
    ‖rootDefect f‖ ≤ ‖f‖ / ((N : ℝ)+2) := by
  have hN : (0 : ℝ) < (N : ℝ)+2 := by positivity
  have hs : ‖rootDefect f‖ ^ 2 ≤ (‖f‖ / ((N : ℝ)+2)) ^ 2 := by
    rw [div_pow, qNorm_sq, qNorm_sq, ← tsum_div_const]
    apply Summable.tsum_le_tsum _ (qCoordinate_square_summable (rootDefect f))
      ((qCoordinate_square_summable f).div_const _)
    intro n
    rw [rootDefect_apply]
    by_cases hn : n < N
    · simp [hhead n hn]
    · have hNn : (N : ℝ) ≤ n := by exact_mod_cast Nat.le_of_not_gt hn
      have hb := rootDefect_weight_bounds n
      have hdiv : 1/((n : ℝ)+2) ≤ 1/((N : ℝ)+2) :=
        one_div_le_one_div_of_le hN (by linarith)
      have hsq := (sq_le_sq₀ hb.1 (by positivity : (0 : ℝ) ≤ 1/((N : ℝ)+2))).mpr
        (hb.2.trans hdiv)
      have hm := mul_le_mul_of_nonneg_right hsq (sq_nonneg (f n))
      simpa only [mul_pow, div_pow, one_pow, one_div_mul_eq_div] using hm
  exact (sq_le_sq₀ (norm_nonneg _) (div_nonneg (norm_nonneg f) hN.le)).mp hs


/-- Finite-head matching controls the entire remaining square-root correction. -/
theorem rootDefect_head_trial_bound (g v z : QHilbert) (N : ℕ)
    (hhead : ∀ n < N, g n = v n) :
    ‖rootDefect g - z‖ ≤
      ‖rootDefect v - z‖ + ‖g - v‖ / ((N : ℝ)+2) := by
  have hh : ∀ n < N, (g - v) n = 0 := by
    intro n hn
    change g n - v n = 0
    exact sub_eq_zero.mpr (hhead n hn)
  have ht := rootDefect_norm_le_of_head_zero (g - v) N hh
  have he : rootDefect g - z = (rootDefect v - z) + rootDefect (g - v) := by
    rw [map_sub]
    abel
  rw [he]
  have hn := norm_add_le (rootDefect v - z) (rootDefect (g - v))
  linarith

end RiemannResearch.RH.QParetoIsometricTransport
