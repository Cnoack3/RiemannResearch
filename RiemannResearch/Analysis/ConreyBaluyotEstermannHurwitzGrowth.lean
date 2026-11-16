/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotEstermann
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# Explicit Hurwitz-to-Estermann growth transfer

The exact finite continuation formula is the starting identity. The ensuing
norm bound is uniform over all numerator classes at fixed positive modulus,
including nonunits. Polynomial bounds of possibly different degrees on the
two Hurwitz factors produce a bound of their summed degree, with an explicit
constant and arbitrary complex shifts.

The transfer below retains its explicit growth hypotheses. Actual quadratic
Hurwitz bounds are supplied in HurwitzEulerMaclaurin; the fixed-parameter
Estermann and contour specializations are in ConreyBaluyotEstermannActualGrowth.

Source: Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
equation (3.1.7), pp. 95–96 (finite Hurwitz identity):
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320
The actual provider uses the corrected Euler--Maclaurin expansion
https://dlmf.nist.gov/25.11.E6, proved separately in HurwitzEulerMaclaurin.
-/

open Complex Set
open scoped BigOperators
noncomputable section
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- Explicit finite Hurwitz bound, uniform over every numerator class. -/
theorem norm_estermann_le_hurwitz_sum_product {K : ℕ} [NeZero K]
    (h : ZMod K) (u v : ℂ) :
    ‖estermann h u v‖ ≤ (K : ℝ) ^ (-u.re - v.re) *
      ((∑ a : ZMod K, ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) u‖) *
        (∑ b : ZMod K, ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle b) v‖)) := by
  classical
  have hK : 0 < (K : ℝ) := Nat.cast_pos.mpr (NeZero.pos K)
  have hp : ‖(K : ℂ) ^ (-u - v)‖ = (K : ℝ) ^ (-u.re - v.re) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hK (-u - v)
  rw [estermann_eq_sum_hurwitzZeta, norm_mul, hp]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hK.le _)
  calc
    _ ≤ ∑ a : ZMod K, ‖∑ b : ZMod K, ZMod.stdAddChar (h * a * b) *
        (HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) u *
          HurwitzZeta.hurwitzZeta (ZMod.toAddCircle b) v)‖ := norm_sum_le _ _
    _ ≤ ∑ a : ZMod K, ∑ b : ZMod K, ‖ZMod.stdAddChar (h * a * b) *
        (HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) u *
          HurwitzZeta.hurwitzZeta (ZMod.toAddCircle b) v)‖ := by
      exact Finset.sum_le_sum (fun a _ => norm_sum_le _ _)
    _ = _ := by
      simp only [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul,
        Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

/-- Conditional transfer of arbitrary polynomial Hurwitz estimates to Estermann.
The explicit constant is uniform over all h modulo the fixed positive K.
The shifts may be complex, and the two growth degrees may differ. -/
theorem norm_estermann_shifted_le_of_hurwitz_polynomial_bounds
    {K : ℕ} [NeZero K] (h : ZMod K) (α β : ℂ) {a b T₀ : ℝ}
    (n m : ℕ) (C D : ZMod K → ℝ)
    (hleft : ∀ j, ∀ r ∈ Icc a b, ∀ t : ℝ, T₀ ≤ |t| →
      ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) ((r : ℂ) + t * I + α)‖ ≤ C j * |t| ^ n)
    (hright : ∀ j, ∀ r ∈ Icc a b, ∀ t : ℝ, T₀ ≤ |t| →
      ‖HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) ((r : ℂ) + t * I + β)‖ ≤ D j * |t| ^ m) :
    ∀ r ∈ Icc a b, ∀ t : ℝ, T₀ ≤ |t| →
      ‖estermann h ((r : ℂ) + t * I + α) ((r : ℂ) + t * I + β)‖ ≤
        ((K : ℝ) ^ (-2 * a - α.re - β.re) * (∑ j, C j) * (∑ j, D j)) * |t| ^ (n + m) := by
  classical
  intro r hr t ht
  have hK : (1 : ℝ) ≤ K := by exact_mod_cast NeZero.pos K
  have hpow : (K : ℝ) ^ (-2 * r - α.re - β.re) ≤ (K : ℝ) ^ (-2 * a - α.re - β.re) :=
    Real.rpow_le_rpow_of_exponent_le hK (by linarith [hr.1])
  have hL := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hleft j r hr t ht)
  have hR := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hright j r hr t ht)
  have hE := norm_estermann_le_hurwitz_sum_product h
    ((r : ℂ) + t * I + α) ((r : ℂ) + t * I + β)
  have hExp : -((r : ℂ) + t * I + α).re - ((r : ℂ) + t * I + β).re =
      -2 * r - α.re - β.re := by simp [Complex.mul_re]; ring
  rw [hExp] at hE
  refine hE.trans ?_
  calc
    _ ≤ (K : ℝ) ^ (-2 * a - α.re - β.re) *
        ((∑ j, C j * |t| ^ n) * (∑ j, D j * |t| ^ m)) := by
      apply mul_le_mul hpow ?_ (by positivity) (by positivity)
      exact mul_le_mul hL hR (by positivity)
        ((Finset.sum_nonneg (fun j _ => norm_nonneg _)).trans hL)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, pow_add]
      ring

end RiemannResearch.Analysis.ConreyBaluyot
