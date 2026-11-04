/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDivisibilityHilbertMoments
import RiemannResearch.RH.QSquarefreePrimorialCofinality
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.SquarefreeStageExhaustion
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
/-!
# Exact complete common-period error contribution

Source: elementary orthogonal decomposition against a divisibility indicator.
The indicator moments are reused from QDivisibilityHilbertMoments.
The concrete RH consumer is the primorial legal projection family.

Every residue with conductor dividing L vanishes on multiples of L.
The exact identity retains the norm-square remainder after removing the
full indicator of that progression. Its consequence is the finite bound
error >= 1/L^2; no positive limiting error is inferred.
-/
noncomputable section
namespace RiemannResearch.RH.QCommonPeriodError
open ZetaTwoHilbert QDivisibilityDensity QSquarefreePrimorialCofinality
open Pareto.SquarefreeStageExhaustion
/-- A common-period divisibility indicator annihilates the entire residue span. -/
theorem inner_divisor_zero_of_mem_span {L : ℕ} (hL : 0 < L)
    (S : Set ℕ) (hS : ∀ d ∈ S, d ∣ L) {f : QHilbert}
    (hf : f ∈ Submodule.span ℝ (qResidue '' S)) :
    inner ℝ f (qDivisor L) = 0 := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨d, hd, rfl⟩ := hx
      exact qResidue_inner_qDivisor_eq_zero d L hL (hS d hd)
  | zero => simp
  | add x y hx hy ihx ihy => rw [inner_add_left, ihx, ihy, add_zero]
  | smul c x hx ih => simp only [real_inner_smul_left, ih, mul_zero]

/-- Exact decomposition: the entire common-multiple contribution is retained. -/
theorem error_exact_of_inner_divisor_zero {L : ℕ} (hL : 0 < L)
    (f : QHilbert) (hf : inner ℝ f (qDivisor L) = 0) :
    ‖qOne - f‖ ^ 2 = 1 / (L : ℝ) ^ 2 +
      ‖qOne - f - qDivisor L‖ ^ 2 := by
  have hi : inner ℝ (qOne - f) (qDivisor L) = 1 / (L : ℝ) ^ 2 := by
    rw [inner_sub_left, qOne_inner_qDivisor L hL, hf, sub_zero]
  have h := norm_sub_sq_real (qOne - f) (qDivisor L)
  rw [hi, qDivisor_norm_sq L hL] at h
  linarith

theorem error_lower_of_mem_span {L : ℕ} (hL : 0 < L)
    (S : Set ℕ) (hS : ∀ d ∈ S, d ∣ L) {f : QHilbert}
    (hf : f ∈ Submodule.span ℝ (qResidue '' S)) :
    1 / (L : ℝ) ^ 2 ≤ ‖qOne - f‖ ^ 2 := by
  rw [error_exact_of_inner_divisor_zero hL f
    (inner_divisor_zero_of_mem_span hL S hS hf)]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem primorial_inner_divisor_zero (n : ℕ) :
    inner ℝ (primorialOptimizer n) (qDivisor (primorialPeriod n)) = 0 := by
  apply inner_divisor_zero_of_mem_span (primorialPeriod_pos n)
    {d | 1 < d ∧ d ∣ primorialPeriod n} (fun d hd => hd.2)
  have h := (primorialStage n).starProjection_apply_mem qOne
  have he : {f : QHilbert | ∃ d : ℕ,
      1 < d ∧ d ∣ primorialPeriod n ∧ f = qResidue d} =
      qResidue '' {d | 1 < d ∧ d ∣ primorialPeriod n} := by
    ext f
    constructor
    · rintro ⟨d, hd, hdiv, rfl⟩
      exact ⟨d, ⟨hd, hdiv⟩, rfl⟩
    · rintro ⟨d, ⟨hd, hdiv⟩, rfl⟩
      exact ⟨d, hd, hdiv, rfl⟩
  change primorialOptimizer n ∈ primorialStage n at h
  change primorialOptimizer n ∈ Submodule.span ℝ
    {f : QHilbert | ∃ d : ℕ, 1 < d ∧ d ∣ primorialPeriod n ∧ f = qResidue d} at h
  rwa [he] at h

theorem primorialError_exact (n : ℕ) :
    primorialError n = 1 / (primorialPeriod n : ℝ) ^ 2 +
      ‖qOne - primorialOptimizer n - qDivisor (primorialPeriod n)‖ ^ 2 :=
  error_exact_of_inner_divisor_zero (primorialPeriod_pos n)
    (primorialOptimizer n) (primorial_inner_divisor_zero n)

theorem primorialError_lower (n : ℕ) :
    1 / (primorialPeriod n : ℝ) ^ 2 ≤ primorialError n := by
  rw [primorialError_exact]
  exact le_add_of_nonneg_right (sq_nonneg _)
end RiemannResearch.RH.QCommonPeriodError
