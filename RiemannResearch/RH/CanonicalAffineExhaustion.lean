/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusTriangular
import RiemannResearch.RH.BalancedSquarefreeCrossing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Complete finite canonical affine geometry and strict charge crossings

Source: user-provided CRT and Four Improvements continuation, 6–7 October 2026.
The extensions retain complete signed identities and correction squares.


The arithmetic nonvanishing and forward affine exhaustion are supplied by
the existing verified modules. Here the converse and the exact direction
space are proved. No asymptotic residual-energy provider is assumed.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- Every combination of the later triangular directions vanishes on the
common head. Together with the existing converse this is an exact kernel
description. -/
theorem consecutiveTailSpan_head_zero (N M : ℕ) (x : ThresholdHilbert)
    (hx : x ∈ consecutiveTailSpan N M) :
    ∀ j : ℕ, 0 < j → j ≤ N → hilbertSequence x j = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hNk, hkM, rfl⟩ := hx
    intro j hj hjN
    exact consecutiveResidueHilbert_head_zero k j (hjN.trans hNk)
  | zero =>
    intro j hj hjN
    change hilbertSequenceLinear 0 j = 0
    simp
  | add x y hx hy hix hiy =>
    intro j hj hjN
    change hilbertSequenceLinear (x + y) j = 0
    simp only [map_add, Pi.add_apply]
    change hilbertSequence x j + hilbertSequence y j = 0
    rw [hix j hj hjN, hiy j hj hjN, add_zero]
  | smul a x hx hix =>
    intro j hj hjN
    change hilbertSequenceLinear (a • x) j = 0
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    change a * hilbertSequence x j = 0
    rw [hix j hj hjN, mul_zero]

/-- The canonical affine direction space is exactly the full legal head
kernel. The reciprocal charges impose no extra restriction. -/
theorem canonicalMobiusDifferenceSpan_eq_consecutiveTailSpan
    (N M : ℕ) (hNM : N ≤ M) :
    canonicalMobiusDifferenceSpan N M = consecutiveTailSpan N M := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨k, hNk, hkM, rfl⟩
    apply mem_consecutiveTailSpan_of_head_zero N M
    · exact (finiteSpace M).sub_mem
        (RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono residueAtom id hkM
          (canonicalMobiusHilbert_mem_finiteSpace k))
        (RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono residueAtom id hNM
          (canonicalMobiusHilbert_mem_finiteSpace N))
    · intro j hj hjN
      change hilbertSequenceLinear (_ - _) j = 0
      simp only [map_sub, Pi.sub_apply]
      change hilbertSequence (canonicalMobiusHilbert k) j -
        hilbertSequence (canonicalMobiusHilbert N) j = 0
      rw [canonicalMobiusHilbert_exact k j hj (hjN.trans hNk),
        canonicalMobiusHilbert_exact N j hj hjN, sub_self]
  · exact consecutiveTailSpan_le_canonicalMobiusDifferenceSpan N M

/-- Canonical combinations within a finite window have the same conductor
budget as the full legal interpolation problem. -/
theorem canonicalMobius_window_combination_mem_finiteSpace
    (N M : ℕ) (hNM : N ≤ M) (c : Fin (M - N + 1) → ℝ) :
    (∑ i : Fin (M - N + 1), c i • canonicalMobiusHilbert (N + i.val)) ∈
      finiteSpace M := by
  apply Submodule.sum_mem
  intro i hi
  apply (finiteSpace M).smul_mem
  exact RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono residueAtom id
    (by have := i.isLt; omega)
    (canonicalMobiusHilbert_mem_finiteSpace (N + i.val))

theorem canonicalMobius_window_combination_exact_head
    (N M : ℕ) (c : Fin (M - N + 1) → ℝ) (hc : (∑ i, c i) = 1) :
    ∀ j : ℕ, 0 < j → j ≤ N →
      hilbertSequence
        (∑ i : Fin (M - N + 1), c i • canonicalMobiusHilbert (N + i.val)) j = 1 := by
  intro j hj hjN
  change hilbertSequenceLinear (∑ i, c i • canonicalMobiusHilbert (N + i.val)) j = 1
  rw [map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i : Fin (M - N + 1), c i *
      hilbertSequence (canonicalMobiusHilbert (N + i.val)) j) = ∑ i, c i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [canonicalMobiusHilbert_exact (N + i.val) j hj (by omega), mul_one]
    _ = 1 := hc

/-- Exact finite equivalence: the normalized signed canonical family is the
entire legal exact-head interpolation space. The indices include every
cutoff in the window and coefficients may have either sign. -/
theorem legal_exact_head_iff_canonicalMobius_affine_expansion
    (N M : ℕ) (hNM : N ≤ M) (x : ThresholdHilbert) :
    (x ∈ finiteSpace M ∧
      ∀ j : ℕ, 0 < j → j ≤ N → hilbertSequence x j = 1) ↔
    ∃ c : Fin (M - N + 1) → ℝ, (∑ i, c i) = 1 ∧
      x = ∑ i : Fin (M - N + 1), c i • canonicalMobiusHilbert (N + i.val) := by
  constructor
  · rintro ⟨hx, hhead⟩
    exact exists_canonicalMobius_affine_expansion_of_exact_head N M hNM x hx hhead
  · rintro ⟨c, hc, rfl⟩
    exact ⟨canonicalMobius_window_combination_mem_finiteSpace N M hNM c,
      canonicalMobius_window_combination_exact_head N M c hc⟩

end RiemannResearch.RH.Pareto.CoefficientStabilization

namespace RiemannResearch.RH.Pareto.BalancedSquarefree

/-- A positive finite charge crossing is always strict: reciprocal Möbius
charges never vanish. -/
theorem crossing_product_neg (Y : ℕ) (hY : 0 < Y) (h : Crossing Y) :
    mobiusReciprocalSum Y * mobiusReciprocalSum (Y + 1) < 0 := by
  exact lt_of_le_of_ne h.2
    (mul_ne_zero (mobiusReciprocalSum_ne_zero hY)
      (mobiusReciprocalSum_ne_zero (by omega)))

theorem crossing_iff_product_neg (Y : ℕ) (hY : 0 < Y) :
    Crossing Y ↔ mobiusReciprocalSum Y * mobiusReciprocalSum (Y + 1) < 0 := by
  constructor
  · exact crossing_product_neg Y hY
  · intro h
    exact ⟨mobiusReciprocalSum_ne_zero hY, h.le⟩

/-- Both raw trial weights at a crossing are strictly positive. A canonical
crossing can never degenerate to the next raw trial. -/
theorem crossing_parameter_lt_one (Y : ℕ) (h : Crossing Y) : parameter Y < 1 := by
  have hb := crossing_bounds Y h
  apply lt_of_le_of_ne hb.2.2
  intro he
  have hparam : parameter Y = 1 := he
  have hmul := parameter_mul_moebius Y h
  rw [hparam, one_mul] at hmul
  have hden : ((Y + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hcharge : ((Y + 1 : ℕ) : ℝ) * mobiusReciprocalSum (Y + 1) =
      ((Y + 1 : ℕ) : ℝ) * mobiusReciprocalSum Y +
        (ArithmeticFunction.moebius (Y + 1) : ℝ) := by
    rw [mobiusReciprocalSum_succ, mul_add]
    field_simp
  have hnext : mobiusReciprocalSum (Y + 1) = 0 := by
    apply (mul_eq_zero.mp (show ((Y + 1 : ℕ) : ℝ) *
      mobiusReciprocalSum (Y + 1) = 0 by rw [hcharge, hmul]; ring)).resolve_left hden
  exact mobiusReciprocalSum_ne_zero (by omega) hnext

theorem crossing_strict_parameter_bounds (Y : ℕ) (h : Crossing Y) :
    0 < parameter Y ∧ parameter Y < 1 :=
  ⟨(crossing_bounds Y h).2.1, crossing_parameter_lt_one Y h⟩

end RiemannResearch.RH.Pareto.BalancedSquarefree
