/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusTriangular
import RiemannResearch.RH.CanonicalMobiusFullEnergy
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.MobiusReciprocalNonvanishing
import RiemannResearch.RH.CRTSquarefreeConverse
import RiemannResearch.RH.ParetoNormalizedResidueHilbert
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Lean.Elab.Tactic.Omega

/-!
# Squarefree support in canonical exact-head coordinates

Source: independently developed in the user's sparse-power-cost program,
17 October 2026, from the existing full-conductor triangular exhaustion.
A nonsquarefree conductor occurs only as its own anchor in a canonical
expansion: its Mobius coefficient in every later head is zero. Finite
reciprocal-sum nonvanishing therefore forces that anchor coefficient to vanish
for a squarefree-legal vector.

This proves exact algebraic support and finite affine exhaustion, with the
same fixed conductor budget. It supplies no energy or inverse-Gram estimate.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open ArithmeticCumulative
open RiemannResearch.Analysis.ExhaustiveWalk

theorem coefficient_canonical_nonsquarefree (m Y : ℕ) (hm : 1 < m)
    (hns : ¬Squarefree m) :
    coefficientCLM m (canonicalMobiusHilbert Y) =
      if m = Y + 1 then ((Y + 1 : ℕ) : ℝ) * mobiusReciprocalSum Y else 0 := by
  have hz : ∀ d ∈ (Finset.Icc 1 Y).attach,
      (ArithmeticFunction.moebius (d : ℕ) : ℝ) *
        coefficientCLM m (normalizedResidueHilbert d (Finset.mem_Icc.mp d.property).1) = 0 := by
    intro d hd
    rw [coefficient_normalizedResidue m d hm]
    by_cases he : m = d
    · have hmu : ArithmeticFunction.moebius (d : ℕ) = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree (he ▸ hns)
      simp [he, hmu]
    · simp [he]
  simp only [canonicalMobiusHilbert, map_add, map_neg, map_sum, map_smul,
    smul_eq_mul]
  rw [Finset.sum_eq_zero hz]
  simp only [neg_zero, zero_add, coefficient_normalizedResidue m (Y + 1) hm]
  split_ifs <;> simp_all

theorem coefficient_squarefree_zero (m : ℕ) (hm : 1 < m) (hns : ¬Squarefree m)
    {x : ThresholdHilbert} (hx : x ∈ squarefreeCRTSpan) :
    coefficientCLM m x = 0 := by
  rw [squarefreeCRTSpan_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, rfl⟩ := hx
    rw [coefficient_normalizedResidue m d hm]
    have hne : m ≠ d := by
      intro he
      exact hns (he.symm ▸ d.property.2)
    simp [hne]
  | zero => exact map_zero _
  | add x y hx hy hix hiy => simp only [map_add, hix, hiy, add_zero]
  | smul c x hx hi => simp only [map_smul, hi, smul_zero]

theorem canonical_expansion_squarefree_mask
    (H M : ℕ) (hH : 0 < H) (c : Fin (M - H + 1) → ℝ)
    (x : ThresholdHilbert) (hx : x ∈ squarefreeCRTSpan)
    (he : x = ∑ j, c j • canonicalMobiusHilbert (H + j.val))
    (i : Fin (M - H + 1)) (hns : ¬Squarefree (H + i.val + 1)) :
    c i = 0 := by
  let m := H + i.val + 1
  have hm : 1 < m := by dsimp [m]; omega
  have hp (j : Fin (M - H + 1)) :
      coefficientCLM m (canonicalMobiusHilbert (H + j.val)) =
        if j = i then (m : ℝ) * mobiusReciprocalSum (H + i.val) else 0 := by
    rw [coefficient_canonical_nonsquarefree m (H + j.val) hm hns]
    by_cases hj : j = i
    · subst j
      simp [m]
    · have hne : m ≠ H + j.val + 1 := by
        intro hv
        apply hj
        apply Fin.ext
        dsimp [m] at hv
        omega
      simp [hj, hne]
  have hc := congrArg (coefficientCLM m) he
  rw [coefficient_squarefree_zero m hm hns hx, map_sum] at hc
  simp only [map_smul, smul_eq_mul, hp, mul_ite, mul_zero] at hc
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hc
  have hnon : (m : ℝ) * mobiusReciprocalSum (H + i.val) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (show m ≠ 0 by omega))
      (mobiusReciprocalSum_ne_zero (by omega))
  exact (mul_eq_zero.mp hc.symm).resolve_right hnon

theorem exists_finiteSpace_of_squarefree (H : ℕ)
    {x : ThresholdHilbert} (hx : x ∈ squarefreeCRTSpan) :
    ∃ M, H ≤ M ∧ x ∈ finiteSpace M := by
  rw [squarefreeCRTSpan_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, rfl⟩ := hx
    let M := max H d.val
    refine ⟨M, le_max_left _ _, ?_⟩
    apply Submodule.subset_span
    refine ⟨⟨d.val - 2, ?_⟩, ?_⟩
    · have := d.property.1
      have := le_max_right H d.val
      dsimp [M]
      omega
    · change residueAtom (d.val - 2) = normalizedResidueHilbert d.val _
      unfold residueAtom
      congr 1
      have := d.property.1
      omega
  | zero => exact ⟨H, le_rfl, Submodule.zero_mem _⟩
  | add x y hx hy hix hiy =>
    obtain ⟨A, hHA, hxA⟩ := hix
    obtain ⟨B, hHB, hyB⟩ := hiy
    refine ⟨max A B, hHA.trans (le_max_left _ _), ?_⟩
    exact Submodule.add_mem _
      (walkSpan_mono residueAtom id (le_max_left A B) hxA)
      (walkSpan_mono residueAtom id (le_max_right A B) hyB)
  | smul c x hx hi =>
    obtain ⟨M, hHM, hxM⟩ := hi
    exact ⟨M, hHM, Submodule.smul_mem _ c hxM⟩

theorem exists_squarefree_canonical_affine_expansion
    (H M : ℕ) (hH : 0 < H) (hHM : H ≤ M)
    (x : ThresholdHilbert) (hx : x ∈ finiteSpace M) (hsf : x ∈ squarefreeCRTSpan)
    (hh : ∀ n, 0 < n → n ≤ H → hilbertSequence x n = 1) :
    ∃ c : Fin (M - H + 1) → ℝ, (∑ i, c i) = 1 ∧
      (∀ i, ¬Squarefree (H + i.val + 1) → c i = 0) ∧
      x = ∑ i, c i • canonicalMobiusHilbert (H + i.val) := by
  obtain ⟨c, hc, he⟩ := exists_canonicalMobius_affine_expansion_of_exact_head
    H M hHM x hx hh
  exact ⟨c, hc, fun i hi => canonical_expansion_squarefree_mask H M hH c x hsf he i hi, he⟩
end RiemannResearch.RH.Pareto.CoefficientStabilization
