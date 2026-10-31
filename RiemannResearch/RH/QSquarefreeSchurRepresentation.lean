/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeSchurCoercivity
import RiemannResearch.RH.QSquarefreeHeadPrediction
import RiemannResearch.RH.QSquarefreeShortHeadResponse
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Exact signed representation by the complete squarefree head Schur family

Every active conductor above the head cutoff is accounted for through its
actual normalized contrast with the legal anchor. No conductor or infinite
tail contribution is removed. The complete Gram inverse represents the
actual stage projection of a source supported on the head.

This is an identity, not a uniform estimate for the signed arithmetic source.
Source: SquarefreeShortHeadSchurResearch20261030.md, sections 2--5, and the
complete-squarefree partial normal equations in the October 30 prefix paper.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeSchurRepresentation
open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeTailResponse
open QFiniteSupportDualCriterion QDivisorHeadCoercivity QSquarefreeSchurCoercivity
open RiemannResearch.Analysis.FiniteGramCoercivity
open RiemannResearch.Analysis.FiniteHilbertGram

/-- The Schur normal equations and the head-null orthogonality together
test every actual stage direction, including all high composite conductors. -/
theorem schur_normal_implies_stage_orthogonal (N H d0 : ℕ) (hH : 1 ≤ H)
    (hanchor : H < d0) (hd0N : d0 ≤ N + 1) (hsf : Squarefree d0)
    (f : QHilbert) (hf : f ∈ (tailStage N H)ᗮ)
    (hn : ∀ i, inner ℝ (squarefreeSchurFamily N H d0 i) f = 0) :
    f ∈ (stage N)ᗮ := by
  have hraw : ∀ i, inner ℝ (squarefreeHeadFamily H d0 i) f = 0 := by
    intro i
    have hp := Submodule.inner_right_of_mem_orthogonal
      ((tailStage N H).starProjection_apply_mem (squarefreeHeadFamily H d0 i)) hf
    have h := hn i
    change inner ℝ (squarefreeHeadFamily H d0 i -
      (tailStage N H).starProjection (squarefreeHeadFamily H d0 i)) f = 0 at h
    simpa only [inner_sub_left, hp, sub_zero] using h
  have ha := hraw none
  change inner ℝ ((d0 : ℝ) • qResidue d0) f = 0 at ha
  rw [real_inner_smul_left] at ha
  have hd0R : (d0 : ℝ) ≠ 0 := by exact_mod_cast (show d0 ≠ 0 by omega)
  have ha0 : inner ℝ (qResidue d0) f = 0 := (mul_eq_zero.mp ha).resolve_left hd0R
  have hactive : ∀ i : Fin N, inner ℝ (squarefreeAtom i.val) f = 0 := by
    intro i
    by_cases hi : Squarefree (i.val + 2)
    · rw [squarefreeAtom, if_pos hi]
      have hdR : ((i.val + 2 : ℕ) : ℝ) ≠ 0 := by positivity
      by_cases hlow : i.val + 2 ≤ H
      · have hd : i.val + 2 ∈ lowConductors H :=
          (mem_lowConductors H (i.val + 2)).mpr ⟨⟨by omega, hlow⟩, hi⟩
        have h := hraw (some ⟨i.val + 2, hd⟩)
        change inner ℝ (((i.val + 2 : ℕ) : ℝ) • qResidue (i.val + 2) -
          (d0 : ℝ) • qResidue d0) f = 0 at h
        simp only [inner_sub_left, real_inner_smul_left, ha0, mul_zero, sub_zero] at h
        exact (mul_eq_zero.mp h).resolve_left hdR
      · let j : Fin N := ⟨d0 - 2, by omega⟩
        have hj : j.val + 2 = d0 := by dsimp [j]; omega
        have ht := normalized_contrast_mem_tailStage N H i j hi
          (by simpa only [hj] using hsf) (by omega)
          (by simpa only [hj] using hanchor)
        have h := Submodule.inner_right_of_mem_orthogonal ht hf
        simp only [hj, inner_sub_left, real_inner_smul_left, ha0, mul_zero, sub_zero] at h
        exact (mul_eq_zero.mp h).resolve_left hdR
    · simp only [squarefreeAtom, if_neg hi, inner_zero_left]
  apply ((stage N).mem_orthogonal f).mpr
  intro x hx
  change x ∈ Submodule.span ℝ
    (Set.range (fun i : Fin N => squarefreeAtom i.val)) at hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hactive i
  | zero => simp
  | add x y hx hy ihx ihy => rw [inner_add_left, ihx, ihy, add_zero]
  | smul c x hx ih => rw [real_inner_smul_left, ih, mul_zero]

/-- Exact actual-stage projection for every source orthogonal to the full
head-null legal subspace. Independence is supplied by proved coercivity. -/
theorem stageProjection_eq_schur_inverseCoeff (N H d0 : ℕ) (hH : 1 ≤ H)
    (hanchor : H < d0) (hd0N : d0 ≤ N + 1) (hsf : Squarefree d0)
    (f : QHilbert) (hf : f ∈ (tailStage N H)ᗮ) :
    (stage N).starProjection f =
      Fintype.linearCombination ℝ (squarefreeSchurFamily N H d0)
        (inverseCoeff (squarefreeSchurFamily_linearIndependent N H d0 hH hanchor) f) := by
  let v := squarefreeSchurFamily N H d0
  let hv := squarefreeSchurFamily_linearIndependent N H d0 hH hanchor
  let c := inverseCoeff hv f
  let p := Fintype.linearCombination ℝ v c
  have hp : p ∈ stage N ⊓ (tailStage N H)ᗮ := by
    change (∑ i, c i • v i) ∈ stage N ⊓ (tailStage N H)ᗮ
    apply (stage N ⊓ (tailStage N H)ᗮ).sum_mem
    intro i hi
    exact (stage N ⊓ (tailStage N H)ᗮ).smul_mem _
      (squarefreeSchurFamily_legal N H d0 hH hanchor hd0N hsf i)
  have hr := schur_normal_implies_stage_orthogonal N H d0 hH hanchor hd0N hsf
    (f - p) (((tailStage N H)ᗮ).sub_mem hf hp.2) (by
      intro i
      change inner ℝ (v i) (f - Fintype.linearCombination ℝ v (inverseCoeff hv f)) = 0
      rw [inner_sub_right, inverseCoeff_normal]
      simp only [cross, sub_self])
  have hz := (stage N).starProjection_apply_eq_zero_iff.mpr hr
  rw [map_sub, Submodule.starProjection_eq_self_iff.mpr hp.1] at hz
  exact sub_eq_zero.mp hz

/-- The concrete Schur family spans the entire actual head response space. -/
theorem schur_span_eq (N H d0 : ℕ) (hH : 1 ≤ H)
    (hanchor : H < d0) (hd0N : d0 ≤ N + 1) (hsf : Squarefree d0) :
    Submodule.span ℝ (Set.range (squarefreeSchurFamily N H d0)) =
      stage N ⊓ (tailStage N H)ᗮ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact squarefreeSchurFamily_legal N H d0 hH hanchor hd0N hsf i
  · intro f hf
    have he := stageProjection_eq_schur_inverseCoeff N H d0 hH hanchor hd0N hsf f hf.2
    rw [Submodule.starProjection_eq_self_iff.mpr hf.1] at he
    rw [he, Fintype.linearCombination_apply]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem schur_span_eq_headKernelSpace (N H d0 : ℕ) (hH : 1 ≤ H)
    (hanchor : H < d0) (hd0N : d0 ≤ N + 1) (hsf : Squarefree d0) :
    Submodule.span ℝ (Set.range (squarefreeSchurFamily N H d0)) =
      QSquarefreeHeadPrediction.headKernelSpace N H := by
  rw [schur_span_eq N H d0 hH hanchor hd0N hsf,
    QSquarefreeHeadPrediction.headKernelSpace_eq]

theorem finiteHead_mem_tailStage_orthogonal (N H : ℕ) (f : QHilbert) :
    finiteHead H f ∈ (tailStage N H)ᗮ := by
  apply ((tailStage N H).mem_orthogonal _).mpr
  intro t ht
  rw [inner_finiteHead_eq_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [ht.2 i (Finset.mem_range.mp hi), mul_zero]

/-- On a physical head source, the screened moments equal the original
anchored moments exactly; no signed source term is discarded. -/
theorem cross_finiteHead_eq (N H d0 : ℕ) (f : QHilbert) :
    cross (squarefreeSchurFamily N H d0) (finiteHead H f) =
      cross (squarefreeHeadFamily H d0) (finiteHead H f) := by
  funext i
  have hp := Submodule.inner_right_of_mem_orthogonal
    ((tailStage N H).starProjection_apply_mem (squarefreeHeadFamily H d0 i))
    (finiteHead_mem_tailStage_orthogonal N H f)
  change inner ℝ (squarefreeHeadFamily H d0 i -
    (tailStage N H).starProjection (squarefreeHeadFamily H d0 i)) (finiteHead H f) = _
  rw [inner_sub_left, hp, sub_zero]
  rfl

/-- Full inverse-Gram representation of the actual projected short-head
source, with its original signed anchored moments. -/
theorem stageProjection_finiteHead_eq_schur_inverseGram (N H d0 : ℕ)
    (hH : 1 ≤ H) (hanchor : H < d0) (hd0N : d0 ≤ N + 1) (hsf : Squarefree d0)
    (f : QHilbert) :
    (stage N).starProjection (finiteHead H f) =
      Fintype.linearCombination ℝ (squarefreeSchurFamily N H d0)
        ((gramMatrix (squarefreeSchurFamily N H d0))⁻¹.mulVec
          (cross (squarefreeHeadFamily H d0) (finiteHead H f))) := by
  rw [stageProjection_eq_schur_inverseCoeff N H d0 hH hanchor hd0N hsf _
    (finiteHead_mem_tailStage_orthogonal N H f), inverseCoeff_eq_inv_mulVec,
    cross_finiteHead_eq]

/-- Literal signed physical response. This equality does not assume any
adjacent-range cancellation or any uniform estimate on the source vector. -/
theorem physical_finiteHead_response_eq (N H d0 : ℕ)
    (hH : 1 ≤ H) (hanchor : H < d0) (hd0N : d0 ≤ N + 1) (hsf : Squarefree d0)
    (f : QHilbert) (n : ℕ) :
    qSequence ((stage N).starProjection (finiteHead H f)) n =
      ∑ i, ((gramMatrix (squarefreeSchurFamily N H d0))⁻¹.mulVec
        (cross (squarefreeHeadFamily H d0) (finiteHead H f))) i *
          qSequence (squarefreeSchurFamily N H d0 i) n := by
  rw [stageProjection_finiteHead_eq_schur_inverseGram N H d0 hH hanchor hd0N hsf,
    Fintype.linearCombination_apply]
  change qSequenceLinear (∑ i, _ • squarefreeSchurFamily N H d0 i) n = _
  rw [map_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  rfl

/-- The actual canonical signed short-head response, in the complete
squarefree CRT dictionary and with the literal full-Q Schur inverse. -/
theorem shortHead_response_eq_schur_inverseGram (N H d0 n : ℕ)
    (hH : 1 ≤ H) (hanchor : H < d0) (hd0N : d0 ≤ N + 1) (hsf : Squarefree d0) :
    QSquarefreeShortHeadResponse.response N H n =
      ∑ i, ((gramMatrix (squarefreeSchurFamily N H d0))⁻¹.mulVec
        (cross (squarefreeHeadFamily H d0) (QSquarefreeShortHeadResponse.source N H n))) i *
          qSequence (squarefreeSchurFamily N H d0 i) n := by
  rw [QSquarefreeShortHeadResponse.response_eq_projected_source]
  simpa only [QSquarefreeShortHeadResponse.source] using
    physical_finiteHead_response_eq N H d0 hH hanchor hd0N hsf
      (QShiftedReciprocal.B (residual N) - (1 / ((n : ℝ) + 1)) • residual N) n

/-- A finite source/evaluation estimate after the exact signed identity.
Its Schur constant is uniform in N; the arithmetic source and evaluation
vectors remain actual quantities to be controlled in the RH criterion. -/
theorem shortHead_response_sq_le_source_evaluation (N H d0 n : ℕ)
    (hH : 1 ≤ H) (hanchor : H < d0) (hd0N : d0 ≤ N + 1) (hsf : Squarefree d0) :
    QSquarefreeShortHeadResponse.response N H n ^ 2 ≤
      coercivityConstant H ^ 2 *
        (∑ i, (qSequence (squarefreeSchurFamily N H d0 i) n) ^ 2) *
        (∑ i, (cross (squarefreeHeadFamily H d0)
          (QSquarefreeShortHeadResponse.source N H n) i) ^ 2) := by
  let v := squarefreeSchurFamily N H d0
  let b := cross (squarefreeHeadFamily H d0) (QSquarefreeShortHeadResponse.source N H n)
  let c := (gramMatrix v)⁻¹.mulVec b
  let e := fun i => qSequence (v i) n
  have hv := squarefreeSchurFamily_linearIndependent N H d0 hH hanchor
  have hc : (∑ i, (c i) ^ 2) ≤ coercivityConstant H ^ 2 * ∑ i, (b i) ^ 2 := by
    dsimp only [c]
    rw [gramMatrix_inverseSource hv]
    exact inverseSource_sq_sum_le hv (coercivityConstant H) (coercivityConstant_pos H hH)
      (QHeadGramCoercivity.screened_head_coercivity N H (squarefreeHeadFamily H d0)
        (coercivityConstant H) (coercivityConstant_pos H hH).le
        (squarefreeHeadFamily_coercivity H d0 hH hanchor)) b
  have he : 0 ≤ ∑ i, (e i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c e
  rw [shortHead_response_eq_schur_inverseGram N H d0 n hH hanchor hd0N hsf]
  change (∑ i, c i * e i) ^ 2 ≤
    coercivityConstant H ^ 2 * (∑ i, (e i) ^ 2) * ∑ i, (b i) ^ 2
  calc
    _ ≤ (∑ i, (c i) ^ 2) * ∑ i, (e i) ^ 2 := hcs
    _ ≤ (coercivityConstant H ^ 2 * ∑ i, (b i) ^ 2) * ∑ i, (e i) ^ 2 :=
      mul_le_mul_of_nonneg_right hc he
    _ = _ := by ring

end RiemannResearch.RH.QSquarefreeSchurRepresentation
