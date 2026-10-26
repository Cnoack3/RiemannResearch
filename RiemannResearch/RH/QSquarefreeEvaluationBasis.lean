/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeCorrectionKernel
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import Mathlib.Analysis.InnerProductSpace.PiL2
import RiemannResearch.RH.QSquarefreeHeadBoundary
import RiemannResearch.RH.QTriangularWeightedBessel
import RiemannResearch.LinearAlgebra.FiniteHilbertSchur
import RiemannResearch.Analysis.ResidualizedProjectionKernel
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Ordered physical evaluation innovations for actual squarefree stages

Source: the user-provided Head Boundary / Tail Response handoff, R1.
The Gram--Schmidt construction uses Mathlib's GramSchmidtOrtho API:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/GramSchmidtOrtho.html
This source supports the orthogonalization API and span identities.
Zero pivots are retained as zero vectors, never called orthonormal vectors.
The resulting exact synthesis and weighted diagonal estimate leave the
uniform arithmetic diagonal bound open.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeEvaluationBasis
open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeSmoothedProjection
open QSquarefreeCorrectionKernel QSquarefreeHeadBoundary QTriangularWeightedBessel
open RiemannResearch.LinearAlgebra
open RiemannResearch.Analysis.ResidualizedProjectionKernel
open InnerProductSpace

def evaluationFamily (N : ℕ) (i : Fin (N + 1)) : QHilbert :=
  kernel N (i.val + 1)

def innovation (N : ℕ) : Fin (N + 1) → QHilbert :=
  gramSchmidt ℝ (evaluationFamily N)

def orderedVector (N : ℕ) : Fin (N + 1) → QHilbert :=
  gramSchmidtNormed ℝ (evaluationFamily N)

theorem evaluationFamily_mem_stage (N : ℕ) (i : Fin (N + 1)) :
    evaluationFamily N i ∈ stage N :=
  (stage N).starProjection_apply_mem _

theorem span_evaluationFamily (N : ℕ) :
    Submodule.span ℝ (Set.range (evaluationFamily N)) = stage N := by
  classical
  have hle : Submodule.span ℝ (Set.range (evaluationFamily N)) ≤ stage N := by
    apply Submodule.span_le.mpr
    rintro f ⟨i, rfl⟩
    exact evaluationFamily_mem_stage N i
  apply le_antisymm hle
  intro f hf
  obtain ⟨c, hc⟩ := finiteSchur_exists_normal f (evaluationFamily N)
  let g := finiteSchurCombination (evaluationFamily N) c
  have hgspan : g ∈ Submodule.span ℝ (Set.range (evaluationFamily N)) := by
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hg : g ∈ stage N := hle hgspan
  have he : g = f := by
    apply stage_head_injective N g f hg hf
    intro k hk
    cases k with
    | zero => simp [qSequence]
    | succ k =>
      let i : Fin (N + 1) := ⟨k, by omega⟩
      have h := hc i
      change inner ℝ (kernel N (k + 1)) g =
        inner ℝ (kernel N (k + 1)) f at h
      rw [← inner_kernel_of_stage N (k + 1) g hg, ← inner_kernel_of_stage N (k + 1) f hf]
      simpa only [real_inner_comm] using h
  rwa [he] at hgspan

theorem innovation_mem_stage (N : ℕ) (i : Fin (N + 1)) :
    innovation N i ∈ stage N := by
  rw [← span_evaluationFamily, ← span_gramSchmidt ℝ (evaluationFamily N)]
  exact Submodule.subset_span ⟨i, rfl⟩

theorem orderedVector_mem_stage (N : ℕ) (i : Fin (N + 1)) :
    orderedVector N i ∈ stage N :=
  (stage N).smul_mem _ (innovation_mem_stage N i)

theorem span_orderedVector (N : ℕ) :
    Submodule.span ℝ (Set.range (orderedVector N)) = stage N := by
  rw [orderedVector, span_gramSchmidtNormed_range,
    span_gramSchmidt, span_evaluationFamily]

theorem orderedVector_orthogonal (N : ℕ) (i j : Fin (N + 1)) (hij : i ≠ j) :
    inner ℝ (orderedVector N i) (orderedVector N j) = 0 := by
  simp only [orderedVector, gramSchmidtNormed, real_inner_smul_left,
    real_inner_smul_right, gramSchmidt_orthogonal ℝ (evaluationFamily N) hij,
    mul_zero]

theorem orderedVector_norm_of_ne_zero (N : ℕ) (i : Fin (N + 1))
    (hi : orderedVector N i ≠ 0) : ‖orderedVector N i‖ = 1 :=
  gramSchmidtNormed_unit_length' hi

theorem orderedVector_norm_sq_le (N : ℕ) (i : Fin (N + 1)) :
    ‖orderedVector N i‖ ^ 2 ≤ 1 := by
  by_cases hi : orderedVector N i = 0
  · simp [hi]
  · rw [orderedVector_norm_of_ne_zero N i hi]
    norm_num

theorem orderedVector_orthonormal_nonzero (N : ℕ) :
    Orthonormal ℝ (fun i : {i : Fin (N + 1) | orderedVector N i ≠ 0} =>
      orderedVector N i) :=
  gramSchmidtNormed_orthonormal' (evaluationFamily N)

theorem orderedVector_physical_zero (N : ℕ) (i : Fin (N + 1))
    (n : ℕ) (hn : n < i.val + 1) : qSequence (orderedVector N i) n = 0 := by
  cases n with
  | zero => simp [qSequence]
  | succ n =>
    let j : Fin (N + 1) := ⟨n, by have := i.isLt; omega⟩
    have hji : j < i := by change n < i.val; omega
    rw [← inner_kernel_of_stage N (n + 1) _ (orderedVector_mem_stage N i)]
    change inner ℝ (gramSchmidtNormed ℝ (evaluationFamily N) i)
      (evaluationFamily N j) = 0
    simp only [gramSchmidtNormed, real_inner_smul_left,
      gramSchmidt_inv_triangular ℝ (evaluationFamily N) hji, mul_zero]

theorem orderedVector_onset (N : ℕ) (i : Fin (N + 1))
    (n : ℕ) (hn : n < i.val) : orderedVector N i n = 0 := by
  have h := orderedVector_physical_zero N i (n + 1) (by omega)
  rw [qSequence_succ] at h
  have hw : Real.sqrt (qWeight n) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (qWeight_pos n))
  have hz := (div_eq_iff hw).mp h
  simpa using hz

theorem stage_synthesis (N : ℕ) (f : QHilbert) (hf : f ∈ stage N) :
    f = ∑ i : Fin (N + 1), inner ℝ f (orderedVector N i) • orderedVector N i := by
  classical
  rw [← span_orderedVector N] at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨i, rfl⟩ := hf
      by_cases hi : orderedVector N i = 0
      · simp [hi]
      · symm
        rw [Finset.sum_eq_single i]
        · rw [real_inner_self_eq_norm_sq, orderedVector_norm_of_ne_zero N i hi]
          simp
        · intro j hj hji
          rw [orderedVector_orthogonal N i j hji.symm, zero_smul]
        · simp
  | zero => simp
  | add f g hf hg hif hig =>
      simp only [inner_add_left, add_smul, Finset.sum_add_distrib]
      rw [← hif, ← hig]
  | smul c f hf hif =>
      simp only [real_inner_smul_left, mul_smul, ← Finset.smul_sum]
      rw [← hif]

abbrev NonzeroIndex (N : ℕ) := {i : Fin (N + 1) | orderedVector N i ≠ 0}

noncomputable instance nonzeroIndex_fintype (N : ℕ) : Fintype (NonzeroIndex N) :=
  Fintype.ofFinite _

def nonzeroStageVector (N : ℕ) (i : NonzeroIndex N) : stage N :=
  ⟨orderedVector N i, orderedVector_mem_stage N i⟩

theorem nonzeroStageVector_orthonormal (N : ℕ) :
    Orthonormal ℝ (nonzeroStageVector N) := by
  constructor
  · intro i
    exact orderedVector_norm_of_ne_zero N i i.prop
  · intro i j hij
    exact orderedVector_orthogonal N i j (fun h => hij (Subtype.ext h))

theorem span_nonzeroStageVector (N : ℕ) :
    ⊤ ≤ Submodule.span ℝ (Set.range (nonzeroStageVector N)) := by
  classical
  intro f hf
  have he : f = ∑ i : Fin (N + 1),
      inner ℝ (f : QHilbert) (orderedVector N i) •
        (⟨orderedVector N i, orderedVector_mem_stage N i⟩ : stage N) := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using
      stage_synthesis N (f : QHilbert) f.prop
  rw [he]
  apply Submodule.sum_mem
  intro i hi
  by_cases hz : orderedVector N i = 0
  · simp [hz]
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hz⟩, rfl⟩)

def orderedBasis (N : ℕ) : OrthonormalBasis (NonzeroIndex N) ℝ (stage N) :=
  OrthonormalBasis.mk (nonzeroStageVector_orthonormal N) (span_nonzeroStageVector N)

theorem orderedBasis_apply (N : ℕ) (i : NonzeroIndex N) :
    (orderedBasis N i : QHilbert) = orderedVector N i := by
  change ((OrthonormalBasis.mk (nonzeroStageVector_orthonormal N)
    (span_nonzeroStageVector N)) i : QHilbert) = _
  rw [OrthonormalBasis.coe_mk]
  rfl

theorem movingCorrection_synthesis (N : ℕ) :
    movingCorrection N = ∑ i : Fin (N + 1),
      inner ℝ (movingCorrection N) (orderedVector N i) • orderedVector N i :=
  stage_synthesis N _ ((stage N).starProjection_apply_mem _)

theorem movingCorrection_physical_synthesis (N n : ℕ) :
    qSequence (movingCorrection N) n = ∑ i : Fin (N + 1),
      inner ℝ (movingCorrection N) (orderedVector N i) *
        qSequence (orderedVector N i) n := by
  conv_lhs => rw [movingCorrection_synthesis N]
  change qSequenceLinear _ n = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

theorem movingCorrection_weighted_coefficients (N : ℕ) :
    (∑ i : Fin (N + 1), ((i.val : ℝ) + 2) ^ 2 *
      (inner ℝ (movingCorrection N) (orderedVector N i)) ^ 2) ≤ error N :=
  movingCorrection_onset_bessel N (N + 1) (orderedVector N) id
    (orderedVector_orthogonal N) (orderedVector_norm_sq_le N)
    (orderedVector_onset N) (orderedVector_mem_stage N)

def reconstructionDiagonal (N n : ℕ) : ℝ :=
  ∑ i : Fin (N + 1),
    (qSequence (orderedVector N i) n / ((i.val : ℝ) + 2)) ^ 2

theorem reconstructionDiagonal_nonneg (N n : ℕ) : 0 ≤ reconstructionDiagonal N n :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem movingCorrection_sq_le_coefficient_diagonal (N n : ℕ) :
    (qSequence (movingCorrection N) n) ^ 2 ≤
      (∑ i : Fin (N + 1), ((i.val : ℝ) + 2) ^ 2 *
        (inner ℝ (movingCorrection N) (orderedVector N i)) ^ 2) *
      reconstructionDiagonal N n := by
  let a : Fin (N + 1) → ℝ := fun i =>
    ((i.val : ℝ) + 2) * inner ℝ (movingCorrection N) (orderedVector N i)
  let v : Fin (N + 1) → ℝ := fun i =>
    qSequence (orderedVector N i) n / ((i.val : ℝ) + 2)
  have he : qSequence (movingCorrection N) n = ∑ i, a i * v i := by
    rw [movingCorrection_physical_synthesis]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [a, v]
    have hw : (i.val : ℝ) + 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp
  have ha : (∑ i, (a i) ^ 2) ≤
      ∑ i : Fin (N + 1), ((i.val : ℝ) + 2) ^ 2 *
        (inner ℝ (movingCorrection N) (orderedVector N i)) ^ 2 := by
    simp only [a, mul_pow, le_refl]
  rw [he]
  exact (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a v).trans
    (mul_le_mul_of_nonneg_right ha (reconstructionDiagonal_nonneg N n))

/-- Sum of the residual-direction gains in the onset layers. Division by
zero is interpreted as zero, so no nonzero-residual premise is required. -/
def residualScreeningGain (N M : ℕ) : ℝ :=
  ∑ k : Fin M, onsetIncrement k * residualLayerGain (residual N) k

theorem residualScreeningGain_nonneg (N M : ℕ) : 0 ≤ residualScreeningGain N M :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (onsetIncrement_nonneg k)
    (residualLayerGain_nonneg (residual N) k))

theorem movingCorrection_weighted_coefficients_screened (N M : ℕ) (hNM : N + 1 ≤ M) :
    (∑ i : Fin (N + 1), ((i.val : ℝ) + 2) ^ 2 *
      (inner ℝ (movingCorrection N) (orderedVector N i)) ^ 2) +
      residualScreeningGain N M ≤ error N :=
  movingCorrection_onset_screened_bessel N M (orderedVector N)
    (fun i => ⟨i.val, lt_of_lt_of_le i.isLt hNM⟩)
    (orderedVector_orthogonal N) (orderedVector_norm_sq_le N)
    (orderedVector_onset N) (orderedVector_mem_stage N)

/-- The physical synthesis estimate retains the actual residual screening gain. -/
theorem movingCorrection_sq_le_screened_diagonal (N M n : ℕ) (hNM : N + 1 ≤ M) :
    (qSequence (movingCorrection N) n) ^ 2 ≤
      (error N - residualScreeningGain N M) * reconstructionDiagonal N n := by
  have h := movingCorrection_weighted_coefficients_screened N M hNM
  exact (movingCorrection_sq_le_coefficient_diagonal N n).trans
    (mul_le_mul_of_nonneg_right (by linarith) (reconstructionDiagonal_nonneg N n))

theorem movingCorrection_sq_le_diagonal (N n : ℕ) :
    (qSequence (movingCorrection N) n) ^ 2 ≤
      error N * reconstructionDiagonal N n :=
  (movingCorrection_sq_le_coefficient_diagonal N n).trans
    (mul_le_mul_of_nonneg_right (movingCorrection_weighted_coefficients N)
      (reconstructionDiagonal_nonneg N n))

end RiemannResearch.RH.QSquarefreeEvaluationBasis
