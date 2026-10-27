import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.Analysis.SingleDirectionResponseDifference
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import Lean.Elab.Tactic.Omega

/-!
# Canonical squarefree innovations and exact response updates
Source: the user's SquarefreeMomentBudgetResearch20261027.md.
The original natural indexing is retained, including every zero innovation.
-/
noncomputable section
namespace RiemannResearch.RH.QCanonicalInnovation
open ZetaTwoHilbert ZetaTwoOptimizerStage InnerProductSpace
open RiemannResearch.Analysis.ExhaustiveWalk

def direction : ℕ → QHilbert := gramSchmidtNormed ℝ squarefreeAtom

theorem span_direction_prefix (N : ℕ) :
    Submodule.span ℝ (direction '' Set.Iio N) = stage N := by
  rw [direction, span_gramSchmidtNormed, span_gramSchmidt_Iio]
  change Submodule.span ℝ (squarefreeAtom '' Set.Iio N) =
    Submodule.span ℝ (Set.range (fun i : Fin N => squarefreeAtom i))
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.isLt, rfl⟩

theorem direction_mem_succ (N : ℕ) : direction N ∈ stage (N + 1) := by
  rw [← span_direction_prefix]
  exact Submodule.subset_span ⟨N, Nat.lt_succ_self N, rfl⟩

theorem direction_orthogonal (i j : ℕ) (hij : i ≠ j) :
    inner ℝ (direction i) (direction j) = 0 := by
  simp only [direction, gramSchmidtNormed, real_inner_smul_left,
    real_inner_smul_right, gramSchmidt_orthogonal ℝ squarefreeAtom hij,
    mul_zero]

theorem direction_mem_orthogonal (N : ℕ) : direction N ∈ (stage N)ᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  intro x hx
  rw [← span_direction_prefix] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact direction_orthogonal i N (Nat.ne_of_lt hi)
  | zero => simp
  | add x y hx hy hix hiy => simp only [inner_add_left, hix, hiy, add_zero]
  | smul c x hx hix => simp only [real_inner_smul_left, hix, mul_zero]

theorem direction_norm (N : ℕ) (hN : direction N ≠ 0) : ‖direction N‖ = 1 :=
  gramSchmidtNormed_unit_length' hN

abbrev Active := {N : ℕ | direction N ≠ 0}

theorem active_orthonormal : Orthonormal ℝ (fun i : Active => direction i) :=
  gramSchmidtNormed_orthonormal' squarefreeAtom

theorem stage_succ (N : ℕ) :
    stage (N + 1) = stage N ⊔ Submodule.span ℝ ({direction N} : Set QHilbert) := by
  apply le_antisymm
  · rw [← span_direction_prefix]
    apply Submodule.span_le.mpr
    rintro x ⟨i, hi, rfl⟩
    change i < N + 1 at hi
    by_cases hiN : i < N
    · apply (show stage N ≤ stage N ⊔
          Submodule.span ℝ ({direction N} : Set QHilbert) from le_sup_left)
      rw [← span_direction_prefix]
      exact Submodule.subset_span ⟨i, hiN, rfl⟩
    · have he : i = N := by omega
      subst i
      apply (show Submodule.span ℝ ({direction N} : Set QHilbert) ≤
          stage N ⊔ Submodule.span ℝ ({direction N} : Set QHilbert) from le_sup_right)
      exact Submodule.subset_span (by simp)
  · apply sup_le
    · exact walkSpan_mono squarefreeAtom id (Nat.le_succ N)
    · apply Submodule.span_le.mpr
      intro x hx
      have he : x = direction N := by simpa using hx
      change x ∈ stage (N + 1)
      rw [he]
      exact direction_mem_succ N

theorem stage_succ_of_zero (N : ℕ) (hN : direction N = 0) :
    stage (N + 1) = stage N := by
  rw [stage_succ, hN]
  simp

theorem projection_direction_eq_zero (N : ℕ) :
    (stage N).starProjection (direction N) = 0 := by
  have h1 := Submodule.inner_right_of_mem_orthogonal
    ((stage N).starProjection_apply_mem (direction N)) (direction_mem_orthogonal N)
  have h2 := Submodule.inner_right_of_mem_orthogonal
    ((stage N).starProjection_apply_mem (direction N))
    (Submodule.sub_starProjection_mem_orthogonal (K := stage N) (direction N))
  rw [inner_sub_right, h1, real_inner_self_eq_norm_sq] at h2
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg ((stage N).starProjection (direction N))]

theorem projection_succ (N : ℕ) (f : QHilbert) :
    (stage (N + 1)).starProjection f = (stage N).starProjection f +
      (inner ℝ f (direction N)) • direction N := by
  by_cases hN : direction N = 0
  · simp [stage_succ_of_zero N hN, hN]
  · have hv : direction N - (stage N).starProjection (direction N) ≠ 0 := by
      simpa only [projection_direction_eq_zero, sub_zero] using hN
    have he := RiemannResearch.Analysis.SingleDirectionProjection.projection_extension_eq
      (stage N) (direction N) f hv
    simpa only [← stage_succ N, projection_direction_eq_zero, sub_zero, direction_norm N hN,
      one_pow, div_one] using he

open RiemannResearch.Analysis.SingleDirectionProjection

theorem response_succ (N : ℕ) (B : QHilbert →L[ℝ] QHilbert) (f : QHilbert) :
    responseOperator (stage (N + 1)) B f - responseOperator (stage N) B f =
      (inner ℝ (B (f - (stage (N + 1)).starProjection f)) (direction N)) •
        direction N -
      (inner ℝ f (direction N)) • (stage N).starProjection (B (direction N)) := by
  by_cases hN : direction N = 0
  · simp [stage_succ_of_zero N hN, hN]
  · have hv : direction N - (stage N).starProjection (direction N) ≠ 0 := by
      simpa only [projection_direction_eq_zero, sub_zero] using hN
    have he := response_extension_difference_eq (stage N) (direction N) B f hv
    simp only [← stage_succ N, projection_direction_eq_zero, sub_zero, direction_norm N hN,
      one_pow, div_one, neg_smul] at he
    rw [he]
    abel

theorem response_succ_norm_sq (N : ℕ) (B : QHilbert →L[ℝ] QHilbert)
    (f : QHilbert) :
    ‖responseOperator (stage (N + 1)) B f - responseOperator (stage N) B f‖ ^ 2 =
      (inner ℝ (B (f - (stage (N + 1)).starProjection f)) (direction N)) ^ 2 +
      (inner ℝ f (direction N)) ^ 2 *
        ‖(stage N).starProjection (B (direction N))‖ ^ 2 := by
  by_cases hN : direction N = 0
  · simp [stage_succ_of_zero N hN, hN]
  · have he := response_extension_difference_norm_sq_exact_unit
      (stage N) (direction N) (direction_mem_orthogonal N) (direction_norm N hN) B f
    simpa only [← stage_succ N] using he

theorem response_succ_norm_sq_le (N : ℕ) (B : QHilbert →L[ℝ] QHilbert)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) (f : QHilbert) :
    ‖responseOperator (stage (N + 1)) B f - responseOperator (stage N) B f‖ ^ 2 ≤
      ‖f - (stage N).starProjection f‖ ^ 2 * ‖B (direction N)‖ ^ 2 := by
  by_cases hN : direction N = 0
  · simp [stage_succ_of_zero N hN, hN]
  · have he := response_extension_difference_norm_sq_le_unit
      (stage N) (direction N) (direction_mem_orthogonal N) (direction_norm N hN) B hB f
    simpa only [← stage_succ N] using he

open QSquarefreeSmoothedProjection QShiftedReciprocal

def targetCoefficient (N : ℕ) : ℝ := inner ℝ qOne (direction N)
def responseCoefficient (N : ℕ) : ℝ := inner ℝ (B (residual (N + 1))) (direction N)
def orthogonalTerm (N : ℕ) : QHilbert := responseCoefficient N • direction N
def correctionTerm (N : ℕ) : QHilbert :=
  targetCoefficient N • (stage N).starProjection (B (direction N))

theorem movingCorrection_increment (N : ℕ) :
    movingCorrection (N + 1) - movingCorrection N =
      orthogonalTerm N - correctionTerm N := by
  simpa only [responseOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, movingCorrection,
    ZetaTwoOptimizerStage.residual, optimizer, orthogonalTerm, correctionTerm, responseCoefficient,
    targetCoefficient] using response_succ N B qOne

theorem movingCorrection_increment_norm_sq (N : ℕ) :
    ‖movingCorrection (N + 1) - movingCorrection N‖ ^ 2 =
      (responseCoefficient N) ^ 2 + (targetCoefficient N) ^ 2 *
        ‖(stage N).starProjection (B (direction N))‖ ^ 2 := by
  simpa only [responseOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, movingCorrection,
    ZetaTwoOptimizerStage.residual, optimizer, responseCoefficient, targetCoefficient] using
      response_succ_norm_sq N B qOne

theorem movingCorrection_increment_norm_sq_le (N : ℕ) :
    ‖movingCorrection (N + 1) - movingCorrection N‖ ^ 2 ≤
      error N * ‖B (direction N)‖ ^ 2 := by
  simpa only [responseOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, movingCorrection,
    ZetaTwoOptimizerStage.residual, optimizer, error] using
      response_succ_norm_sq_le N B B_symmetric qOne

end RiemannResearch.RH.QCanonicalInnovation
