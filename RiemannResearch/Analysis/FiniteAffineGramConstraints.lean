/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteHilbertConstraints
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.Analysis.AffineObservationProjection
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Complete finite-Gram interpolation and constrained approximation

Source: user-provided reciprocal-head investigation, 7 November 2026,
Section 4. Observation rows are projected into the actual legal subspace.
Their independence is the precise finite full-row-rank condition. Their Gram
matrix is constructed from actual inner products and identified with
A G^{-1} A^T for an independent synthesis dictionary. No infinite physical
tail is replaced by a finite coordinate Gram matrix.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteAffineGramConstraints
open FiniteHilbertGram FiniteHilbertConstraints
open SingleObservationProjection

variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (S : Submodule ℝ H) [S.HasOrthogonalProjection]

/-- Actual Riesz vectors of the observations restricted to the legal space. -/
def projectedRows (e : κ → H) : κ → S :=
  fun i => ⟨S.starProjection (e i), S.starProjection_apply_mem (e i)⟩

theorem projectedRows_inner (e : κ → H) (i : κ) (y : S) :
    inner ℝ (projectedRows S e i) y = inner ℝ (e i) (y : H) := by
  change inner ℝ (S.starProjection (e i)) (y : H) = _
  have h := Submodule.starProjection_inner_eq_zero (e i) (y : H) y.property
  rw [inner_sub_left] at h
  linarith

/-- Minimum complete norm under all independent observations. -/
def minimumInterpolation (e : κ → H)
    (he : LinearIndependent ℝ (projectedRows S e)) (b : κ → ℝ) : H :=
  (minimumVector he b : S)

theorem minimumInterpolation_mem (e : κ → H)
    (he : LinearIndependent ℝ (projectedRows S e)) (b : κ → ℝ) :
    minimumInterpolation S e he b ∈ S :=
  (minimumVector he b).property

theorem minimumInterpolation_observation (e : κ → H)
    (he : LinearIndependent ℝ (projectedRows S e)) (b : κ → ℝ) (i : κ) :
    inner ℝ (e i) (minimumInterpolation S e he b) = b i := by
  rw [minimumInterpolation, ← projectedRows_inner S e i]
  exact minimumVector_observation he b i

/-- Exact interpolation completion, including the full legal-null remainder. -/
theorem minimumInterpolation_completion (e : κ → H)
    (he : LinearIndependent ℝ (projectedRows S e)) (b : κ → ℝ)
    (y : H) (hy : y ∈ S) (hobs : ∀ i, inner ℝ (e i) y = b i) :
    ‖y‖ ^ 2 = ‖minimumInterpolation S e he b‖ ^ 2 +
      ‖y - minimumInterpolation S e he b‖ ^ 2 := by
  have hc := feasible_norm_sq_completion he b (⟨y, hy⟩ : S) (by
    intro i
    rw [projectedRows_inner]
    exact hobs i)
  exact hc

variable [DecidableEq κ]

/-- Literal inverse of the actual restricted-observation Gram matrix. -/
theorem minimumInterpolation_matrix_value (e : κ → H)
    (he : LinearIndependent ℝ (projectedRows S e)) (b : κ → ℝ) :
    ‖minimumInterpolation S e he b‖ ^ 2 =
      dotProduct b ((gramMatrix (projectedRows S e))⁻¹.mulVec b) := by
  change ‖minimumVector he b‖ ^ 2 = _
  rw [minimumVector_norm_sq, gramMatrix_inverseSource he]
  unfold FiniteGramCapacity.inverseSource dotProduct
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- Project the full target first, then repair its exact observation mismatch. -/
def affineOptimizer (e : κ → H)
    (he : LinearIndependent ℝ (projectedRows S e)) (x : H) (b : κ → ℝ) : H :=
  S.starProjection x + minimumInterpolation S e he
    (fun i => b i - inner ℝ (e i) (S.starProjection x))

theorem affineOptimizer_mem (e : κ → H)
    (he : LinearIndependent ℝ (projectedRows S e)) (x : H) (b : κ → ℝ) :
    affineOptimizer S e he x b ∈ S :=
  S.add_mem (S.starProjection_apply_mem x) (minimumInterpolation_mem S e he _)

theorem affineOptimizer_observation (e : κ → H)
    (he : LinearIndependent ℝ (projectedRows S e)) (x : H) (b : κ → ℝ) (i : κ) :
    inner ℝ (e i) (affineOptimizer S e he x b) = b i := by
  rw [affineOptimizer, inner_add_right, minimumInterpolation_observation]
  ring

/-- Complete constrained approximation: projection error, exact repair cost,
and the complete nonnegative null-observation remainder are all retained. -/
theorem affine_error_completion (e : κ → H)
    (he : LinearIndependent ℝ (projectedRows S e)) (x y : H) (b : κ → ℝ)
    (hy : y ∈ S) (hobs : ∀ i, inner ℝ (e i) y = b i) :
    ‖x - y‖ ^ 2 = ‖x - S.starProjection x‖ ^ 2 +
      ‖minimumInterpolation S e he
        (fun i => b i - inner ℝ (e i) (S.starProjection x))‖ ^ 2 +
      ‖y - affineOptimizer S e he x b‖ ^ 2 := by
  rw [affine_target_error_split S x y hy]
  have hc := minimumInterpolation_completion S e he
    (fun i => b i - inner ℝ (e i) (S.starProjection x))
    (y - S.starProjection x)
    (S.sub_mem hy (S.starProjection_apply_mem x)) (by
      intro i
      rw [inner_sub_right, hobs i])
  rw [hc]
  have hid : y - S.starProjection x - minimumInterpolation S e he
      (fun i => b i - inner ℝ (e i) (S.starProjection x)) =
      y - affineOptimizer S e he x b := by
    unfold affineOptimizer
    abel
  rw [hid]
  ring

/-- Constrained approximation really attains its complete error minimum. -/
theorem affineOptimizer_minimizes (e : κ → H)
    (he : LinearIndependent ℝ (projectedRows S e)) (x y : H) (b : κ → ℝ)
    (hy : y ∈ S) (hobs : ∀ i, inner ℝ (e i) y = b i) :
    ‖x - affineOptimizer S e he x b‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
  have hyc := affine_error_completion S e he x y b hy hobs
  have hoc := affine_error_completion S e he x (affineOptimizer S e he x b) b
    (affineOptimizer_mem S e he x b) (affineOptimizer_observation S e he x b)
  simp only [sub_self, norm_zero, zero_pow, add_zero] at hoc
  nlinarith [sq_nonneg ‖y - affineOptimizer S e he x b‖]

/-- Full projection agrees with the constraints precisely when the exact
observation mismatch vanishes; no approximate-head substitution is made. -/
theorem projection_feasible_iff_mismatch_zero (e : κ → H) (x : H) (b : κ → ℝ) :
    (∀ i, inner ℝ (e i) (S.starProjection x) = b i) ↔
      (fun i => b i - inner ℝ (e i) (S.starProjection x)) = 0 := by
  constructor
  · intro h
    funext i
    simp only [h i, sub_self, Pi.zero_apply]
  · intro h i
    have hi := congrFun h i
    simp only [Pi.zero_apply] at hi
    exact (sub_eq_zero.mp hi).symm

variable [DecidableEq ι]

/-- The restricted-row Gram is exactly A G^{-1} A^T for the physical dictionary. -/
theorem projectedRows_gramMatrix {v : ι → H} (hv : LinearIndependent ℝ v)
    (e : κ → H) :
    gramMatrix (projectedRows (synthesisSpan v) e) =
      observationMatrix v e * (gramMatrix v)⁻¹ * (observationMatrix v e).transpose := by
  ext i j
  change inner ℝ ((synthesisSpan v).starProjection (e i))
    ((synthesisSpan v).starProjection (e j)) = _
  exact congrFun (congrFun (projection_kernel_matrix hv e) i) j

/-- The paper's complete finite-Gram constrained approximation formula,
with both inverse matrices derived from independence of their actual rows. -/
theorem finiteDictionary_error_completion {v : ι → H}
    (hv : LinearIndependent ℝ v) (e : κ → H)
    (he : LinearIndependent ℝ (projectedRows (synthesisSpan v) e))
    (x y : H) (b : κ → ℝ) (hy : y ∈ synthesisSpan v)
    (hobs : ∀ i, inner ℝ (e i) y = b i) :
    let δ := fun i => b i - inner ℝ (e i) ((synthesisSpan v).starProjection x)
    ‖x - y‖ ^ 2 =
      ‖x‖ ^ 2 - dotProduct (cross v x) ((gramMatrix v)⁻¹.mulVec (cross v x)) +
      dotProduct δ
        ((observationMatrix v e * (gramMatrix v)⁻¹ *
          (observationMatrix v e).transpose)⁻¹.mulVec δ) +
      ‖y - affineOptimizer (synthesisSpan v) e he x b‖ ^ 2 := by
  dsimp only
  have hc := affine_error_completion (synthesisSpan v) e he x y b hy hobs
  rw [minimumInterpolation_matrix_value, projectedRows_gramMatrix hv e] at hc
  have hp := residual_matrix_value hv x
  rw [← inverseCoeff_eq_inv_mulVec hv x,
    synthesis_inverseCoeff_eq_projection hv x] at hp
  rw [hp] at hc
  rw [inverseCoeff_eq_inv_mulVec hv x] at hc
  exact hc

end RiemannResearch.Analysis.FiniteAffineGramConstraints
