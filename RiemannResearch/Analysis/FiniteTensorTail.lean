/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Complete finite orthonormal-row tail certificates

Source: Prime Tensor CRT RH Research Project (2 November 2026), section 6,
for the requested certificate; standard orthogonal projection and triangle
inequality for the proofs. The residual Gram is the actual complete tail,
not a matrix of truncated physical moments. RH application: use arithmetic
divisor-wavelet rows and legal residue columns.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteTensorTail
open RiemannResearch.Analysis.FiniteHilbertGram
variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def tailMap (v : κ → H) : H →ₗ[ℝ] H :=
  LinearMap.id - (synthesisSpan v).starProjection.toLinearMap

theorem split_error (v : κ → H) (hv : Orthonormal ℝ v) (x : H) :
    ‖x‖^2 = (∑ k, (inner ℝ (v k) x)^2) + ‖tailMap v x‖^2 := by
  have h := projection_error_eq_orthonormal_sum hv x
  change ‖x - (synthesisSpan v).starProjection x‖^2 = _ at h
  change _ = _ + ‖x - (synthesisSpan v).starProjection x‖^2
  linarith

theorem column_bound (v : κ → H) (a : ι → H) (c : ι → ℝ) :
    ‖tailMap v (Fintype.linearCombination ℝ a c)‖ ≤
      ∑ i, |c i| * ‖tailMap v (a i)‖ := by
  rw [Fintype.linearCombination_apply, map_sum]
  simpa only [map_smul, norm_smul, Real.norm_eq_abs] using
    norm_sum_le Finset.univ (fun i => c i • tailMap v (a i))

/-- All signed cross terms of the complete residual Gram. -/
theorem tail_gram_exact (v : κ → H) (a : ι → H) (c : ι → ℝ) :
    (∑ i, ∑ j, c i * c j * inner ℝ (tailMap v (a i)) (tailMap v (a j))) =
      ‖tailMap v (Fintype.linearCombination ℝ a c)‖^2 := by
  rw [Fintype.linearCombination_apply, map_sum, ← real_inner_self_eq_norm_sq, sum_inner]
  simp only [map_smul, real_inner_smul_left, inner_sum, inner_smul_right]
  congr 1
  funext i
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tail_gram_nonneg (v : κ → H) (a : ι → H) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j *
      inner ℝ (tailMap v (a i)) (tailMap v (a j)) := by
  rw [tail_gram_exact]
  exact sq_nonneg _

theorem column_tail_sq (v : κ → H) (hv : Orthonormal ℝ v) (a : H) :
    ‖tailMap v a‖^2 = ‖a‖^2 - ∑ k, (inner ℝ (v k) a)^2 := by
  linarith [split_error v hv a]

/-- The target must be a retained mode; this is not a density assumption. -/
theorem column_certificate (v : κ → H) (hv : Orthonormal ℝ v)
    (a : ι → H) (c : ι → ℝ) (target : H) (ht : target ∈ synthesisSpan v) :
    ‖target - Fintype.linearCombination ℝ a c‖^2 ≤
      (∑ k, (inner ℝ (v k) (target-Fintype.linearCombination ℝ a c))^2) +
      (∑ i, |c i| * ‖tailMap v (a i)‖)^2 := by
  have hz : tailMap v target = 0 := by
    change target - (synthesisSpan v).starProjection target = 0
    rw [Submodule.starProjection_eq_self_iff.mpr ht, sub_self]
  rw [split_error v hv, map_sub, hz, zero_sub, norm_neg]
  have hb := column_bound v a c
  apply add_le_add_right
  simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) hb

end RiemannResearch.Analysis.FiniteTensorTail
