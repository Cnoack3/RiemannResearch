/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteHilbertConstraints
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Capacities of actual finite Hilbert Gram forms

Source: user-provided argument,
`RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`,
Sections 12 and 14. This file formalizes the inverse-Gram variational
quantity and its rank-one change on adding the first physical coordinate.
The Gram inverse is constructed from independence of the actual vectors.
No divergent-capacity assertion is assumed or proved here.
-/

open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteGramCapacity
noncomputable section

open FiniteHilbertGram FiniteHilbertConstraints

variable {ι H K : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- The actual inverse Gram action on an arbitrary source vector. -/
def inverseSource {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) : ι → ℝ :=
  (gramEquiv hv).symm b

/-- Inverse-Gram capacity, with all signed mixed entries retained. -/
def capacity {v : ι → H} (hv : LinearIndependent ℝ v) (b : ι → ℝ) : ℝ :=
  ∑ i, inverseSource hv b i * b i

theorem inverseSource_normal {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (i : ι) :
    gram v (inverseSource hv b) i = b i := by
  exact congrFun ((gramEquiv hv).apply_symm_apply b) i

theorem inner_synthesis_minimumVector {v : ι → H} (hv : LinearIndependent ℝ v)
    (b c : ι → ℝ) :
    inner ℝ (Fintype.linearCombination ℝ v c) (minimumVector hv b) =
      ∑ i, c i * b i := by
  rw [inner_synthesis_left]
  simp only [minimumVector_observation]

theorem capacity_eq_norm_sq {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) : capacity hv b = ‖minimumVector hv b‖ ^ 2 := by
  simpa only [capacity, inverseSource] using (minimumVector_norm_sq hv b).symm

theorem capacity_nonneg {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) : 0 ≤ capacity hv b := by
  rw [capacity_eq_norm_sq]
  exact sq_nonneg _

theorem capacity_pos {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (hb : b ≠ 0) : 0 < capacity hv b := by
  rw [capacity_eq_norm_sq]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hz
  apply hb
  funext i
  have hi := minimumVector_observation hv b i
  rw [hz, inner_zero_right] at hi
  exact hi.symm

/-- The complete unconstrained quadratic optimization identity. -/
theorem capacity_completion {v : ι → H} (hv : LinearIndependent ℝ v)
    (b c : ι → ℝ) :
    2 * (∑ i, c i * b i) - ‖Fintype.linearCombination ℝ v c‖ ^ 2 =
      capacity hv b - ‖minimumVector hv b - Fintype.linearCombination ℝ v c‖ ^ 2 := by
  rw [norm_sub_sq_real, ← capacity_eq_norm_sq, real_inner_comm,
    inner_synthesis_minimumVector]
  ring

theorem quadratic_le_capacity {v : ι → H} (hv : LinearIndependent ℝ v)
    (b c : ι → ℝ) :
    2 * (∑ i, c i * b i) - ‖Fintype.linearCombination ℝ v c‖ ^ 2 ≤
      capacity hv b := by
  rw [capacity_completion]
  exact sub_le_self _ (sq_nonneg _)

/-- A trial direction gives a capacity lower bound without discarding cross terms. -/
theorem source_sq_le_capacity_mul_energy {v : ι → H} (hv : LinearIndependent ℝ v)
    (b c : ι → ℝ) :
    (∑ i, c i * b i) ^ 2 ≤
      capacity hv b * ‖Fintype.linearCombination ℝ v c‖ ^ 2 := by
  rw [← inner_synthesis_minimumVector hv b c, capacity_eq_norm_sq]
  have h := real_inner_mul_inner_self_le
    (Fintype.linearCombination ℝ v c) (minimumVector hv b)
  simpa only [real_inner_self_eq_norm_sq, ← pow_two, mul_comm] using h

/-- Prescribing source pairing one has the exact minimum `1 / capacity`.
The nonnegative square on the right also certifies uniqueness. -/
theorem constrained_completion {v : ι → H} (hv : LinearIndependent ℝ v)
    (b c : ι → ℝ) (hb : b ≠ 0) (hc : (∑ i, c i * b i) = 1) :
    ‖Fintype.linearCombination ℝ v c‖ ^ 2 =
      1 / capacity hv b +
        ‖Fintype.linearCombination ℝ v c - (capacity hv b)⁻¹ • minimumVector hv b‖ ^ 2 := by
  have hp := capacity_pos hv b hb
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_smul_right, inner_synthesis_minimumVector, hc, ← capacity_eq_norm_sq]
  field_simp [ne_of_gt hp]
  ring

theorem normalized_source {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (hb : b ≠ 0) :
    (∑ i, ((capacity hv b)⁻¹ • inverseSource hv b) i * b i) = 1 := by
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  change (capacity hv b)⁻¹ * capacity hv b = 1
  exact inv_mul_cancel₀ (ne_of_gt (capacity_pos hv b hb))

theorem normalized_energy {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (hb : b ≠ 0) :
    ‖(capacity hv b)⁻¹ • minimumVector hv b‖ ^ 2 = 1 / capacity hv b := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ← capacity_eq_norm_sq]
  field_simp [ne_of_gt (capacity_pos hv b hb)]

/-- A point vector of squared norm `1/2` with source pairings `b/2`
has the exact finite approximation deficit used in the RH application. -/
theorem point_target_deficit {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (e : H) (he : ‖e‖ ^ 2 = (1 / 2 : ℝ))
    (hcross : ∀ i, cross v e i = (1 / 2 : ℝ) * b i) :
    ‖e - Fintype.linearCombination ℝ v (inverseCoeff hv e)‖ ^ 2 =
      (1 / 2 : ℝ) - (1 / 4 : ℝ) * capacity hv b := by
  have hcoeff : inverseCoeff hv e = (1 / 2 : ℝ) • inverseSource hv b := by
    have hvec : cross v e = (1 / 2 : ℝ) • b := by
      funext i
      exact hcross i
    unfold inverseCoeff inverseSource
    rw [hvec, map_smul]
  rw [residual_schur_value, he]
  congr 1
  rw [hcoeff]
  simp only [Pi.smul_apply, smul_eq_mul, hcross]
  unfold capacity
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Sherman--Morrison in the one-coordinate normalization of the source.
Both inverses are actual Hilbert Gram inverses. -/
theorem inverseSource_rank_one_half {v : ι → H} {w : ι → K}
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w)
    (b : ι → ℝ)
    (hrel : ∀ c i, gram v c i = gram w c i +
      (1 / 2 : ℝ) * b i * (∑ j, c j * b j)) :
    inverseSource hv b =
      (2 / (capacity hw b + 2)) • inverseSource hw b := by
  have hden : capacity hw b + 2 ≠ 0 := by
    have hn := capacity_nonneg hw b
    linarith
  apply gram_injective hv
  funext i
  rw [inverseSource_normal, hrel]
  have hsum : (∑ j, ((2 / (capacity hw b + 2)) • inverseSource hw b) j * b j) =
      (2 / (capacity hw b + 2)) * capacity hw b := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    rfl
  rw [hsum]
  rw [map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, inverseSource_normal]
  field_simp [hden]
  ring

theorem capacity_rank_one_half {v : ι → H} {w : ι → K}
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w)
    (b : ι → ℝ)
    (hrel : ∀ c i, gram v c i = gram w c i +
      (1 / 2 : ℝ) * b i * (∑ j, c j * b j)) :
    capacity hv b = 2 * capacity hw b / (capacity hw b + 2) := by
  unfold capacity
  rw [inverseSource_rank_one_half hv hw b hrel]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  unfold capacity
  ring

theorem pointDeficit_rank_one_half {v : ι → H} {w : ι → K}
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w)
    (b : ι → ℝ)
    (hrel : ∀ c i, gram v c i = gram w c i +
      (1 / 2 : ℝ) * b i * (∑ j, c j * b j)) :
    (1 / 2 : ℝ) - (1 / 4 : ℝ) * capacity hv b = 1 / (capacity hw b + 2) := by
  have hden : capacity hw b + 2 ≠ 0 := by
    have hn := capacity_nonneg hw b
    linarith
  rw [capacity_rank_one_half hv hw b hrel]
  field_simp [hden]
  ring

/-- The two Gram minimizers with source pairing one coincide. -/
theorem normalized_inverseSource_rank_one_half {v : ι → H} {w : ι → K}
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w)
    (b : ι → ℝ) (hb : b ≠ 0)
    (hrel : ∀ c i, gram v c i = gram w c i +
      (1 / 2 : ℝ) * b i * (∑ j, c j * b j)) :
    (capacity hv b)⁻¹ • inverseSource hv b =
      (capacity hw b)⁻¹ • inverseSource hw b := by
  have hτ := ne_of_gt (capacity_pos hw b hb)
  have hden : capacity hw b + 2 ≠ 0 := by
    have hn := capacity_nonneg hw b
    linarith
  rw [capacity_rank_one_half hv hw b hrel,
    inverseSource_rank_one_half hv hw b hrel]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [hτ, hden]

/-- Exact scalar-observation completion, with arbitrary prescribed value. -/
theorem constrained_value_completion {v : ι → H} (hv : LinearIndependent ℝ v)
    (b c : ι → ℝ) (hb : b ≠ 0) (δ : ℝ)
    (hc : (∑ i, c i * b i) = δ) :
    ‖Fintype.linearCombination ℝ v c‖ ^ 2 =
      δ ^ 2 / capacity hv b +
        ‖Fintype.linearCombination ℝ v c -
          (δ / capacity hv b) • minimumVector hv b‖ ^ 2 := by
  have hp := capacity_pos hv b hb
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_smul_right, inner_synthesis_minimumVector, hc, ← capacity_eq_norm_sq]
  field_simp [ne_of_gt hp]
  ring

/-- Energy of the minimum-norm vector at an arbitrary scalar observation. -/
theorem scaled_source_energy {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (hb : b ≠ 0) (δ : ℝ) :
    ‖(δ / capacity hv b) • minimumVector hv b‖ ^ 2 =
      δ ^ 2 / capacity hv b := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ← capacity_eq_norm_sq]
  field_simp [ne_of_gt (capacity_pos hv b hb)]

end
end RiemannResearch.Analysis.FiniteGramCapacity
