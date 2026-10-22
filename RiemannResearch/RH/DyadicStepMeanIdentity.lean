import RiemannResearch.RH.DyadicQuotientAbel
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Module

/-!
# Exact mean and centered energies for the actual projected step orbit

Source: user-provided September 10, 2026 dyadic-regularization ledger,
step-orbit provider (N24)--(N30); supports the actual orbit and energy questions.

Every integer step has mean one. The finite Abel cutoff has mean `1-r^N`,
so its approximation error includes the exact scalar defect `r^(2*N)`.
The remaining energy is the complete centered Gram form. These identities
do not assert the still-required uniform arithmetic Gram estimate.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators
noncomputable section

@[simp] theorem dyadicQuotientProjection_inner_one (f : ThresholdHilbert) :
    inner ℝ (dyadicQuotientProjection f) hilbertOne = inner ℝ f hilbertOne := by
  rw [dyadicQuotientProjection_inner, dyadicQuotientProjection_one]

@[simp] theorem dyadicQuotientDilation_inner_one (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) :
    inner ℝ (dyadicQuotientDilation m hm f) hilbertOne = inner ℝ f hilbertOne := by
  rw [dyadicQuotientDilation_apply, dyadicQuotientProjection_inner_one]
  have h := ContinuousLinearMap.adjoint_inner_right
    (hilbertDilationContinuous m hm) f hilbertOne
  change inner ℝ f (hilbertDilationAdjoint m hm hilbertOne) =
    inner ℝ (hilbertDilation m hm f) hilbertOne at h
  rw [hilbertDilationAdjoint_one] at h
  exact h.symm

/-- The actual quotient representative of the integer step `T_m 1`. -/
def dyadicProjectedStep (m : ℕ) (hm : 0 < m) : ThresholdHilbert :=
  dyadicQuotientProjection (hilbertDilation m hm hilbertOne)

@[simp] theorem dyadicProjectedStep_inner_one (m : ℕ) (hm : 0 < m) :
    inner ℝ (dyadicProjectedStep m hm) hilbertOne = 1 := by
  have h := dyadicQuotientDilation_inner_one m hm hilbertOne
  simpa only [dyadicQuotientDilation_apply, dyadicProjectedStep,
    real_inner_self_eq_norm_sq, hilbertOne_norm_sq] using h

@[simp] theorem dyadicProjectedStep_one :
    dyadicProjectedStep 1 (by norm_num) = hilbertOne := by
  simp only [dyadicProjectedStep, hilbertDilation_one, dyadicQuotientProjection_one]

/-- Multiplying a physical step index by two changes no quotient vector. -/
theorem dyadicProjectedStep_double (m : ℕ) (hm : 0 < m) :
    dyadicProjectedStep (2 * m) (by positivity) = dyadicProjectedStep m hm := by
  unfold dyadicProjectedStep
  rw [← hilbertDilation_comp 2 m (by norm_num) hm,
    dyadicQuotientProjection_dilation_two]

@[simp] theorem dyadicProjectedStep_two_pow (j : ℕ) :
    dyadicProjectedStep (2 ^ j) (by positivity) = hilbertOne := by
  induction j with
  | zero => simpa only [pow_zero] using dyadicProjectedStep_one
  | succ j ih =>
      simpa only [pow_succ'] using
        (dyadicProjectedStep_double (2 ^ j) (by positivity)).trans ih

/-- The mean channel is removed with an exact rank-one Gram correction. -/
theorem dyadicProjectedStep_centered_inner (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    inner ℝ (dyadicProjectedStep m hm - hilbertOne)
      (dyadicProjectedStep n hn - hilbertOne) =
      inner ℝ (dyadicProjectedStep m hm) (dyadicProjectedStep n hn) - 1 := by
  have hright : inner ℝ hilbertOne (dyadicProjectedStep n hn) = 1 := by
    rw [real_inner_comm, dyadicProjectedStep_inner_one]
  rw [inner_sub_left, inner_sub_right, inner_sub_right,
    dyadicProjectedStep_inner_one, hright,
    real_inner_self_eq_norm_sq, hilbertOne_norm_sq]
  ring

/-- Exact mean/variance splitting in the physical weighted Hilbert space. -/
theorem hilbert_norm_sq_eq_mean_sq_add_centered (f : ThresholdHilbert) (a : ℝ)
    (ha : inner ℝ f hilbertOne = a) :
    ‖f‖ ^ 2 = a ^ 2 + ‖f - a • hilbertOne‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    hilbertOne_norm_sq, real_inner_smul_right, ha]
  ring

/-- The exact error keeps the scalar mean defect and the complete variance. -/
theorem hilbert_error_sq_eq_mean_defect_add_centered (f : ThresholdHilbert) (a : ℝ)
    (ha : inner ℝ f hilbertOne = a) :
    ‖f - hilbertOne‖ ^ 2 = (a - 1) ^ 2 + ‖f - a • hilbertOne‖ ^ 2 := by
  rw [norm_sub_sq_real, hilbertOne_norm_sq, ha,
    norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    hilbertOne_norm_sq, real_inner_smul_right, ha]
  ring

/-- Every actual projected integer step has norm at least one. -/
theorem dyadicProjectedStep_norm_sq_eq (m : ℕ) (hm : 0 < m) :
    ‖dyadicProjectedStep m hm‖ ^ 2 =
      1 + ‖dyadicProjectedStep m hm - hilbertOne‖ ^ 2 := by
  simpa only [one_pow, one_smul] using
    hilbert_norm_sq_eq_mean_sq_add_centered (dyadicProjectedStep m hm) 1
      (dyadicProjectedStep_inner_one m hm)

theorem one_le_dyadicProjectedStep_norm_sq (m : ℕ) (hm : 0 < m) :
    1 ≤ ‖dyadicProjectedStep m hm‖ ^ 2 := by
  rw [dyadicProjectedStep_norm_sq_eq]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Signed finite step combinations retain the sum of their coefficients as
their exact mean. No positivity requirement is imposed on the coefficients. -/
theorem dyadicProjectedStep_sum_inner_one {ι : Type*} (s : Finset ι)
    (m : ι → ℕ) (hm : ∀ i, 0 < m i) (c : ι → ℝ) :
    inner ℝ (∑ i ∈ s, c i • dyadicProjectedStep (m i) (hm i)) hilbertOne =
      ∑ i ∈ s, c i := by
  simp only [sum_inner, real_inner_smul_left, dyadicProjectedStep_inner_one, mul_one]

/-- The entire centered Gram energy of a signed finite step combination. -/
theorem dyadicProjectedStep_sum_error_sq {ι : Type*} (s : Finset ι)
    (m : ι → ℕ) (hm : ∀ i, 0 < m i) (c : ι → ℝ) :
    ‖(∑ i ∈ s, c i • dyadicProjectedStep (m i) (hm i)) - hilbertOne‖ ^ 2 =
      ((∑ i ∈ s, c i) - 1) ^ 2 +
        ∑ i ∈ s, ∑ j ∈ s, c i * c j *
          (inner ℝ (dyadicProjectedStep (m i) (hm i))
            (dyadicProjectedStep (m j) (hm j)) - 1) := by
  rw [hilbert_error_sq_eq_mean_defect_add_centered _ _
    (dyadicProjectedStep_sum_inner_one s m hm c)]
  congr 1
  have hcenter : (∑ i ∈ s, c i • dyadicProjectedStep (m i) (hm i)) -
      (∑ i ∈ s, c i) • hilbertOne =
      ∑ i ∈ s, c i • (dyadicProjectedStep (m i) (hm i) - hilbertOne) := by
    simp only [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]
  rw [hcenter, ← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_smul_left, real_inner_smul_right,
    dyadicProjectedStep_centered_inner]
  ring

/-- The finite Abel cutoff for the same actual step orbit as (N24). -/
def dyadicStepFiniteAbelAverage (r : ℝ) (N : ℕ) : ThresholdHilbert :=
  (1 - r) • ∑ j ∈ Finset.range N,
    r ^ j • dyadicProjectedStep (3 ^ (j + 1)) (by positivity)

private theorem finite_geometric_mass (r : ℝ) (N : ℕ) :
    (1 - r) * (∑ j ∈ Finset.range N, r ^ j) = 1 - r ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring

/-- The terminal mean defect survives every finite Abel truncation. -/
theorem dyadicStepFiniteAbelAverage_inner_one (r : ℝ) (N : ℕ) :
    inner ℝ (dyadicStepFiniteAbelAverage r N) hilbertOne = 1 - r ^ N := by
  rw [dyadicStepFiniteAbelAverage, real_inner_smul_left,
    dyadicProjectedStep_sum_inner_one]
  exact finite_geometric_mass r N

/-- Exact finite error decomposition, including the omitted geometric tail. -/
theorem dyadicStepFiniteAbelAverage_error_sq (r : ℝ) (N : ℕ) :
    ‖dyadicStepFiniteAbelAverage r N - hilbertOne‖ ^ 2 =
      r ^ (2 * N) +
        ‖dyadicStepFiniteAbelAverage r N - (1 - r ^ N) • hilbertOne‖ ^ 2 := by
  rw [hilbert_error_sq_eq_mean_defect_add_centered _ _
    (dyadicStepFiniteAbelAverage_inner_one r N)]
  congr 1
  rw [Nat.mul_comm 2 N, pow_mul]
  ring

/-- The infinite step Abel average has mean exactly one whenever its physical
vector series is summable. An unsummable `tsum` cannot satisfy this argument. -/
theorem dyadicStepAbelOrbit_inner_one (ε : ℝ) (hε : 0 < ε)
    (hs : Summable (fun j : ℕ => triadicDampingRatio ε ^ j •
      dyadicQuotientProjection
        (hilbertDilation (3 ^ (j + 1)) (by positivity) hilbertOne))) :
    inner ℝ (dyadicStepAbelOrbit ε) hilbertOne = 1 := by
  have hsum : inner ℝ hilbertOne
      (∑' j : ℕ, triadicDampingRatio ε ^ j •
        dyadicProjectedStep (3 ^ (j + 1)) (by positivity)) =
      ∑' j : ℕ, triadicDampingRatio ε ^ j := by
    have hmap := (innerSL ℝ hilbertOne).map_tsum hs
    change inner ℝ hilbertOne
      (∑' j : ℕ, triadicDampingRatio ε ^ j •
        dyadicProjectedStep (3 ^ (j + 1)) (by positivity)) =
      ∑' j : ℕ, inner ℝ hilbertOne (triadicDampingRatio ε ^ j •
        dyadicProjectedStep (3 ^ (j + 1)) (by positivity)) at hmap
    rw [hmap]
    apply tsum_congr
    intro j
    rw [real_inner_smul_right, real_inner_comm,
      dyadicProjectedStep_inner_one, mul_one]
  have hrnorm : ‖triadicDampingRatio ε‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (triadicDampingRatio_pos ε)]
    exact triadicDampingRatio_lt_one hε
  have hg := hasSum_geometric_of_norm_lt_one hrnorm
  rw [dyadicStepAbelOrbit, real_inner_smul_left]
  change (1 - triadicDampingRatio ε) *
    inner ℝ (∑' j : ℕ, triadicDampingRatio ε ^ j •
      dyadicProjectedStep (3 ^ (j + 1)) (by positivity)) hilbertOne = 1
  rw [real_inner_comm, hsum, hg.tsum_eq]
  exact mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr (triadicDampingRatio_lt_one hε)))

/-- All energy beyond the unavoidable mean-one channel is exactly the
distance squared from the target. This does not supply its upper bound. -/
theorem dyadicStepAbelOrbit_norm_sq_eq (ε : ℝ) (hε : 0 < ε)
    (hs : Summable (fun j : ℕ => triadicDampingRatio ε ^ j •
      dyadicQuotientProjection
        (hilbertDilation (3 ^ (j + 1)) (by positivity) hilbertOne))) :
    ‖dyadicStepAbelOrbit ε‖ ^ 2 =
      1 + ‖dyadicStepAbelOrbit ε - hilbertOne‖ ^ 2 := by
  simpa only [one_pow, one_smul] using
    hilbert_norm_sq_eq_mean_sq_add_centered (dyadicStepAbelOrbit ε) 1
      (dyadicStepAbelOrbit_inner_one ε hε hs)

theorem one_le_dyadicStepAbelOrbit_norm_sq (ε : ℝ) (hε : 0 < ε)
    (hs : Summable (fun j : ℕ => triadicDampingRatio ε ^ j •
      dyadicQuotientProjection
        (hilbertDilation (3 ^ (j + 1)) (by positivity) hilbertOne))) :
    1 ≤ ‖dyadicStepAbelOrbit ε‖ ^ 2 := by
  rw [dyadicStepAbelOrbit_norm_sq_eq ε hε hs]
  exact le_add_of_nonneg_right (sq_nonneg _)

end
end RiemannResearch.RH.Pareto
