import RiemannResearch.RH.DyadicQuotientAbel
import RiemannResearch.RH.DyadicTriadicComplementObstruction

/-!
# Actual centered dyadic repairs with exact signed scalar optimization

Source: user-provided `DyadicRegularizedVerificationContinuation20260910.md`,
the remaining complete complementary-energy obligation and its second seed.

For every positive integer m the vector G_m = T_m R₂ - R₂ is a finite
dyadic legal vector, and the residue cocycle gives G_m = (T₂-I)R_m.
Consequently it does not change the dyadic quotient. For m ≥ 2 its physical
coordinate at 1 is -1, so the scalar least-squares denominator is nonzero.

The full error reduction is an exact equality with its signed mixed term.
There is no claim that iterating these repairs exhausts complementary energy.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators

noncomputable section

/-- A finite dyadic legal direction using an arbitrary integer dilation. -/
def dyadicCenteredSeed (m : ℕ) (hm : 0 < m) : ThresholdHilbert :=
  hilbertDilation m hm (hilbertResidue 2 (by norm_num)) -
    hilbertResidue 2 (by norm_num)

theorem dyadicCenteredSeed_cocycle (m : ℕ) (hm : 0 < m) :
    dyadicCenteredSeed m hm =
      hilbertDilation 2 (by norm_num) (hilbertResidue m hm) - hilbertResidue m hm :=
  hilbertDilation_residue_cocycle m 2 hm (by norm_num)

/-- Both summands are genuine finite legal dyadic generators. -/
theorem dyadicCenteredSeed_mem_legalSubspace
    (m : ℕ) (hm : 0 < m) (A : Set ℕ) (h2 : 2 ∈ A) :
    dyadicCenteredSeed m hm ∈ hilbertLegalSubspace A := by
  have hgen (d : ℕ) (hd : 0 < d) :
      hilbertDilation d hd (hilbertResidue 2 (by norm_num)) ∈
        hilbertLegalSubspace A := by
    change hilbertSequence (hilbertDilation d hd (hilbertResidue 2 (by norm_num))) ∈
      legalSeedSpan A
    rw [hilbertDilation_sequence, hilbertResidue_sequence]
    exact dilation_generator_mem A h2 hd
  exact (hilbertLegalSubspace A).sub_mem (hgen m hm)
    (by simpa only [hilbertDilation_one] using hgen 1 (by norm_num))

/-- The correction changes only the complementary physical energy. -/
@[simp] theorem dyadicQuotientProjection_centeredSeed (m : ℕ) (hm : 0 < m) :
    dyadicQuotientProjection (dyadicCenteredSeed m hm) = 0 := by
  rw [dyadicCenteredSeed_cocycle, map_sub,
    dyadicQuotientProjection_dilation_two, sub_self]

theorem dyadicCenteredSeed_coordinate_one (m : ℕ) (hm : 0 < m) (hm2 : 2 ≤ m) :
    hilbertSequence (dyadicCenteredSeed m hm) 1 = -1 := by
  rw [dyadicCenteredSeed, hilbertSequence_sub,
    hilbertDilation_sequence, hilbertResidue_sequence]
  have hdiv : 1 / m = 0 := Nat.div_eq_of_lt (by omega)
  simp [dilation, residue, hdiv]

theorem dyadicCenteredSeed_ne_zero (m : ℕ) (hm : 0 < m) (hm2 : 2 ≤ m) :
    dyadicCenteredSeed m hm ≠ 0 := by
  intro hz
  have hc := dyadicCenteredSeed_coordinate_one m hm hm2
  rw [hz] at hc
  have hzero : hilbertSequence (0 : ThresholdHilbert) = 0 :=
    hilbertSequenceLinear.map_zero
  rw [hzero] at hc
  norm_num at hc

theorem dyadicCenteredSeed_norm_sq_pos (m : ℕ) (hm : 0 < m) (hm2 : 2 ≤ m) :
    0 < ‖dyadicCenteredSeed m hm‖ ^ 2 :=
  sq_pos_of_pos (norm_pos_iff.mpr (dyadicCenteredSeed_ne_zero m hm hm2))

theorem inner_one_dyadicCenteredSeed (m : ℕ) (hm : 0 < m) :
    inner ℝ hilbertOne (dyadicCenteredSeed m hm) = 0 := by
  calc
    inner ℝ hilbertOne (dyadicCenteredSeed m hm) =
        inner ℝ (dyadicQuotientProjection hilbertOne) (dyadicCenteredSeed m hm) := by
      rw [dyadicQuotientProjection_one]
    _ = inner ℝ hilbertOne (dyadicQuotientProjection (dyadicCenteredSeed m hm)) :=
      dyadicQuotientProjection_inner _ _
    _ = 0 := by rw [dyadicQuotientProjection_centeredSeed, inner_zero_right]

@[simp] theorem dyadicQuotientProjection_centered_repair
    (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) (t : ℝ) :
    dyadicQuotientProjection (f + t • dyadicCenteredSeed m hm) =
      dyadicQuotientProjection f := by
  rw [map_add, map_smul, dyadicQuotientProjection_centeredSeed, smul_zero, add_zero]

/-- Every finite dyadic lift splits into one uncentered seed and centered
integer-dilation corrections, with its exact signed coefficient sum. -/
theorem finite_dyadic_lift_centered_decomposition
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) :
    ∑ i ∈ s, a i • hilbertDilation (m i) (hm i) (hilbertResidue 2 (by norm_num)) =
      (∑ i ∈ s, a i) • hilbertResidue 2 (by norm_num) +
        ∑ i ∈ s, a i • dyadicCenteredSeed (m i) (hm i) := by
  simp only [dyadicCenteredSeed, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]
  abel

/-- The projected dyadic channel depends on precisely one signed scalar.
In particular a zero-total-coefficient dyadic lift is quotient-null. -/
theorem finite_dyadic_lift_projection
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) :
    dyadicQuotientProjection
      (∑ i ∈ s, a i • hilbertDilation (m i) (hm i) (hilbertResidue 2 (by norm_num))) =
      (∑ i ∈ s, a i) • dyadicQuotientProjection (hilbertResidue 2 (by norm_num)) := by
  rw [finite_dyadic_lift_centered_decomposition]
  simp only [map_add, map_smul, map_sum, dyadicQuotientProjection_centeredSeed,
    smul_zero, Finset.sum_const_zero, add_zero]

/-- The optimizer uses exactly the complementary correlation. -/
theorem inner_dyadicCenteredSeed_eq_complementary
    (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) :
    inner ℝ f (dyadicCenteredSeed m hm) =
      inner ℝ (f - dyadicQuotientProjection f) (dyadicCenteredSeed m hm) := by
  rw [inner_sub_left, dyadicQuotientProjection_inner,
    dyadicQuotientProjection_centeredSeed, inner_zero_right, sub_zero]

/-- The repaired vector is an actual finite two-seed legal lift. -/
theorem dyadicCenteredSeed_repair_mem_twoSeed
    (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert)
    (hf : f ∈ dyadicTailTriadicSpan 1) (t : ℝ) :
    f + t • dyadicCenteredSeed m hm ∈ hilbertLegalSubspace ({2, 3} : Set ℕ) := by
  apply (hilbertLegalSubspace ({2, 3} : Set ℕ)).add_mem
  · exact dyadicTailTriadicSpan_le_hilbertLegalSubspace 1 _ (by simp) hf
  · exact (hilbertLegalSubspace ({2, 3} : Set ℕ)).smul_mem t
      (dyadicCenteredSeed_mem_legalSubspace m hm _ (by simp))

/-- The entire signed mixed term is retained before optimization. -/
theorem dyadicCenteredSeed_repair_error
    (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) (t : ℝ) :
    ‖hilbertOne - (f + t • dyadicCenteredSeed m hm)‖ ^ 2 =
      ‖hilbertOne - f‖ ^ 2 +
        2 * t * inner ℝ f (dyadicCenteredSeed m hm) +
        t ^ 2 * ‖dyadicCenteredSeed m hm‖ ^ 2 := by
  have heq : hilbertOne - (f + t • dyadicCenteredSeed m hm) =
      (hilbertOne - f) - t • dyadicCenteredSeed m hm := by abel
  rw [heq, norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, real_inner_smul_right, inner_sub_left, inner_one_dyadicCenteredSeed]
  ring

/-- The actual, signed least-squares coefficient. -/
def dyadicCenteredRepairCoefficient (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) : ℝ :=
  -(inner ℝ f (dyadicCenteredSeed m hm)) / ‖dyadicCenteredSeed m hm‖ ^ 2

/-- Exact complete-square identity, including the nonnegative distance from
the unique minimizing scalar. It makes no convergence assumption. -/
theorem dyadicCenteredSeed_repair_complete_square
    (m : ℕ) (hm : 0 < m) (hm2 : 2 ≤ m) (f : ThresholdHilbert) (t : ℝ) :
    ‖hilbertOne - (f + t • dyadicCenteredSeed m hm)‖ ^ 2 =
      ‖hilbertOne - f‖ ^ 2 -
        (inner ℝ f (dyadicCenteredSeed m hm)) ^ 2 / ‖dyadicCenteredSeed m hm‖ ^ 2 +
      ‖dyadicCenteredSeed m hm‖ ^ 2 *
        (t - dyadicCenteredRepairCoefficient m hm f) ^ 2 := by
  rw [dyadicCenteredSeed_repair_error, dyadicCenteredRepairCoefficient]
  have hn : ‖dyadicCenteredSeed m hm‖ ^ 2 ≠ 0 :=
    ne_of_gt (dyadicCenteredSeed_norm_sq_pos m hm hm2)
  have hnorm : ‖dyadicCenteredSeed m hm‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (dyadicCenteredSeed_ne_zero m hm hm2)
  field_simp [hn, hnorm]
  ring

/-- A proved physical gain, with no discarded cross term and no statement
that the remaining error can be made to tend to zero. -/
theorem dyadicCenteredSeed_optimal_repair_error
    (m : ℕ) (hm : 0 < m) (hm2 : 2 ≤ m) (f : ThresholdHilbert) :
    ‖hilbertOne - (f + dyadicCenteredRepairCoefficient m hm f •
      dyadicCenteredSeed m hm)‖ ^ 2 =
      ‖hilbertOne - f‖ ^ 2 -
        (inner ℝ f (dyadicCenteredSeed m hm)) ^ 2 / ‖dyadicCenteredSeed m hm‖ ^ 2 := by
  simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero]
    using dyadicCenteredSeed_repair_complete_square m hm hm2 f
      (dyadicCenteredRepairCoefficient m hm f)

theorem dyadicCenteredSeed_optimal_repair_minimizes
    (m : ℕ) (hm : 0 < m) (hm2 : 2 ≤ m) (f : ThresholdHilbert) (t : ℝ) :
    ‖hilbertOne - (f + dyadicCenteredRepairCoefficient m hm f •
      dyadicCenteredSeed m hm)‖ ^ 2 ≤
      ‖hilbertOne - (f + t • dyadicCenteredSeed m hm)‖ ^ 2 := by
  rw [dyadicCenteredSeed_optimal_repair_error m hm hm2,
    dyadicCenteredSeed_repair_complete_square m hm hm2]
  exact le_add_of_nonneg_right
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The same exact gain occurs wholly in the complementary energy. The
projected error is unchanged and every signed interaction is present. -/
theorem dyadicCenteredSeed_optimal_complementary_energy
    (m : ℕ) (hm : 0 < m) (hm2 : 2 ≤ m) (f : ThresholdHilbert) :
    ‖(f + dyadicCenteredRepairCoefficient m hm f • dyadicCenteredSeed m hm) -
      dyadicQuotientProjection
        (f + dyadicCenteredRepairCoefficient m hm f • dyadicCenteredSeed m hm)‖ ^ 2 =
      ‖f - dyadicQuotientProjection f‖ ^ 2 -
        (inner ℝ f (dyadicCenteredSeed m hm)) ^ 2 / ‖dyadicCenteredSeed m hm‖ ^ 2 := by
  rw [dyadicQuotientProjection_centered_repair]
  have heq : (f + dyadicCenteredRepairCoefficient m hm f • dyadicCenteredSeed m hm) -
      dyadicQuotientProjection f =
      (f - dyadicQuotientProjection f) +
        dyadicCenteredRepairCoefficient m hm f • dyadicCenteredSeed m hm := by abel
  rw [heq, norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_smul_right, ← inner_dyadicCenteredSeed_eq_complementary,
    dyadicCenteredRepairCoefficient]
  have hnorm : ‖dyadicCenteredSeed m hm‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (dyadicCenteredSeed_ne_zero m hm hm2)
  field_simp [hnorm]
  ring

/-- A simultaneous finite signed centered repair is a genuine two-seed lift. -/
theorem finite_centered_dyadic_repair_mem_twoSeed
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) (f : ThresholdHilbert)
    (hf : f ∈ dyadicTailTriadicSpan 1) :
    f + (∑ i ∈ s, c i • dyadicCenteredSeed (m i) (hm i)) ∈
      hilbertLegalSubspace ({2, 3} : Set ℕ) := by
  apply (hilbertLegalSubspace ({2, 3} : Set ℕ)).add_mem
  · exact dyadicTailTriadicSpan_le_hilbertLegalSubspace 1 _ (by simp) hf
  · apply (hilbertLegalSubspace ({2, 3} : Set ℕ)).sum_mem
    intro i hi
    exact (hilbertLegalSubspace ({2, 3} : Set ℕ)).smul_mem (c i)
      (dyadicCenteredSeed_mem_legalSubspace (m i) (hm i) _ (by simp))

/-- Simultaneous centered corrections preserve the exact projected target. -/
@[simp] theorem finite_centered_dyadic_repair_projection
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) (f : ThresholdHilbert) :
    dyadicQuotientProjection
      (f + ∑ i ∈ s, c i • dyadicCenteredSeed (m i) (hm i)) =
      dyadicQuotientProjection f := by
  simp only [map_add, map_sum, map_smul, dyadicQuotientProjection_centeredSeed,
    smul_zero, Finset.sum_const_zero, add_zero]

/-- The complete physical error of a simultaneous finite signed repair.
This identity retains the projected error, initial complementary energy,
every signed correlation with the lift, and every i,j repair interaction.
No Gram bound, convergence statement, or arithmetic cancellation is assumed. -/
theorem finite_centered_dyadic_repair_error_sq
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) (f : ThresholdHilbert) :
    ‖hilbertOne - (f + ∑ i ∈ s, c i • dyadicCenteredSeed (m i) (hm i))‖ ^ 2 =
      ‖hilbertOne - dyadicQuotientProjection f‖ ^ 2 +
      ‖f - dyadicQuotientProjection f‖ ^ 2 +
      2 * (∑ i ∈ s, c i * inner ℝ f (dyadicCenteredSeed (m i) (hm i))) +
      ∑ i ∈ s, ∑ j ∈ s, c i * c j *
        inner ℝ (dyadicCenteredSeed (m i) (hm i))
          (dyadicCenteredSeed (m j) (hm j)) := by
  have hsplit : ‖hilbertOne - f‖ ^ 2 =
      ‖hilbertOne - dyadicQuotientProjection f‖ ^ 2 +
        ‖f - dyadicQuotientProjection f‖ ^ 2 := by
    have h := dyadicQuotientProjection_pythagoras (hilbertOne - f)
    rw [map_sub, dyadicQuotientProjection_one] at h
    have heq : hilbertOne - f - (hilbertOne - dyadicQuotientProjection f) =
        -(f - dyadicQuotientProjection f) := by abel
    rw [heq, norm_neg] at h
    exact h
  have hzero : inner ℝ hilbertOne
      (∑ i ∈ s, c i • dyadicCenteredSeed (m i) (hm i)) = 0 := by
    simp only [inner_sum, real_inner_smul_right, inner_one_dyadicCenteredSeed,
      mul_zero, Finset.sum_const_zero]
  have hlin : inner ℝ f (∑ i ∈ s, c i • dyadicCenteredSeed (m i) (hm i)) =
      ∑ i ∈ s, c i * inner ℝ f (dyadicCenteredSeed (m i) (hm i)) := by
    simp only [inner_sum, real_inner_smul_right]
  have hgram : ‖∑ i ∈ s, c i • dyadicCenteredSeed (m i) (hm i)‖ ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j *
        inner ℝ (dyadicCenteredSeed (m i) (hm i))
          (dyadicCenteredSeed (m j) (hm j)) := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  have heq : hilbertOne - (f + ∑ i ∈ s, c i • dyadicCenteredSeed (m i) (hm i)) =
      (hilbertOne - f) - ∑ i ∈ s, c i • dyadicCenteredSeed (m i) (hm i) := by abel
  rw [heq, norm_sub_sq_real, inner_sub_left, hzero, hlin, hgram, hsplit]
  ring

end
end RiemannResearch.RH.Pareto
