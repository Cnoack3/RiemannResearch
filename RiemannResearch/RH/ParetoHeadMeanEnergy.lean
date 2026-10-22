import RiemannResearch.RH.ParetoGibbsTailBasis

/-!
# Exact head-and-mean energy on the complete Pareto Hilbert space

Source: user-provided `ParetoCovarianceRepairReport_Advanced_2026-09-08.md`,
Section 4, and `tail_projection.md`, Section 3. The head contains physical
coordinates 1,...,N; the existing Gibbs coordinates are indexed from zero.
The minimizer and the complete nonnegative remainder are actual Hilbert vectors.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- Retain the first N physical coordinates. -/
def paretoHead (N : ℕ) (f : ThresholdHilbert) : ThresholdHilbert :=
  ∑ k ∈ Finset.range N, hilbertGibbsPhysical f k • paretoPointHilbert k

/-- Indicator of the entire infinite tail above physical coordinate N. -/
def paretoTail (N : ℕ) : ThresholdHilbert :=
  hilbertOne - ∑ k ∈ Finset.range N, paretoPointHilbert k

def paretoHeadMean (N : ℕ) (f : ThresholdHilbert) : ℝ :=
  ∑ k ∈ Finset.range N, paretoWeight k * hilbertGibbsPhysical f k

private theorem physical_sum_head (s : Finset ℕ) (g : ℕ → ThresholdHilbert) (k : ℕ) :
    hilbertGibbsPhysical (∑ n ∈ s, g n) k = ∑ n ∈ s, hilbertGibbsPhysical (g n) k := by
  change hilbertSequenceLinear (∑ n ∈ s, g n) (k+1) =
    ∑ n ∈ s, hilbertSequenceLinear (g n) (k+1)
  rw [map_sum]
  simp only [Finset.sum_apply]

private theorem physical_sub_head (f g : ThresholdHilbert) (k : ℕ) :
    hilbertGibbsPhysical (f-g) k = hilbertGibbsPhysical f k - hilbertGibbsPhysical g k := by
  simp [hilbertGibbsPhysical, sub_div]

@[simp] theorem paretoHead_physical (N : ℕ) (f : ThresholdHilbert) (k : ℕ) :
    hilbertGibbsPhysical (paretoHead N f) k = if k < N then hilbertGibbsPhysical f k else 0 := by
  unfold paretoHead
  rw [physical_sum_head]
  simp only [hilbertGibbsPhysical_smul, hilbertGibbsPhysical_paretoPoint,
    mul_ite, mul_one, mul_zero]
  simp

@[simp] theorem paretoTail_physical (N k : ℕ) :
    hilbertGibbsPhysical (paretoTail N) k = if k < N then 0 else 1 := by
  unfold paretoTail
  rw [physical_sub_head, physical_sum_head, hilbertGibbs_one_physical]
  simp only [hilbertGibbsPhysical_paretoPoint]
  simp
  split_ifs <;> norm_num

 theorem paretoHead_inner (N : ℕ) (f g : ThresholdHilbert) :
    inner ℝ f (paretoHead N g) =
      ∑ k ∈ Finset.range N, paretoWeight k *
        (hilbertGibbsPhysical f k * hilbertGibbsPhysical g k) := by
  unfold paretoHead
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [real_inner_smul_right, inner_paretoPoint]
  ring

 theorem paretoHead_inner_one (N : ℕ) (f : ThresholdHilbert) :
    inner ℝ (paretoHead N f) hilbertOne = paretoHeadMean N f := by
  rw [real_inner_comm, paretoHead_inner]
  simp only [hilbertGibbs_one_physical, one_mul, paretoHeadMean]

 theorem paretoHead_norm_sq (N : ℕ) (f : ThresholdHilbert) :
    ‖paretoHead N f‖ ^ 2 =
      ∑ k ∈ Finset.range N, paretoWeight k * hilbertGibbsPhysical f k ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, paretoHead_inner]
  apply Finset.sum_congr rfl
  intro k hk
  rw [paretoHead_physical, if_pos (Finset.mem_range.mp hk), pow_two]

 theorem paretoTail_inner (N : ℕ) (f : ThresholdHilbert) :
    inner ℝ f (paretoTail N) = inner ℝ f hilbertOne - paretoHeadMean N f := by
  unfold paretoTail paretoHeadMean
  rw [inner_sub_right, inner_sum]
  simp only [inner_paretoPoint]

 theorem paretoTail_inner_one (N : ℕ) :
    inner ℝ (paretoTail N) hilbertOne = 1 / ((N : ℝ)+1) := by
  unfold paretoTail
  rw [inner_sub_left, sum_inner, real_inner_self_eq_norm_sq, hilbertOne_norm_sq]
  simp only [paretoPoint_inner_one]
  rw [paretoWeight_partial_sum]
  ring

 theorem paretoTail_head_orthogonal (N : ℕ) (f : ThresholdHilbert) :
    inner ℝ (paretoTail N) (paretoHead N f) = 0 := by
  rw [paretoHead_inner]
  apply Finset.sum_eq_zero
  intro k hk
  rw [paretoTail_physical, if_pos (Finset.mem_range.mp hk), zero_mul, mul_zero]

 theorem paretoTail_norm_sq (N : ℕ) : ‖paretoTail N‖ ^ 2 = 1 / ((N : ℝ)+1) := by
  rw [← real_inner_self_eq_norm_sq, paretoTail_inner, paretoTail_inner_one]
  have hz : paretoHeadMean N (paretoTail N) = 0 := by
    unfold paretoHeadMean
    apply Finset.sum_eq_zero
    intro k hk
    rw [paretoTail_physical, if_pos (Finset.mem_range.mp hk), mul_zero]
  rw [hz, sub_zero]

/-- The unique universal completion with a constant tail and the original mean. -/
def paretoHeadMeanMinimizer (N : ℕ) (f : ThresholdHilbert) : ThresholdHilbert :=
  paretoHead N f + (((N : ℝ)+1) * (inner ℝ f hilbertOne - paretoHeadMean N f)) • paretoTail N

 theorem paretoHeadMeanMinimizer_head (N : ℕ) (f : ThresholdHilbert)
    (k : ℕ) (hk : k < N) :
    hilbertGibbsPhysical (paretoHeadMeanMinimizer N f) k = hilbertGibbsPhysical f k := by
  unfold paretoHeadMeanMinimizer
  simp only [hilbertGibbsPhysical_add, hilbertGibbsPhysical_smul,
    paretoHead_physical, paretoTail_physical, if_pos hk, if_pos hk, mul_zero, add_zero]

 theorem paretoHeadMeanMinimizer_tail (N : ℕ) (f : ThresholdHilbert)
    (k : ℕ) (hk : N ≤ k) :
    hilbertGibbsPhysical (paretoHeadMeanMinimizer N f) k =
      ((N : ℝ)+1) * (inner ℝ f hilbertOne - paretoHeadMean N f) := by
  unfold paretoHeadMeanMinimizer
  simp only [hilbertGibbsPhysical_add, hilbertGibbsPhysical_smul,
    paretoHead_physical, paretoTail_physical, if_neg (not_lt.mpr hk),
    if_neg (not_lt.mpr hk), mul_one, zero_add]

 theorem paretoHeadMeanMinimizer_mean (N : ℕ) (f : ThresholdHilbert) :
    inner ℝ (paretoHeadMeanMinimizer N f) hilbertOne = inner ℝ f hilbertOne := by
  unfold paretoHeadMeanMinimizer
  rw [inner_add_left, real_inner_smul_left, paretoHead_inner_one, paretoTail_inner_one]
  have hN : (N : ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

 theorem paretoHeadMeanMinimizer_norm_sq (N : ℕ) (f : ThresholdHilbert) :
    ‖paretoHeadMeanMinimizer N f‖ ^ 2 =
      (∑ k ∈ Finset.range N, paretoWeight k * hilbertGibbsPhysical f k ^ 2) +
      ((N : ℝ)+1) * (inner ℝ f hilbertOne - paretoHeadMean N f)^2 := by
  unfold paretoHeadMeanMinimizer
  rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_add_right, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_right, real_inner_smul_right, paretoTail_head_orthogonal,
    real_inner_comm (paretoTail N) (paretoHead N f), paretoTail_head_orthogonal,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    paretoHead_norm_sq, paretoTail_norm_sq]
  have hN : (N : ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

 theorem paretoHeadMeanMinimizer_remainder_orthogonal (N : ℕ) (f : ThresholdHilbert) :
    inner ℝ (f - paretoHeadMeanMinimizer N f) (paretoHeadMeanMinimizer N f) = 0 := by
  have hhead : inner ℝ (f - paretoHeadMeanMinimizer N f) (paretoHead N f) = 0 := by
    rw [paretoHead_inner]
    apply Finset.sum_eq_zero
    intro k hk
    rw [physical_sub_head, paretoHeadMeanMinimizer_head N f k (Finset.mem_range.mp hk),
      sub_self, zero_mul, mul_zero]
  have htail : inner ℝ (f - paretoHeadMeanMinimizer N f) (paretoTail N) = 0 := by
    rw [paretoTail_inner, inner_sub_left, paretoHeadMeanMinimizer_mean, sub_self]
    have hz : paretoHeadMean N (f - paretoHeadMeanMinimizer N f) = 0 := by
      unfold paretoHeadMean
      apply Finset.sum_eq_zero
      intro k hk
      rw [physical_sub_head, paretoHeadMeanMinimizer_head N f k (Finset.mem_range.mp hk),
        sub_self, mul_zero]
    rw [hz, sub_self]
  conv_lhs => rhs; unfold paretoHeadMeanMinimizer
  rw [inner_add_right, real_inner_smul_right, hhead, htail, mul_zero, add_zero]

/-- The full infinite norm equals the sharp head-and-mean cost plus the exact
nonnegative remaining tail energy. No boundedness hypothesis is required. -/
 theorem paretoHeadMean_energy_identity (N : ℕ) (f : ThresholdHilbert) :
    ‖f‖^2 =
      (∑ k ∈ Finset.range N, paretoWeight k * hilbertGibbsPhysical f k ^ 2) +
      ((N : ℝ)+1) * (inner ℝ f hilbertOne - paretoHeadMean N f)^2 +
      ‖f - paretoHeadMeanMinimizer N f‖^2 := by
  have h := paretoHeadMeanMinimizer_remainder_orthogonal N f
  have h' : inner ℝ (paretoHeadMeanMinimizer N f)
      (f - paretoHeadMeanMinimizer N f) = 0 := by rw [real_inner_comm]; exact h
  have he : f = paretoHeadMeanMinimizer N f +
      (f - paretoHeadMeanMinimizer N f) := by abel
  conv_lhs => rw [he]
  rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_add_right, h, h', real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, paretoHeadMeanMinimizer_norm_sq]
  ring

 theorem paretoHeadMean_energy_lower (N : ℕ) (f : ThresholdHilbert) :
    (∑ k ∈ Finset.range N, paretoWeight k * hilbertGibbsPhysical f k ^ 2) +
      ((N : ℝ)+1) * (inner ℝ f hilbertOne - paretoHeadMean N f)^2 ≤ ‖f‖^2 := by
  rw [paretoHeadMean_energy_identity N f]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Matching the constant through N with zero total mean costs at least N. -/
 theorem paretoHead_one_mean_zero_cost (N : ℕ) (f : ThresholdHilbert)
    (hhead : ∀ k < N, hilbertGibbsPhysical f k = 1)
    (hm : inner ℝ f hilbertOne = 0) : (N : ℝ) ≤ ‖f‖^2 := by
  have h := paretoHeadMean_energy_lower N f
  have hs : (∑ k ∈ Finset.range N, paretoWeight k * hilbertGibbsPhysical f k ^ 2) =
      1 - 1 / ((N : ℝ)+1) := by
    trans ∑ k ∈ Finset.range N, paretoWeight k
    · apply Finset.sum_congr rfl
      intro k hk
      rw [hhead k (Finset.mem_range.mp hk)]
      ring
    · exact paretoWeight_partial_sum N
  have ha : paretoHeadMean N f = 1 - 1 / ((N : ℝ)+1) := by
    unfold paretoHeadMean
    trans ∑ k ∈ Finset.range N, paretoWeight k
    · apply Finset.sum_congr rfl
      intro k hk
      rw [hhead k (Finset.mem_range.mp hk), mul_one]
    · exact paretoWeight_partial_sum N
  rw [hs, ha, hm] at h
  have he : 1 - 1 / ((N : ℝ)+1) +
      ((N : ℝ)+1) * (0 - (1 - 1 / ((N : ℝ)+1)))^2 = N := by
    have hN : (N : ℝ)+1 ≠ 0 := by positivity
    field_simp
    ring
  rwa [he] at h

end
end RiemannResearch.RH.Pareto
