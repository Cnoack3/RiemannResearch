import RiemannResearch.RH.ParetoFiniteSieveBoundary
import RiemannResearch.RH.ParetoSignedTailRegularity
import RiemannResearch.RH.ThresholdHilbertMean

/-!
# Exact Hilbert norm of the signed sieve boundary

Source: Christian Noack's
`RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`,
Section 27, equations (27.3)--(27.5). The representing kernel contains the
whole signed sieve before squaring. Cauchy--Schwarz uses the actual physical
tail of the candidate annihilator, preserving every covariance in the kernel.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Physical cutoff of a sequence, with no alteration of its surviving tail. -/
def paretoTailSequence (h : ℕ → ℝ) (K k : ℕ) : ℝ :=
  if K < k then h k else 0

theorem paretoTailSequence_square_summable {h : ℕ → ℝ}
    (hs : Summable (fun k => positiveWeight k * h k ^ 2)) (K : ℕ) :
    Summable (fun k => positiveWeight k * paretoTailSequence h K k ^ 2) := by
  apply hs.of_norm_bounded
  intro k
  unfold paretoTailSequence
  split_ifs
  · rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))]
  · simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, norm_zero]
    exact mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _)

def paretoTailHilbert (h : ThresholdHilbert) (K : ℕ) : ThresholdHilbert :=
  sequenceHilbert (paretoTailSequence (hilbertSequence h) K)
    (paretoTailSequence_square_summable (hilbertSequence_square_summable h) K)

@[simp] theorem paretoTailHilbert_sequence (h : ThresholdHilbert) (K : ℕ) :
    hilbertSequence (paretoTailHilbert h K) = paretoTailSequence (hilbertSequence h) K := by
  apply hilbertSequence_sequenceHilbert
  simp [paretoTailSequence]

private theorem tsum_eq_shift_of_zero_prefix {f : ℕ → ℝ}
    (hf : Summable f) (K : ℕ) (hz : ∀ k, k ≤ K → f k = 0) :
    (∑' k, f k) = ∑' j, f (j + (K + 1)) := by
  have he := hf.sum_add_tsum_nat_add (K + 1)
  have hzero : (∑ k ∈ Finset.range (K + 1), f k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact hz k (by have := Finset.mem_range.mp hk; omega)
  rw [hzero, zero_add] at he
  exact he.symm

theorem paretoTailHilbert_norm_sq (h : ThresholdHilbert) (K : ℕ) :
    ‖paretoTailHilbert h K‖ ^ 2 = signedTailEnergy (hilbertSequence h) (K + 1) := by
  rw [hilbert_norm_weighted_sq, paretoTailHilbert_sequence]
  rw [tsum_eq_shift_of_zero_prefix
    (paretoTailSequence_square_summable (hilbertSequence_square_summable h) K) K
      (fun k hk => by simp [paretoTailSequence, Nat.not_lt.mpr hk])]
  unfold signedTailEnergy
  apply tsum_congr
  intro j
  simp [paretoTailSequence, show K < j + (K + 1) by omega]

/-- The exact signed boundary kernel on physical coordinates. -/
def paretoBoundaryKernel (g : ℕ → ℝ) (K k : ℕ) : ℝ :=
  if K < k then g K - g k else 0

theorem paretoBoundaryKernel_abs_le {g : ℕ → ℝ} {C : ℝ}
    (hg : ∀ k, |g k| ≤ C) (K k : ℕ) :
    |paretoBoundaryKernel g K k| ≤ 2 * C := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hg 0)
  unfold paretoBoundaryKernel
  split_ifs
  · have ht := (abs_sub (g K) (g k)).trans (add_le_add (hg K) (hg k))
    linarith
  · simp only [abs_zero]
    positivity

theorem paretoBoundaryKernel_square_summable {g : ℕ → ℝ} {C : ℝ}
    (hg : ∀ k, |g k| ≤ C) (K : ℕ) :
    Summable (fun k => positiveWeight k * paretoBoundaryKernel g K k ^ 2) := by
  apply weighted_summable_of_bounded (C := (2 * C) ^ 2)
  intro k
  rw [abs_of_nonneg (sq_nonneg _)]
  have hb := paretoBoundaryKernel_abs_le hg K k
  have hC : 0 ≤ C := (abs_nonneg _).trans (hg 0)
  nlinarith [sq_abs (paretoBoundaryKernel g K k), abs_nonneg (paretoBoundaryKernel g K k)]

def paretoBoundaryHilbert (g : ℕ → ℝ) {C : ℝ}
    (hg : ∀ k, |g k| ≤ C) (K : ℕ) : ThresholdHilbert :=
  sequenceHilbert (paretoBoundaryKernel g K)
    (paretoBoundaryKernel_square_summable hg K)

@[simp] theorem paretoBoundaryHilbert_sequence {g : ℕ → ℝ} {C : ℝ}
    (hg : ∀ k, |g k| ≤ C) (K : ℕ) :
    hilbertSequence (paretoBoundaryHilbert g hg K) = paretoBoundaryKernel g K := by
  apply hilbertSequence_sequenceHilbert
  simp [paretoBoundaryKernel]

/-- Equation (27.4): one full signed square, with no dropped mixed terms. -/
def paretoBoundaryNormSq (g : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑' j, positiveWeight (j + (K + 1)) * (g K - g (j + (K + 1))) ^ 2

theorem paretoBoundaryNormSq_nonneg (g : ℕ → ℝ) (K : ℕ) :
    0 ≤ paretoBoundaryNormSq g K := by
  apply tsum_nonneg
  intro j
  exact mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _)

theorem paretoBoundaryHilbert_norm_sq {g : ℕ → ℝ} {C : ℝ}
    (hg : ∀ k, |g k| ≤ C) (K : ℕ) :
    ‖paretoBoundaryHilbert g hg K‖ ^ 2 = paretoBoundaryNormSq g K := by
  rw [hilbert_norm_weighted_sq, paretoBoundaryHilbert_sequence]
  rw [tsum_eq_shift_of_zero_prefix (paretoBoundaryKernel_square_summable hg K) K
    (fun k hk => by simp [paretoBoundaryKernel, Nat.not_lt.mpr hk])]
  unfold paretoBoundaryNormSq
  apply tsum_congr
  intro j
  simp [paretoBoundaryKernel, show K < j + (K + 1) by omega]

theorem paretoBoundaryHilbert_norm {g : ℕ → ℝ} {C : ℝ}
    (hg : ∀ k, |g k| ≤ C) (K : ℕ) :
    ‖paretoBoundaryHilbert g hg K‖ = Real.sqrt (paretoBoundaryNormSq g K) := by
  rw [← paretoBoundaryHilbert_norm_sq hg K, Real.sqrt_sq (norm_nonneg _)]

/-- The boundary is exactly the functional represented by the signed kernel. -/
theorem paretoFiniteBoundary_eq_inner (h : ThresholdHilbert) {g : ℕ → ℝ} {C : ℝ}
    (hg : ∀ k, |g k| ≤ C) (K : ℕ) :
    paretoFiniteBoundary (hilbertSequence h) g K =
      inner ℝ h (paretoBoundaryHilbert g hg K) := by
  rw [hilbert_inner_weighted, paretoBoundaryHilbert_sequence]
  unfold paretoInner
  have hp := weighted_product_summable_of_square_of_bounded
    (hilbertSequence_square_summable h) (paretoBoundaryKernel_abs_le hg K)
  rw [tsum_eq_shift_of_zero_prefix hp K
    (fun k hk => by simp [paretoBoundaryKernel, Nat.not_lt.mpr hk])]
  unfold paretoFiniteBoundary
  apply tsum_congr
  intro j
  simp only [paretoBoundaryKernel, show K < j + (K + 1) by omega, ite_true,
    signedCoefficient]
  ring

theorem paretoFiniteBoundary_eq_tail_inner (h : ThresholdHilbert)
    {g : ℕ → ℝ} {C : ℝ} (hg : ∀ k, |g k| ≤ C) (K : ℕ) :
    paretoFiniteBoundary (hilbertSequence h) g K =
      inner ℝ (paretoTailHilbert h K) (paretoBoundaryHilbert g hg K) := by
  rw [← paretoFiniteBoundary_eq_inner (paretoTailHilbert h K) hg K,
    paretoTailHilbert_sequence]
  unfold paretoFiniteBoundary
  apply tsum_congr
  intro j
  simp [signedCoefficient, paretoTailSequence, show K < j + (K + 1) by omega]

/-- Equation (27.5), with the actual tail norm and exact signed kernel norm. -/
theorem paretoFiniteBoundary_abs_le (h : ThresholdHilbert)
    {g : ℕ → ℝ} {C : ℝ} (hg : ∀ k, |g k| ≤ C) (K : ℕ) :
    |paretoFiniteBoundary (hilbertSequence h) g K| ≤
      ‖paretoTailHilbert h K‖ * Real.sqrt (paretoBoundaryNormSq g K) := by
  rw [paretoFiniteBoundary_eq_tail_inner h hg K, ← paretoBoundaryHilbert_norm hg K]
  exact abs_real_inner_le_norm _ _

/-- The full-space bound is attained at the representing kernel. This proves
sharpness on the Hilbert space, without asserting attainment in the annihilator. -/
theorem paretoFiniteBoundary_at_kernel {g : ℕ → ℝ} {C : ℝ}
    (hg : ∀ k, |g k| ≤ C) (K : ℕ) :
    paretoFiniteBoundary (hilbertSequence (paretoBoundaryHilbert g hg K)) g K =
      paretoBoundaryNormSq g K := by
  rw [paretoFiniteBoundary_eq_inner (paretoBoundaryHilbert g hg K) hg K,
    real_inner_self_eq_norm_sq,
    paretoBoundaryHilbert_norm_sq hg K]

end
end RiemannResearch.RH.Pareto
