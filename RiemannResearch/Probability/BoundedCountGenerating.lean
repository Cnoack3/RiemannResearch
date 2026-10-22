import RiemannResearch.Probability.DeterminantalBernoulliCount
import RiemannResearch.Probability.DeterminantalMoments
import Mathlib.Probability.Moments.Basic

/-!
# Exact concentration from a bounded count generating function

The Mellin finite projection process is the intended consumer.  These results
only concern an actual probability measure and a bounded natural-valued count;
they do not posit an infinite process or independence of spatial points.

The Chernoff argument is the exponential Markov inequality, supplied by
Mathlib's `measure_ge_le_exp_mul_mgf`. The product on the right is exact, so
each positive tilt may be chosen separately and optimized afterwards.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace RiemannResearch.Probability

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Y : Ω → ℕ} {n : ℕ} {p : ι → ℝ}

/-- A uniformly bounded natural count has every real exponential moment. -/
theorem bounded_nat_count_integrable_exp
    (hY : Measurable (fun ω => (Y ω : ℝ))) (hbound : ∀ ω, Y ω ≤ n)
    (t : ℝ) : Integrable (fun ω => Real.exp (t * (Y ω : ℝ))) μ := by
  refine (integrable_const (Real.exp (|t| * (n : ℝ)))).mono'
    ((measurable_const.mul hY).exp.aestronglyMeasurable) ?_
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    t * (Y ω : ℝ) ≤ |t| * (Y ω : ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self t) (Nat.cast_nonneg _)
    _ ≤ |t| * (n : ℝ) :=
      mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hbound ω)) (abs_nonneg _)

/-- The Bernoulli product PGF is also the exact moment generating function. -/
theorem count_mgf_eq_product
    (hpgf : ∀ z : ℝ, (∫ ω, z ^ Y ω ∂μ) = ∏ i, (1 - p i + z * p i))
    (t : ℝ) :
    mgf (fun ω => (Y ω : ℝ)) μ t =
      ∏ i, (1 - p i + Real.exp t * p i) := by
  have he (ω : Ω) : Real.exp (t * (Y ω : ℝ)) = (Real.exp t) ^ Y ω := by
    simpa [mul_comm] using Real.exp_nat_mul t (Y ω)
  simpa only [mgf, he] using hpgf (Real.exp t)

/-- Exact spectral-product upper-tail bound for every nonnegative tilt.
The endpoint `t=0` recovers the probability bound by one. -/
theorem count_upper_tail_le_product
    (hY : Measurable (fun ω => (Y ω : ℝ))) (hbound : ∀ ω, Y ω ≤ n)
    (hpgf : ∀ z : ℝ, (∫ ω, z ^ Y ω ∂μ) = ∏ i, (1 - p i + z * p i))
    (a t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | a ≤ (Y ω : ℝ)} ≤
      Real.exp (-t * a) * ∏ i, (1 - p i + Real.exp t * p i) := by
  have h := measure_ge_le_exp_mul_mgf (X := fun ω => (Y ω : ℝ))
    (μ := μ) a ht (bounded_nat_count_integrable_exp hY hbound t)
  rwa [count_mgf_eq_product hpgf t] at h

/-- Exact spectral-product lower-tail bound for every nonnegative tilt. -/
theorem count_lower_tail_le_product
    (hY : Measurable (fun ω => (Y ω : ℝ))) (hbound : ∀ ω, Y ω ≤ n)
    (hpgf : ∀ z : ℝ, (∫ ω, z ^ Y ω ∂μ) = ∏ i, (1 - p i + z * p i))
    (a t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | (Y ω : ℝ) ≤ a} ≤
      Real.exp (t * a) * ∏ i, (1 - p i + Real.exp (-t) * p i) := by
  have hInt : Integrable (fun ω => Real.exp (t * -(Y ω : ℝ))) μ := by
    simpa only [mul_neg, neg_mul] using
      bounded_nat_count_integrable_exp hY hbound (-t)
  have h := measure_ge_le_exp_mul_mgf (X := fun ω => -(Y ω : ℝ))
    (μ := μ) (-a) ht hInt
  have hevent : {ω | -a ≤ -(Y ω : ℝ)} = {ω | (Y ω : ℝ) ≤ a} := by
    ext ω
    simp
  have hmgf : mgf (fun ω => -(Y ω : ℝ)) μ t =
      mgf (fun ω => (Y ω : ℝ)) μ (-t) := by
    simp only [mgf, mul_neg, neg_mul]
  rw [hevent, hmgf, count_mgf_eq_product hpgf (-t)] at h
  simpa only [neg_mul_neg] using h


/-- Exact hole probability follows by evaluating the actual count PGF at zero. -/
theorem count_hole_probability
    (hY : Measurable Y)
    (hpgf : ∀ z : ℝ, (∫ ω, z ^ Y ω ∂μ) = ∏ i, (1 - p i + z * p i)) :
    μ.real {ω | Y ω = 0} = ∏ i, (1 - p i) := by
  have hz := hpgf 0
  have he : (fun ω => (0 : ℝ) ^ Y ω) =
      ({ω | Y ω = 0} : Set Ω).indicator 1 := by
    funext ω
    by_cases h : Y ω = 0 <;> simp [Set.indicator_apply, h, zero_pow]
  have hEvent : MeasurableSet {ω | Y ω = 0} := hY (measurableSet_singleton 0)
  rw [he] at hz
  have hint := integral_indicator_one (μ := μ) hEvent
  rw [hint] at hz
  simpa using hz

/-- The hole probability is no larger than the Poisson hole probability with
the same mean; the exact product is generally sharper. -/
theorem count_hole_probability_le_exp
    (hY : Measurable Y)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hpgf : ∀ z : ℝ, (∫ ω, z ^ Y ω ∂μ) = ∏ i, (1 - p i + z * p i)) :
    μ.real {ω | Y ω = 0} ≤ Real.exp (- ∑ i, p i) := by
  rw [count_hole_probability hY hpgf]
  calc
    (∏ i, (1 - p i)) ≤ ∏ i, Real.exp (-p i) := by
      apply Finset.prod_le_prod
      · intro i _
        exact sub_nonneg.mpr (hp i).2
      · intro i _
        have h := Real.add_one_le_exp (-p i)
        linarith
    _ = Real.exp (- ∑ i, p i) := by
      rw [← Real.exp_sum]
      simp

end RiemannResearch.Probability
