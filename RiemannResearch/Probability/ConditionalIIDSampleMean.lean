/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Probability.ConditionalIIDUniformMoments
import RiemannResearch.Probability.ConditionalVarianceError

/-!
# Conditional sample averages on the actual infinite mixture space

All global squared-error assertions have an explicit `MemLp ... 2` hypothesis.
Finite-fiber integrability is proved, not postulated. The conditional-mean
contribution is retained throughout.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Probability.ConditionalIID

/-- Every arithmetic observable has a second moment on every finite conditional fiber. -/
theorem uniform_memLp_two (k : ℕ) (F : ℕ → ℝ) : MemLp F 2 (uniformLaw k) :=
  (memLp_two_iff_integrable_sq
    (measurable_of_countable F).stronglyMeasurable.aestronglyMeasurable).2
      (uniform_integrable k (fun n => F n ^ 2))

theorem path_coordinate_memLp_two (k i : ℕ) (F : ℕ → ℝ) :
    MemLp (fun x : Path => F (x i)) 2 (pathLaw k) :=
  (uniform_memLp_two k F).comp_measurePreserving
    (measurePreserving_eval_infinitePi (fun _ : ℕ => uniformLaw k) i)

theorem path_coordinate_variance (k i : ℕ) (F : ℕ → ℝ) :
    variance (fun x : Path => F (x i)) (pathLaw k) = variance F (uniformLaw k) := by
  rw [variance_eq_sub (path_coordinate_memLp_two k i F),
    variance_eq_sub (uniform_memLp_two k F)]
  simp only [Pi.pow_apply, path_integral_coordinate, uniform_integral]
  rw [path_integral_coordinate k i (fun n => F n ^ 2)]

/-- The average uses one deterministic arithmetic function on every sampled coordinate. -/
def pathAverage (F : ℕ → ℝ) (r : ℕ) : Path → ℝ :=
  (r : ℝ)⁻¹ • ∑ i ∈ Finset.range r, (fun x : Path => F (x i))

@[simp] theorem pathAverage_apply (F : ℕ → ℝ) (r : ℕ) (x : Path) :
    pathAverage F r x = (r : ℝ)⁻¹ * ∑ i ∈ Finset.range r, F (x i) := by
  simp [pathAverage, Finset.sum_apply, smul_eq_mul]

theorem pathAverage_measurable (F : ℕ → ℝ) (r : ℕ) : Measurable (pathAverage F r) := by
  have hF : Measurable F := measurable_of_countable _
  change Measurable (fun x : Path => pathAverage F r x)
  simp only [pathAverage_apply]
  fun_prop

theorem pathAverage_memLp_two (k : ℕ) (F : ℕ → ℝ) (r : ℕ) :
    MemLp (pathAverage F r) 2 (pathLaw k) := by
  change MemLp (fun x : Path => pathAverage F r x) 2 (pathLaw k)
  simp only [pathAverage_apply]
  exact (memLp_finset_sum (Finset.range r) (fun i _ => path_coordinate_memLp_two k i F)).const_mul
      ((r : ℝ)⁻¹)

theorem pathAverage_mean (k : ℕ) (F : ℕ → ℝ) (r : ℕ) (hr : 0 < r) :
    (∫ x, pathAverage F r x ∂pathLaw k) = cesaro F (k + 1) := by
  simp only [pathAverage_apply]
  rw [integral_const_mul, integral_finset_sum]
  · simp only [path_integral_coordinate, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
    field_simp
  · intro i hi
    exact (path_coordinate_memLp_two k i F).integrable one_le_two

/-- Conditional independence supplies exactly the usual 1/r variance factor within each fiber. -/
theorem pathAverage_variance (k : ℕ) (F : ℕ → ℝ) (r : ℕ) (hr : 0 < r) :
    variance (pathAverage F r) (pathLaw k) = variance F (uniformLaw k) / (r : ℝ) := by
  rw [pathAverage, variance_smul, IndepFun.variance_sum
    (fun i _ => path_coordinate_memLp_two k i F)
    (fun i _ j _ hij => (iIndepFun_infinitePi
      (P := fun _ : ℕ => uniformLaw k) (fun _ => measurable_of_countable F)).indepFun hij)]
  simp only [path_coordinate_variance, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  field_simp

/-- The actual conditional-fiber squared error, with its bias term intact. -/
theorem pathAverage_error (k : ℕ) (F : ℕ → ℝ) (r : ℕ) (hr : 0 < r) (c : ℝ) :
    (∫ x, (c - pathAverage F r x) ^ 2 ∂pathLaw k) =
      (c - cesaro F (k + 1)) ^ 2 + variance F (uniformLaw k) / (r : ℝ) := by
  rw [integral_const_sub_sq_eq_bias_sq_add_variance (pathAverage_memLp_two k F r) c,
    pathAverage_mean k F r hr, pathAverage_variance k F r hr]

/-- Global L2 integrability is not inferred from finite-fiber integrability. -/
theorem observationAverage_memLp_two (F : ℕ → ℝ) (r : ℕ)
    (hF : ∀ i, MemLp (fun ω => F (coordinate i ω)) 2 probability) :
    MemLp (fun ω : Omega => pathAverage F r ω.2) 2 probability := by
  simpa only [pathAverage, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, coordinate] using
    (memLp_finset_sum (Finset.range r) (fun i _ => hF i)).const_mul ((r : ℝ)⁻¹)

/-- An actual conditional-expectation identity for averages, not a finite weighted surrogate. -/
theorem conditional_average_mean (F : ℕ → ℝ) (r : ℕ) (hr : 0 < r)
    (hF : ∀ i, MemLp (fun ω => F (coordinate i ω)) 2 probability) :
    probability[(fun ω : Omega => pathAverage F r ω.2) | latentSigma] =ᵐ[probability]
      (fun ω => cesaro F (endpoint ω)) := by
  have h := conditional_path_expectation (pathAverage F r)
    (pathAverage_measurable F r).stronglyMeasurable
    ((observationAverage_memLp_two F r hF).integrable one_le_two)
  filter_upwards [h] with ω hω
  rw [hω, pathAverage_mean _ F r hr]
  rfl

/-- Actual conditional iid sample-mean squared error on the common probability space. -/
theorem conditional_average_error (F : ℕ → ℝ) (r : ℕ) (hr : 0 < r) (c : ℝ)
    (hF : ∀ i, MemLp (fun ω => F (coordinate i ω)) 2 probability) :
    probability[(fun ω : Omega => (c - pathAverage F r ω.2) ^ 2) | latentSigma]
      =ᵐ[probability] (fun ω => (c - cesaro F (endpoint ω)) ^ 2 +
        variance F (uniformLaw (latentIndex ω)) / (r : ℝ)) := by
  have hm : Measurable (fun x : Path => (c - pathAverage F r x) ^ 2) := by
    exact (measurable_const.sub (pathAverage_measurable F r)).pow_const 2
  have hi := ((memLp_const c).sub (observationAverage_memLp_two F r hF)).integrable_sq
  have h := conditional_path_expectation (fun x => (c - pathAverage F r x) ^ 2)
    hm.stronglyMeasurable hi
  filter_upwards [h] with ω hω
  rw [hω, pathAverage_error _ F r hr c]
  rfl

/-- The conditional fiber variance is an explicit arithmetic expression. -/
theorem uniform_variance_formula (k : ℕ) (F : ℕ → ℝ) :
    variance F (uniformLaw k) = cesaro (fun n => F n ^ 2) (k + 1) -
      cesaro F (k + 1) ^ 2 := by
  rw [variance_eq_sub (uniform_memLp_two k F)]
  simp only [Pi.pow_apply, uniform_integral]

/-- Integrability of the conditional-mean error follows from conditional L2 contraction. -/
theorem conditionalMean_error_integrable (F : ℕ → ℝ) (c : ℝ)
    (hF : MemLp (fun ω => F (coordinate 0 ω)) 2 probability) :
    Integrable (fun ω => (c - cesaro F (endpoint ω)) ^ 2) probability := by
  have hce := conditional_coordinate_expectation 0 F (hF.integrable one_le_two)
  have hi := ((memLp_const c).sub (hF.condExp (m := latentSigma) one_le_two)).integrable_sq
  apply hi.congr
  filter_upwards [hce] with ω hω
  change (c - probability[(fun ω => F (coordinate 0 ω)) | latentSigma] ω) ^ 2 = _
  rw [hω]

/-- The conditional-mean square is globally integrable, not just finite on each fiber. -/
theorem conditionalMean_sq_integrable (F : ℕ → ℝ)
    (hF : MemLp (fun ω => F (coordinate 0 ω)) 2 probability) :
    Integrable (fun ω => cesaro F (endpoint ω) ^ 2) probability := by
  simpa only [zero_sub, neg_sq] using conditionalMean_error_integrable F 0 hF

/-- The mixture of finite-fiber variances is integrable under the global L2 hypothesis. -/
theorem fiberVariance_integrable (F : ℕ → ℝ)
    (hF : MemLp (fun ω => F (coordinate 0 ω)) 2 probability) :
    Integrable (fun ω => variance F (uniformLaw (latentIndex ω))) probability := by
  have hce := conditional_coordinate_expectation 0 (fun n => F n ^ 2) hF.integrable_sq
  have h2 : Integrable (fun ω => cesaro (fun n => F n ^ 2) (endpoint ω)) probability :=
    (integrable_condExp (μ := probability) (m := latentSigma)
      (f := fun ω => F (coordinate 0 ω) ^ 2)).congr hce
  apply (h2.sub (conditionalMean_sq_integrable F hF)).congr
  exact ae_of_all _ (fun ω => (uniform_variance_formula (latentIndex ω) F).symm)

/-- Full unconditional conditional-iid sample error, with both integrable terms retained. -/
theorem average_error (F : ℕ → ℝ) (r : ℕ) (hr : 0 < r) (c : ℝ)
    (hF : ∀ i, MemLp (fun ω => F (coordinate i ω)) 2 probability) :
    (∫ ω : Omega, (c - pathAverage F r ω.2) ^ 2 ∂probability) =
      (∫ ω, (c - cesaro F (endpoint ω)) ^ 2 ∂probability) +
      (∫ ω, variance F (uniformLaw (latentIndex ω)) ∂probability) / (r : ℝ) := by
  calc
    _ = ∫ ω, probability[(fun ω : Omega => (c - pathAverage F r ω.2) ^ 2) |
        latentSigma] ω ∂probability := (integral_condExp latentSigma_le).symm
    _ = ∫ ω, ((c - cesaro F (endpoint ω)) ^ 2 +
        variance F (uniformLaw (latentIndex ω)) / (r : ℝ)) ∂probability :=
      integral_congr_ae (conditional_average_error F r hr c hF)
    _ = _ := by
      rw [integral_add (conditionalMean_error_integrable F c (hF 0))
        ((fiberVariance_integrable F (hF 0)).div_const (r : ℝ)), integral_div]

/-- More samples cannot remove the conditional-mean error. -/
theorem conditionalMean_error_le_average_error (F : ℕ → ℝ) (r : ℕ) (hr : 0 < r) (c : ℝ)
    (hF : ∀ i, MemLp (fun ω => F (coordinate i ω)) 2 probability) :
    (∫ ω, (c - cesaro F (endpoint ω)) ^ 2 ∂probability) ≤
      ∫ ω : Omega, (c - pathAverage F r ω.2) ^ 2 ∂probability := by
  rw [average_error F r hr c hF]
  apply le_add_of_nonneg_right
  apply div_nonneg
  · exact integral_nonneg (fun ω => variance_nonneg F (uniformLaw (latentIndex ω)))
  · positivity

end RiemannResearch.Probability.ConditionalIID
