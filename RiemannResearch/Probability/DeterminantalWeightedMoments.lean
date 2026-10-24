import RiemannResearch.Probability.DeterminantalMoments

/-!
# Signed weighted determinantal linear statistics

Source: sixth transfer program, 24 October 2026. The unweighted count owner is
extended to arbitrary real weights, retaining the complete signed covariance
matrix. No kernel symmetry or nonnegativity of weights is assumed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace RiemannResearch.Probability.DPP

variable {ι α Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → Set α} {K : α → α → ℝ}

def linearStatistic (X : Ω → Set α) (e : ι → α) (a : ι → ℝ) (ω : Ω) : ℝ :=
  ∑ i, a i * occupancyIndicator X (e i) ω

theorem IsDPP.linearStatistic_integrable (h : IsDPP μ X K) (e : ι → α) (a : ι → ℝ) :
    Integrable (linearStatistic X e a) μ :=
  integrable_finsetSum Finset.univ (fun i _ =>
    (h.occupancyIndicator_integrable (e i)).const_mul (a i))

theorem IsDPP.linearStatistic_memLp (h : IsDPP μ X K) (e : ι → α) (a : ι → ℝ) :
    MemLp (linearStatistic X e a) 2 μ := by
  apply memLp_finsetSum Finset.univ
  intro i _
  exact (MemLp.indicator (h.measurable_occupancy (e i))
    (memLp_const (1 : ℝ))).const_mul (a i)

theorem IsDPP.expected_linearStatistic (h : IsDPP μ X K) (e : ι → α) (a : ι → ℝ) :
    (∫ ω, linearStatistic X e a ω ∂μ) = ∑ i, a i * K (e i) (e i) := by
  simp only [linearStatistic]
  rw [integral_finsetSum Finset.univ
    (fun i _ => (h.occupancyIndicator_integrable (e i)).const_mul (a i))]
  simp_rw [integral_const_mul, h.integral_occupancyIndicator]

private theorem linearStatistic_product (e : ι → α) (a b : ι → ℝ) (ω : Ω) :
    linearStatistic X e a ω * linearStatistic X e b ω =
      ∑ i, ∑ j, (a i * b j) * (occupancyIndicator X (e i) ω *
        occupancyIndicator X (e j) ω) := by
  unfold linearStatistic
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem IsDPP.linearStatistic_product_integrable (h : IsDPP μ X K)
    (e : ι → α) (a b : ι → ℝ) :
    Integrable (fun ω => linearStatistic X e a ω * linearStatistic X e b ω) μ := by
  simp_rw [linearStatistic_product]
  exact integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      (h.occupancy_product_integrable (e i) (e j)).const_mul (a i * b j)))

/-- Arbitrary signed weights and all diagonal/off-diagonal mixed moments. -/
theorem IsDPP.linearStatistic_product_moment (h : IsDPP μ X K)
    (e : ι ↪ α) (a b : ι → ℝ) :
    (∫ ω, linearStatistic X e a ω * linearStatistic X e b ω ∂μ) =
      ∑ i, ∑ j, (a i * b j) *
        (K (e i) (e i) * K (e j) (e j) - K (e i) (e j) * K (e j) (e i) +
          if i = j then K (e i) (e i) else 0) := by
  simp_rw [linearStatistic_product]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      (h.occupancy_product_integrable (e i) (e j)).const_mul (a i * b j)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ =>
    (h.occupancy_product_integrable (e i) (e j)).const_mul (a i * b j))]
  simp_rw [integral_const_mul, h.integral_occupancy_product e]

/-- The exact covariance keeps every signed cross term. -/
theorem IsDPP.linearStatistic_covariance (h : IsDPP μ X K)
    (e : ι ↪ α) (a b : ι → ℝ) :
    (∫ ω, linearStatistic X e a ω * linearStatistic X e b ω ∂μ) -
      (∫ ω, linearStatistic X e a ω ∂μ) * (∫ ω, linearStatistic X e b ω ∂μ) =
        (∑ i, a i * b i * K (e i) (e i)) -
          ∑ i, ∑ j, a i * b j * K (e i) (e j) * K (e j) (e i) := by
  rw [h.linearStatistic_product_moment e a b,
    h.expected_linearStatistic e a, h.expected_linearStatistic e b]
  have hmain : (∑ i, ∑ j, (a i * b j) * (K (e i) (e i) * K (e j) (e j))) =
      (∑ i, a i * K (e i) (e i)) * (∑ j, b j * K (e j) (e j)) := by
    symm
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hdiag : (∑ i, ∑ j, (a i * b j) *
      (if i = j then K (e i) (e i) else 0)) = ∑ i, a i * b i * K (e i) (e i) := by
    simp [mul_ite]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hmain, hdiag]
  simp only [mul_assoc]
  ring

theorem IsDPP.variance_linearStatistic (h : IsDPP μ X K)
    (e : ι ↪ α) (a : ι → ℝ) :
    ProbabilityTheory.variance (linearStatistic X e a) μ =
      (∑ i, (a i) ^ 2 * K (e i) (e i)) -
        ∑ i, ∑ j, a i * a j * K (e i) (e j) * K (e j) (e i) := by
  rw [ProbabilityTheory.variance_eq_sub (h.linearStatistic_memLp e a)]
  simpa only [pow_two, Pi.mul_apply] using h.linearStatistic_covariance e a a

end RiemannResearch.Probability.DPP
