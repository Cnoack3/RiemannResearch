import RiemannResearch.Probability.DeterminantalEntry
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Moments.Variance

/-!
# Finite-window moments of determinantal processes

Source: Hough--Krishnapur--Peres--Virag, Determinantal Processes and
Independence, arXiv:math/0503110, for the count expectation and variance
statements. The proof integrates the finite sums of occupancy indicators and
uses the already proved exact two-point correlation formula.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace RiemannResearch.Probability.DPP

variable {ι α Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → Set α} {K : α → α → ℝ}

def occupancyIndicator (X : Ω → Set α) (i : α) : Ω → ℝ :=
  ({ω | i ∈ X ω} : Set Ω).indicator 1

def windowCount (X : Ω → Set α) (e : ι → α) (ω : Ω) : ℝ :=
  ∑ i : ι, occupancyIndicator X (e i) ω

theorem IsDPP.occupancyIndicator_integrable (h : IsDPP μ X K) (i : α) :
    Integrable (occupancyIndicator X i) μ :=
  (integrable_const (1 : ℝ)).indicator (h.measurable_occupancy i)

theorem IsDPP.integral_occupancyIndicator (h : IsDPP μ X K) (i : α) :
    (∫ ω, occupancyIndicator X i ω ∂μ) = K i i := by
  rw [occupancyIndicator, integral_indicator_one (h.measurable_occupancy i)]
  exact h.occupation i

theorem IsDPP.windowCount_integrable (h : IsDPP μ X K) (e : ι → α) :
    Integrable (windowCount X e) μ :=
  integrable_finsetSum Finset.univ (fun i _ => h.occupancyIndicator_integrable (e i))

theorem IsDPP.windowCount_memLp (h : IsDPP μ X K) (e : ι → α) :
    MemLp (windowCount X e) 2 μ :=
  memLp_finsetSum Finset.univ (fun i _ =>
    MemLp.indicator (h.measurable_occupancy (e i)) (memLp_const (1 : ℝ)))

/-- The expectation of the number of occupied sites in a finite window. -/
theorem IsDPP.expected_windowCount (h : IsDPP μ X K) (e : ι → α) :
    (∫ ω, windowCount X e ω ∂μ) = ∑ i, K (e i) (e i) := by
  simp only [windowCount]
  rw [integral_finsetSum Finset.univ
    (fun i _ => h.occupancyIndicator_integrable (e i))]
  simp_rw [h.integral_occupancyIndicator]

private theorem occupancyIndicator_mul (i j : α) (ω : Ω) :
    occupancyIndicator X i ω * occupancyIndicator X j ω =
      ({ω | i ∈ X ω ∧ j ∈ X ω} : Set Ω).indicator (1 : Ω → ℝ) ω := by
  by_cases hi : i ∈ X ω <;> by_cases hj : j ∈ X ω <;>
    simp [occupancyIndicator, hi, hj]

theorem IsDPP.occupancy_product_integrable (h : IsDPP μ X K) (i j : α) :
    Integrable (fun ω => occupancyIndicator X i ω * occupancyIndicator X j ω) μ := by
  simp_rw [occupancyIndicator_mul]
  exact (integrable_const (1 : ℝ)).indicator
    ((h.measurable_occupancy i).inter (h.measurable_occupancy j))

theorem IsDPP.integral_occupancy_product (h : IsDPP μ X K)
    (e : ι ↪ α) (i j : ι) :
    (∫ ω, occupancyIndicator X (e i) ω * occupancyIndicator X (e j) ω ∂μ) =
      K (e i) (e i) * K (e j) (e j) - K (e i) (e j) * K (e j) (e i) +
        (if i = j then K (e i) (e i) else 0) := by
  simp_rw [occupancyIndicator_mul]
  by_cases hij : i = j
  · subst j
    simp only [and_self, if_true]
    rw [integral_indicator_one (h.measurable_occupancy (e i)), h.occupation (e i)]
    ring
  · have hm : MeasurableSet {ω | e i ∈ X ω ∧ e j ∈ X ω} :=
      (h.measurable_occupancy (e i)).inter (h.measurable_occupancy (e j))
    rw [if_neg hij, add_zero, integral_indicator_one hm]
    exact h.two_point (fun he => hij (e.injective he))

theorem IsDPP.windowCount_square_integrable (h : IsDPP μ X K) (e : ι → α) :
    Integrable (fun ω => (windowCount X e ω) ^ 2) μ := by
  have he : (fun ω => (windowCount X e ω) ^ 2) =
      (fun ω => ∑ i : ι, ∑ j : ι,
        occupancyIndicator X (e i) ω * occupancyIndicator X (e j) ω) := by
    funext ω
    simp only [windowCount, pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [he]
  exact integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => h.occupancy_product_integrable (e i) (e j)))

/-- The second moment of a finite-window count is the square of its mean plus
the trace defect `tr(Q) - tr(Q^2)`. No symmetry hypothesis is needed for the
algebraic correlation identity. -/
theorem IsDPP.windowCount_second_moment (h : IsDPP μ X K) (e : ι ↪ α) :
    (∫ ω, (windowCount X e ω) ^ 2 ∂μ) =
      (∑ i, K (e i) (e i)) ^ 2 + (∑ i, K (e i) (e i)) -
        ∑ i, ∑ j, K (e i) (e j) * K (e j) (e i) := by
  have he : (fun ω => (windowCount X e ω) ^ 2) =
      (fun ω => ∑ i : ι, ∑ j : ι,
        occupancyIndicator X (e i) ω * occupancyIndicator X (e j) ω) := by
    funext ω
    simp only [windowCount, pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [he, integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => h.occupancy_product_integrable (e i) (e j)))]
  have hinner (i : ι) :
      (∫ ω, ∑ j : ι, occupancyIndicator X (e i) ω * occupancyIndicator X (e j) ω ∂μ) =
        ∑ j : ι, (∫ ω, occupancyIndicator X (e i) ω * occupancyIndicator X (e j) ω ∂μ) :=
    integral_finsetSum Finset.univ (fun j _ => h.occupancy_product_integrable (e i) (e j))
  simp_rw [hinner, h.integral_occupancy_product e]
  have hdiag : (∑ i : ι, ∑ j : ι, if i = j then K (e i) (e i) else 0) =
      ∑ i : ι, K (e i) (e i) := by simp
  have hmain : (∑ i : ι, ∑ j : ι, K (e i) (e i) * K (e j) (e j)) =
      (∑ i : ι, K (e i) (e i)) ^ 2 := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hdiag, hmain]
  ring

/-- The actual variance of the finite-window number of occupied sites. -/
theorem IsDPP.variance_windowCount (h : IsDPP μ X K) (e : ι ↪ α) :
    ProbabilityTheory.variance (windowCount X e) μ =
      (∑ i, K (e i) (e i)) -
        ∑ i, ∑ j, K (e i) (e j) * K (e j) (e i) := by
  rw [ProbabilityTheory.variance_eq_sub (h.windowCount_memLp e)]
  change (∫ ω, (windowCount X e ω) ^ 2 ∂μ) -
    (∫ ω, windowCount X e ω ∂μ) ^ 2 = _
  rw [h.windowCount_second_moment e, h.expected_windowCount e]
  ring

end RiemannResearch.Probability.DPP
