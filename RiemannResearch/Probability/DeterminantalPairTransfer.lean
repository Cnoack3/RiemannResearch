import RiemannResearch.Probability.DeterminantalMoments
import RiemannResearch.Probability.DeterminantalInclusionBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Exact determinantal pair-statistic transfer

Source: the standard determinant inclusion identities in Lyons,
Determinantal probability measures, https://arxiv.org/abs/math/0204325.
The transfer inequality below is an elementary union-bound consequence;
no novelty claim is made. It keeps the complete signed defect before bounding
it by weighted diagonal vacancies. Actual zero-label consumers are in
ZeroOrdinateInfiniteDPP. No asymptotic or independence assumption is used.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RiemannResearch.Probability.DPP
variable {α Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → Set α} {K : α → α → ℝ}

def pairDefect (K : α → α → ℝ) (i j : α) : ℝ :=
  1 - (K i i * K j j - K i j * K j i)

theorem pairDefect_exact (i j : α) :
    pairDefect K i j =
      (1-K i i) + (1-K j j) - (1-K i i)*(1-K j j) + K i j*K j i := by
  unfold pairDefect
  ring

theorem IsDPP.pairDefect_bounds (h : IsDPP μ X K) {i j : α} (hij : i ≠ j) :
    0 ≤ pairDefect K i j ∧ pairDefect K i j ≤ (1-K i i)+(1-K j j) := by
  have hlo := h.inclusion_lower_bound (fun b : Bool => if b then i else j)
  have he : {ω | ∀ b : Bool, (if b then i else j) ∈ X ω} =
      {ω | i ∈ X ω ∧ j ∈ X ω} := by
    ext ω
    simp [Bool.forall_bool, and_comm]
  rw [he] at hlo
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true] at hlo
  rw [h.two_point hij] at hlo
  have hup : μ.real {ω | i ∈ X ω ∧ j ∈ X ω} ≤ 1 := by
    calc
      _ ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _) (measure_ne_top μ _)
      _ = 1 := by simp
  rw [h.two_point hij] at hup
  constructor <;> dsimp [pairDefect] <;> linarith

variable {ι : Type*} [Fintype ι]
def pairMass (w : ι → ι → ℝ) : ℝ := ∑ i, ∑ j, w i j
def expectedPairMass (K : α → α → ℝ) (e : ι → α) (w : ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, w i j * (K (e i) (e i) * K (e j) (e j) - K (e i) (e j) * K (e j) (e i))
def pairVacancyBudget (K : α → α → ℝ) (e : ι → α) (w : ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, |w i j| * ((1-K (e i) (e i))+(1-K (e j) (e j)))

theorem pairMass_sub_expected_exact (e : ι → α) (w : ι → ι → ℝ) :
    pairMass w - expectedPairMass K e w =
      ∑ i, ∑ j, w i j * pairDefect K (e i) (e j) := by
  simp only [pairMass, expectedPairMass, ← Finset.sum_sub_distrib, pairDefect]
  congr 1
  funext i
  congr 1
  funext j
  ring

theorem IsDPP.pairMass_error_le (h : IsDPP μ X K)
    (e : ι ↪ α) (w : ι → ι → ℝ) (hw : ∀ i, w i i = 0) :
    |pairMass w - expectedPairMass K e w| ≤ pairVacancyBudget K e w := by
  classical
  rw [pairMass_sub_expected_exact]
  calc
    _ ≤ ∑ i, |∑ j, w i j * pairDefect K (e i) (e j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |w i j| * ((1-K (e i) (e i))+(1-K (e j) (e j))) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ ∑ j, |w i j * pairDefect K (e i) (e j)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j hj
          by_cases hij : i = j
          · subst j; simp [hw]
          · have hb := h.pairDefect_bounds (fun he => hij (e.injective he))
            rw [abs_mul, abs_of_nonneg hb.1]
            exact mul_le_mul_of_nonneg_left hb.2 (abs_nonneg _)
    _ = _ := rfl

theorem pairVacancyBudget_eq_degrees (e : ι → α) (w : ι → ι → ℝ) :
    pairVacancyBudget K e w =
      ∑ i, (1-K (e i) (e i)) * (∑ j, (|w i j|+|w j i|)) := by
  simp only [pairVacancyBudget, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i j => |w i j| * (1-K (e j) (e j)))]
  congr 1
  all_goals apply Finset.sum_congr rfl
  all_goals intro i hi
  · apply Finset.sum_congr rfl
    intro j hj
    ring
  · apply Finset.sum_congr rfl
    intro j hj
    ring

def pairStatistic (X : Ω → Set α) (e : ι → α) (w : ι → ι → ℝ) (ω : Ω) : ℝ :=
  ∑ i, ∑ j, w i j * (occupancyIndicator X (e i) ω * occupancyIndicator X (e j) ω)

theorem IsDPP.pairStatistic_integrable (h : IsDPP μ X K)
    (e : ι → α) (w : ι → ι → ℝ) : Integrable (pairStatistic X e w) μ :=
  integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      (h.occupancy_product_integrable (e i) (e j)).const_mul (w i j)))

theorem IsDPP.expected_pairStatistic (h : IsDPP μ X K)
    (e : ι ↪ α) (w : ι → ι → ℝ) (hw : ∀ i, w i i = 0) :
    (∫ ω, pairStatistic X e w ω ∂μ) = expectedPairMass K e w := by
  classical
  unfold pairStatistic expectedPairMass
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      (h.occupancy_product_integrable (e i) (e j)).const_mul (w i j)))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum Finset.univ (fun j _ =>
      (h.occupancy_product_integrable (e i) (e j)).const_mul (w i j))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul, h.integral_occupancy_product e]
  by_cases hij : i = j
  · subst j; simp [hw]
  · simp [hij]

theorem IsDPP.pairStatistic_error_le (h : IsDPP μ X K)
    (e : ι ↪ α) (w : ι → ι → ℝ) (hw : ∀ i, w i i = 0) :
    |pairMass w - ∫ ω, pairStatistic X e w ω ∂μ| ≤ pairVacancyBudget K e w := by
  rw [h.expected_pairStatistic e w hw]
  exact h.pairMass_error_le e w hw


theorem IsDPP.totalVacancy_bounds (h : IsDPP μ X K) (e : ι → α) :
    0 ≤ (∑ i, (1-K (e i) (e i))) ∧
      (∑ i, (1-K (e i) (e i))) ≤ Fintype.card ι := by
  have hv (i : ι) : 0 ≤ 1-K (e i) (e i) := by
    rw [← h.vacancy (e i)]
    exact measureReal_nonneg
  have ho (i : ι) : 0 ≤ K (e i) (e i) := by
    rw [← h.occupation (e i)]
    exact measureReal_nonneg
  constructor
  · exact Finset.sum_nonneg (fun i _ => hv i)
  · calc
      _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by linarith [ho i])
      _ = _ := by simp

theorem IsDPP.pairVacancyBudget_le_count (h : IsDPP μ X K)
    (e : ι → α) (w : ι → ι → ℝ) (M : ℝ) (hw : ∀ i j, |w i j| ≤ M) :
    pairVacancyBudget K e w ≤
      2 * M * (Fintype.card ι : ℝ) * ∑ i, (1-K (e i) (e i)) := by
  have hv (i : ι) : 0 ≤ 1-K (e i) (e i) := by
    rw [← h.vacancy (e i)]
    exact measureReal_nonneg
  have hd (i : ι) : (∑ j, (|w i j|+|w j i|)) ≤ (Fintype.card ι : ℝ)*(2*M) := by
    calc
      _ ≤ ∑ j, (M+M) := Finset.sum_le_sum (fun j _ => add_le_add (hw i j) (hw j i))
      _ = _ := by simp; ring
  rw [pairVacancyBudget_eq_degrees]
  calc
    _ ≤ ∑ i, (1-K (e i) (e i)) * ((Fintype.card ι : ℝ)*(2*M)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hd i) (hv i))
    _ = _ := by rw [← Finset.sum_mul]; ring

end RiemannResearch.Probability.DPP
