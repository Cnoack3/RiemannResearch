import RiemannResearch.RH.ParetoTailCapacityDuality
import RiemannResearch.Analysis.FiniteGramScreenedCapacity
import RiemannResearch.Analysis.ResidualGainProduct

/-!
# Vacancy, capacity, and hazard products

Source: user-provided
`RH_DPP_Proof_Attempt_and_Explicit_Zero_Hole_Obstruction_2026-09-20.md`,
Section 2. This module uses the actual residue-tail Gram matrices and their
verified inverses. No divergence hypothesis is assumed except explicitly
in the conditional RH endpoints.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization
open CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.ExhaustiveWalk

def vacancy (n : ℕ) : ℝ := 2 * pointError n

theorem vacancy_eq_capacity (n : ℕ) :
    vacancy n = 2 / (tailCapacity n + 2) := by
  rw [vacancy, pointError_eq_inv_capacity]
  ring

theorem vacancy_eq_projection_residual (n : ℕ) :
    vacancy n = 2 * ‖paretoPointHilbert 0 -
      (finiteSpace n).starProjection (paretoPointHilbert 0)‖ ^ 2 := rfl

theorem vacancy_eq_fullCapacity (n : ℕ) :
    vacancy n = 1 - fullCapacity n / 2 := by
  rw [vacancy, pointError_eq_deficit]
  ring

@[simp] theorem vacancy_zero : vacancy 0 = 1 := by
  have hc : tailCapacity 0 = 0 := by
    simp [tailCapacity, RiemannResearch.Analysis.FiniteGramCapacity.capacity]
  rw [vacancy_eq_capacity, hc]
  norm_num

theorem vacancy_pos (n : ℕ) : 0 < vacancy n := by
  exact mul_pos (by norm_num) (pointError_pos n)

theorem vacancy_antitone : Antitone vacancy := by
  intro m n hmn
  exact mul_le_mul_of_nonneg_left
    (walkError_antitone residueAtom id (paretoPointHilbert 0) hmn) (by norm_num)

theorem vacancy_le_one (n : ℕ) : vacancy n ≤ 1 := by
  simpa only [vacancy_zero] using vacancy_antitone (Nat.zero_le n)

/-- The deterministic conditional-entry ratio; a probabilistic reading requires
    the corresponding nested DPP coupling. Independence is not assumed. -/
def hazard (n : ℕ) : ℝ := 1 - vacancy (n+1) / vacancy n

theorem hazard_nonneg (n : ℕ) : 0 ≤ hazard n := by
  have h := vacancy_antitone (Nat.le_succ n)
  have hp := vacancy_pos n
  dsimp [hazard]
  have hd : vacancy (n+1) / vacancy n ≤ 1 :=
    (div_le_iff₀ hp).mpr (by simpa using h)
  linarith

theorem hazard_lt_one (n : ℕ) : hazard n < 1 := by
  have hd : 0 < vacancy (n+1) / vacancy n :=
    div_pos (vacancy_pos (n+1)) (vacancy_pos n)
  dsimp [hazard]
  linarith

theorem hazard_eq_capacity_increment (n : ℕ) :
    hazard n = (tailCapacity (n+1) - tailCapacity n) /
      (tailCapacity (n+1) + 2) := by
  have h₀ : tailCapacity n + 2 ≠ 0 := by linarith [tailCapacity_nonneg n]
  have h₁ : tailCapacity (n+1) + 2 ≠ 0 := by
    linarith [tailCapacity_nonneg (n+1)]
  simp only [hazard, vacancy_eq_capacity]
  field_simp [h₀, h₁]
  ring

theorem hazard_eq_minimum_increment (n : ℕ) :
    hazard n = ‖tailMinimum (n+1) - tailMinimum n‖ ^ 2 /
      (tailCapacity (n+1) + 2) := by
  rw [hazard_eq_capacity_increment,
    tailMinimum_increment n (n+1) (Nat.le_succ n)]

theorem vacancy_step (n : ℕ) :
    vacancy (n+1) = vacancy n * (1 - hazard n) := by
  have hq : vacancy n ≠ 0 := ne_of_gt (vacancy_pos n)
  dsimp [hazard]
  field_simp [hq]
  ring

theorem vacancy_product (n : ℕ) :
    vacancy n = ∏ j ∈ Finset.range n, (1 - hazard j) := by
  induction n with
  | zero => simp
  | succ n ih => rw [vacancy_step, ih, Finset.prod_range_succ]

theorem vacancy_tendsto_zero_iff :
    Tendsto vacancy atTop (𝓝 0) ↔ Tendsto tailCapacity atTop atTop := by
  rw [tailCapacity_tendsto_iff]
  constructor
  · intro h
    have h' := h.const_mul (1 / 2 : ℝ)
    have he : (fun n => (1 / 2 : ℝ) * vacancy n) = pointError := by
      funext n
      simp only [vacancy]
      ring
    simpa only [he, mul_zero] using h'
  · intro h
    change Tendsto (fun n => 2 * pointError n) atTop (𝓝 0)
    simpa only [mul_zero] using h.const_mul (2 : ℝ)

theorem riemannHypothesis_of_vacancy_tendsto_zero
    (h : Tendsto vacancy atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_tailCapacity_tendsto (vacancy_tendsto_zero_iff.mp h)

theorem riemannHypothesis_of_hazard_product_tendsto_zero
    (h : Tendsto (fun n => ∏ j ∈ Finset.range n, (1 - hazard j))
      atTop (𝓝 0)) : RiemannHypothesis := by
  apply riemannHypothesis_of_vacancy_tendsto_zero
  simpa only [← vacancy_product] using h


/-- The hazard series uses the actual reciprocal-tail Gram capacities. -/
theorem vacancy_tendsto_zero_iff_hazard_not_summable :
    Tendsto vacancy atTop (𝓝 0) ↔ ¬Summable hazard :=
  RiemannResearch.Analysis.ResidualGain.residual_tendsto_zero_iff_not_summable
    (vacancy_pos 0) hazard_nonneg hazard_lt_one vacancy_step

theorem vacancy_tendsto_zero_iff_hazard_sum_tendsto :
    Tendsto vacancy atTop (𝓝 0) ↔
      Tendsto (fun N => ∑ j ∈ Finset.range N, hazard j) atTop atTop :=
  vacancy_tendsto_zero_iff_hazard_not_summable.trans
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hazard_nonneg)

theorem riemannHypothesis_of_hazard_not_summable (h : ¬Summable hazard) :
    RiemannHypothesis :=
  riemannHypothesis_of_vacancy_tendsto_zero
    (vacancy_tendsto_zero_iff_hazard_not_summable.mpr h)

theorem riemannHypothesis_of_hazard_sum_tendsto
    (h : Tendsto (fun N => ∑ j ∈ Finset.range N, hazard j) atTop atTop) :
    RiemannHypothesis :=
  riemannHypothesis_of_vacancy_tendsto_zero
    (vacancy_tendsto_zero_iff_hazard_sum_tendsto.mpr h)

/-- Exact finite log accounting, with no assumption that the hazards diverge. -/
theorem log_hazard_telescope (n : ℕ) :
    (∑ j ∈ Finset.range n, -Real.log (1 - hazard j)) =
      -Real.log (vacancy n) := by
  have h := RiemannResearch.Analysis.ResidualGain.log_recurrence_eq_initial_sub_sum
    (vacancy_pos 0) hazard_lt_one vacancy_step n
  rw [vacancy_zero, Real.log_one] at h
  linarith

theorem hazard_sum_le_log_vacancy (n : ℕ) :
    (∑ j ∈ Finset.range n, hazard j) ≤ -Real.log (vacancy n) := by
  rw [← log_hazard_telescope]
  exact Finset.sum_le_sum (fun j _ =>
    RiemannResearch.Analysis.ResidualGain.gain_le_neg_log_one_sub (hazard_lt_one j))

/-- Complete telescoping of the actual successive reciprocal-tail optimizers. -/
theorem capacity_eq_sum_minimum_increments (n : ℕ) :
    tailCapacity n = ∑ j ∈ Finset.range n,
      ‖tailMinimum (j+1) - tailMinimum j‖ ^ 2 := by
  have hs (j : ℕ) : tailCapacity (j+1) = tailCapacity j +
      ‖tailMinimum (j+1) - tailMinimum j‖ ^ 2 := by
    rw [tailMinimum_increment j (j+1) (Nat.le_succ j)]
    ring
  have h := RiemannResearch.Analysis.FiniteGramCapacity.capacity_telescope
    tailCapacity (fun j => ‖tailMinimum (j+1) - tailMinimum j‖ ^ 2) hs n
  have hc : tailCapacity 0 = 0 := by
    simp [tailCapacity, RiemannResearch.Analysis.FiniteGramCapacity.capacity]
  simpa only [hc, zero_add] using h

end RiemannResearch.RH.Pareto.IntegerDPP
