import RiemannResearch.RH.QReciprocalSchurDescent
import RiemannResearch.RH.QReciprocalFullMinimizer
import RiemannResearch.RH.QReciprocalCostEquivalence
import RiemannResearch.RH.QReciprocalTargetLift
import RiemannResearch.RH.QReciprocalMetric
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Exact normalized balance for changing conductor and regularization

Source: PQ_Density_Operators_and_RH_Agenda.pdf, agendas 1 and 2,
12 November 2026. The signed step retains the entire smoothed residual,
the entire enlargement energy, and the changing-parameter correction.
The signed partial-sum bound in the RH consumer is an Open arithmetic provider.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QReciprocalNormalizedBalance
open ZetaTwoHilbert QReciprocalMetric QReciprocalCostEquivalence
open QReciprocalFullMinimizer QReciprocalSchurDescent

def signedStep (H K : ℕ) (α β : ℝ) : ℝ :=
  (α - β) / (α * β) * ‖D (fullMinimizer H α - qOne)‖ ^ 2 -
    (‖D (fullMinimizer H α - fullMinimizer K β)‖ ^ 2 +
      β * ‖fullMinimizer H α - fullMinimizer K β‖ ^ 2) / β

theorem normalized_balance (H K : ℕ) (hHK : H ≤ K)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    fullValue K β / β - fullValue H α / α = signedStep H K α β := by
  have hi := fullValue_parameters_identity H K hHK α β hα hβ
  have hc := full_minimum_value H α hα
  unfold cost at hc
  have ha : α ≠ 0 := ne_of_gt hα
  have hb : β ≠ 0 := ne_of_gt hβ
  unfold signedStep
  field_simp
  nlinarith [hi, hc]

/-- Exact finite telescoping; no positive-part replacement is made. -/
theorem normalized_telescoping (H : ℕ → ℕ) (hH : Monotone H)
    (reg : ℕ → ℝ) (hr : ∀ j, 0 < reg j) (n : ℕ) :
    fullValue (H n) (reg n) / reg n =
      fullValue (H 0) (reg 0) / reg 0 +
        ∑ j ∈ Finset.range n, signedStep (H j) (H (j + 1)) (reg j) (reg (j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := normalized_balance (H n) (H (n + 1))
      (hH (Nat.le_succ n)) (reg n) (reg (n + 1)) (hr n) (hr (n + 1))
    rw [Finset.sum_range_succ]
    linarith only [ih, hs]

/-- Conditional research reduction: bounded signed cumulative deficit supplies RH. -/
theorem riemannHypothesis_of_signed_budget (H : ℕ → ℕ) (hH : Monotone H)
    (reg : ℕ → ℝ) (hr : ∀ j, 0 < reg j)
    (hr0 : Tendsto reg atTop (𝓝 0)) (C : ℝ)
    (hbudget : ∀ n, (∑ j ∈ Finset.range n,
      signedStep (H j) (H (j + 1)) (reg j) (reg (j + 1))) ≤ C) :
    RiemannHypothesis := by
  let M := fullValue (H 0) (reg 0) / reg 0 + C
  apply QReciprocalTargetLift.riemannHypothesis_of_regularized_D_cost
    (max M 0) (le_max_right _ _) reg (fun j => fullMinimizer (H j) (reg j))
    hr hr0 (fun j => fullMinimizer_legal _ _)
  intro j
  change cost (reg j) qOne (fullMinimizer (H j) (reg j)) ≤ max M 0 * reg j
  rw [full_minimum_value _ _ (hr j)]
  have hb : fullValue (H j) (reg j) / reg j ≤ M := by
    rw [normalized_telescoping H hH reg hr j]
    dsimp [M]
    linarith [hbudget j]
  exact ((div_le_iff₀ (hr j)).mp hb).trans
    (mul_le_mul_of_nonneg_right (le_max_left M 0) (hr j).le)

#print axioms normalized_balance
#print axioms riemannHypothesis_of_signed_budget
end RiemannResearch.RH.QReciprocalNormalizedBalance
