import RiemannResearch.RH.QReciprocalTargetLift
import RiemannResearch.RH.QReciprocalCostEquivalence
import RiemannResearch.RH.QReciprocalNormalizedBalance
import RiemannResearch.RH.QReciprocalSchurDescent
import RiemannResearch.RH.QReciprocalFiniteCost
import RiemannResearch.RH.QResidueTriangular
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Agenda 02: necessary budgets and explicit direction certificates

Source: PQ_Density_Operators_and_RH_Agenda.pdf, Agenda 02; follow-up of
13 November 2026. All norms use the complete Q measure. D divides by n.

The lower barrier is unconditional. The last RH implication retains a uniform
upper bound on cumulative direction deficits as an Open arithmetic provider.
No finite numerical experiment or lower bound supplies that provider.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QReciprocalBalanceCertificates
open ZetaTwoHilbert QReciprocalMetric QReciprocalCostEquivalence
open QReciprocalTargetLift QReciprocalFullMinimizer QReciprocalSchurDescent
open QReciprocalFiniteCost RiemannResearch.Analysis.FiniteHilbertGram

/-- A bounded normalized cost cannot be smaller than the target's squared norm in the zero-regularization limit. -/
theorem norm_sq_le_of_cost_bound (S : Submodule ℝ QHilbert)
    [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (x : QHilbert) (reg : ℕ → ℝ) (hr : ∀ j, 0 < reg j)
    (hrlim : Tendsto reg atTop (𝓝 0)) (C : ℝ) (hC : 0 ≤ C)
    (F : ℕ → QHilbert) (hm : ∀ j, F j ∈ S)
    (hc : ∀ j, cost (reg j) x (F j) ≤ C * reg j) :
    ‖x‖ ^ 2 ≤ C := by
  have hb (j : ℕ) : ‖F j‖ ≤ Real.sqrt C := by
    have hh := hc j
    unfold cost at hh
    have hsq : ‖F j‖ ^ 2 ≤ C := by
      nlinarith [sq_nonneg ‖D (F j - x)‖, hr j]
    have hs := Real.sq_sqrt hC
    nlinarith [norm_nonneg (F j), Real.sqrt_nonneg C]
  have he (j : ℕ) : ‖D (F j) - D x‖ ^ 2 ≤ C * reg j := by
    have hh := hc j
    unfold cost at hh
    rw [map_sub] at hh
    nlinarith [mul_nonneg (hr j).le (sq_nonneg ‖F j‖)]
  have hu : Tendsto (fun j => C * reg j) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hrlim
  have hs := squeeze_zero (fun j => sq_nonneg ‖D (F j) - D x‖) he hu
  have ht : Tendsto (fun j => D (F j)) atTop (𝓝 (D x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hs
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn
  have hx := (mem_of_bounded_D_tendsto S C.sqrt F x hm hb ht).2
  nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg C, norm_nonneg x]

def directionDeficit (H : ℕ) (α β : ℝ) (w : QHilbert) : ℝ :=
  (α - β) / (α * β) * ‖D (fullMinimizer H α - qOne)‖ ^ 2 -
    (residualPairing β qOne (fullMinimizer H α) w) ^ 2 /
      (β * directionEnergy β w)

/-- An explicit legal direction supplies a lower bound on the complete gain, hence an upper bound on the signed step. -/
theorem signedStep_le_directionDeficit (H K : ℕ) (hHK : H ≤ K)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (w : QHilbert)
    (hw : w ∈ synthesisSpan
      (fun i : Fin K => qResidue (QFullResidueProjection.conductor K i)))
    (hew : 0 < directionEnergy β w) :
    QReciprocalNormalizedBalance.signedStep H K α β ≤ directionDeficit H α β w := by
  have hi := minimizer_direction_bound
    (fun i : Fin K => qResidue (QFullResidueProjection.conductor K i))
    (QResidueTriangular.qResidue_linearIndependent_injective _
      (QFullResidueProjection.conductor_gt_one K)
      (QFullResidueProjection.conductor_injective K))
    β hβ qOne (fullMinimizer H α) w
    (fullSpan_mono H K hHK (minimizer_mem _ qOne α)) hw (ne_of_gt hew)
  change cost β qOne (fullMinimizer K β) ≤ _ at hi
  rw [full_minimum_value K β hβ] at hi
  have hc := full_minimum_value H α hα
  rw [QReciprocalNormalizedBalance.normalized_balance H K hHK α β hα hβ |>.symm]
  calc
    fullValue K β / β - fullValue H α / α ≤
        (cost β qOne (fullMinimizer H α) -
          residualPairing β qOne (fullMinimizer H α) w ^ 2 / directionEnergy β w) / β -
          cost α qOne (fullMinimizer H α) / α := by
      rw [hc]
      exact sub_le_sub_right (div_le_div_of_nonneg_right hi hβ.le) _
    _ = directionDeficit H α β w := by
      unfold cost directionDeficit
      have ha := ne_of_gt hα
      have hb := ne_of_gt hβ
      have he := ne_of_gt hew
      field_simp
      ring

/-- Eventual lower barrier for every constant strictly below the squared target norm. -/
theorem eventually_normalized_cost_ge (S : Submodule ℝ QHilbert)
    [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (x : QHilbert) (reg : ℕ → ℝ) (hr : ∀ j, 0 < reg j)
    (hrlim : Tendsto reg atTop (𝓝 0)) (F : ℕ → QHilbert)
    (hm : ∀ j, F j ∈ S) (c : ℝ) (hc : c < ‖x‖ ^ 2) :
    ∀ᶠ j in atTop, c ≤ cost (reg j) x (F j) / reg j := by
  classical
  by_contra h
  have hcofinal : ∀ N : ℕ, ∃ j : ℕ, N ≤ j ∧ cost (reg j) x (F j) / reg j < c := by
    intro N
    by_contra hn
    apply h
    apply eventually_atTop.mpr
    refine ⟨N, ?_⟩
    intro j hj
    by_contra hjc
    exact hn ⟨j, hj, lt_of_not_ge hjc⟩
  choose φ hφge hφbound using hcofinal
  have hφ : Tendsto φ atTop atTop := tendsto_atTop_mono hφge tendsto_id
  have hmax : max c 0 < ‖x‖ ^ 2 := by
    have hn : 0 ≤ cost (reg (φ 0)) x (F (φ 0)) / reg (φ 0) := by
      unfold cost
      have hp := hr (φ 0)
      positivity
    have hcpos : 0 < c := lt_of_le_of_lt hn (hφbound 0)
    simpa only [max_eq_left hcpos.le] using hc
  have hx := norm_sq_le_of_cost_bound S x (reg ∘ φ) (fun j => hr (φ j))
    (hrlim.comp hφ) (max c 0) (le_max_right _ _) (F ∘ φ) (fun j => hm (φ j)) (by
      intro j
      exact ((div_le_iff₀ (hr (φ j))).mp (hφbound j).le).trans
        (mul_le_mul_of_nonneg_right (le_max_left c 0) (hr (φ j)).le))
  exact (not_le_of_gt hmax) hx

/-- The actual complete minimizers satisfy liminf normalized cost at least one. -/
theorem eventually_fullValue_ge
    (H : ℕ → ℕ) (reg : ℕ → ℝ) (hr : ∀ j, 0 < reg j)
    (hr0 : Tendsto reg atTop (𝓝 0)) (c : ℝ) (hc : c < 1) :
    ∀ᶠ j in atTop, c ≤ fullValue (H j) (reg j) / reg j := by
  have he := eventually_normalized_cost_ge QFullResidueProjection.closure qOne reg hr hr0
    (fun j => fullMinimizer (H j) (reg j))
    (fun j => QFullResidueProjection.legalSpan.le_topologicalClosure (fullMinimizer_legal _ _))
    c (by simpa only [qOne_norm_sq] using hc)
  filter_upwards [he] with j hj
  rwa [full_minimum_value _ _ (hr j)] at hj

/-- Exact telescoping transfers the lower barrier to cumulative signed deficits. -/
theorem eventually_signed_sum_ge
    (H : ℕ → ℕ) (hH : Monotone H) (reg : ℕ → ℝ)
    (hr : ∀ j, 0 < reg j) (hr0 : Tendsto reg atTop (𝓝 0))
    (c : ℝ) (hc : c < 1 - fullValue (H 0) (reg 0) / reg 0) :
    ∀ᶠ n in atTop, c ≤ ∑ j ∈ Finset.range n,
      QReciprocalNormalizedBalance.signedStep
        (H j) (H (j + 1)) (reg j) (reg (j + 1)) := by
  have he := eventually_fullValue_ge H reg hr hr0
    (c + fullValue (H 0) (reg 0) / reg 0) (by linarith)
  filter_upwards [he] with n hn
  rw [QReciprocalNormalizedBalance.normalized_telescoping H hH reg hr n] at hn
  linarith

/-- Every uniform upper budget must leave room for the unit target energy. -/
theorem one_le_initial_add_budget (H : ℕ → ℕ) (hH : Monotone H)
    (reg : ℕ → ℝ) (hr : ∀ j, 0 < reg j)
    (hr0 : Tendsto reg atTop (𝓝 0)) (C : ℝ)
    (hbudget : ∀ n, (∑ j ∈ Finset.range n,
      QReciprocalNormalizedBalance.signedStep
        (H j) (H (j + 1)) (reg j) (reg (j + 1))) ≤ C) :
    1 ≤ fullValue (H 0) (reg 0) / reg 0 + C := by
  let M := fullValue (H 0) (reg 0) / reg 0 + C
  have hb (j : ℕ) : fullValue (H j) (reg j) / reg j ≤ M := by
    rw [QReciprocalNormalizedBalance.normalized_telescoping H hH reg hr j]
    dsimp [M]
    linarith [hbudget j]
  have hM : 0 ≤ M :=
    (div_nonneg (fullValue_nonneg _ _ (hr 0)) (hr 0).le).trans (hb 0)
  have hx := norm_sq_le_of_cost_bound QFullResidueProjection.closure qOne reg hr hr0 M hM
    (fun j => fullMinimizer (H j) (reg j))
    (fun j => QFullResidueProjection.legalSpan.le_topologicalClosure (fullMinimizer_legal _ _))
    (by
      intro j
      rw [full_minimum_value _ _ (hr j)]
      exact (div_le_iff₀ (hr j)).mp (hb j))
  simpa only [qOne_norm_sq] using hx

/-- A nonpositive cumulative budget below unit initial cost is incompatible with vanishing regularization. -/
theorem no_nonpositive_signed_budget_of_initial_lt_one
    (H : ℕ → ℕ) (hH : Monotone H) (reg : ℕ → ℝ)
    (hr : ∀ j, 0 < reg j) (hr0 : Tendsto reg atTop (𝓝 0))
    (hi : fullValue (H 0) (reg 0) / reg 0 < 1) :
    ¬ (∀ n, (∑ j ∈ Finset.range n,
      QReciprocalNormalizedBalance.signedStep
        (H j) (H (j + 1)) (reg j) (reg (j + 1))) ≤ 0) := by
  intro h
  have hh := one_le_initial_add_budget H hH reg hr hr0 0 h
  linarith

/-- Conditional RH consumer: the uniform direction-budget hypothesis remains an Open arithmetic provider. -/
theorem riemannHypothesis_of_direction_budget
    (H : ℕ → ℕ) (hH : Monotone H) (reg : ℕ → ℝ)
    (hr : ∀ j, 0 < reg j) (hr0 : Tendsto reg atTop (𝓝 0))
    (w : ℕ → QHilbert)
    (hw : ∀ j, w j ∈ synthesisSpan
      (fun i : Fin (H (j + 1)) => qResidue (QFullResidueProjection.conductor _ i)))
    (he : ∀ j, 0 < directionEnergy (reg (j + 1)) (w j))
    (C : ℝ)
    (hb : ∀ n, (∑ j ∈ Finset.range n,
      directionDeficit (H j) (reg j) (reg (j + 1)) (w j)) ≤ C) :
    RiemannHypothesis := by
  apply QReciprocalNormalizedBalance.riemannHypothesis_of_signed_budget H hH reg hr hr0 C
  intro n
  apply le_trans (Finset.sum_le_sum (fun j _ =>
    signedStep_le_directionDeficit (H j) (H (j + 1)) (hH (Nat.le_succ j))
      (reg j) (reg (j + 1)) (hr j) (hr (j + 1)) (w j) (hw j) (he j))) (hb n)

#print axioms eventually_fullValue_ge
#print axioms eventually_signed_sum_ge
#print axioms norm_sq_le_of_cost_bound
#print axioms eventually_normalized_cost_ge
#print axioms signedStep_le_directionDeficit
#print axioms one_le_initial_add_budget
#print axioms no_nonpositive_signed_budget_of_initial_lt_one
#print axioms riemannHypothesis_of_direction_budget
end RiemannResearch.RH.QReciprocalBalanceCertificates
