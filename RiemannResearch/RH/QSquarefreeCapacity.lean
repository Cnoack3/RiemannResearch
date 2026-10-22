import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import RiemannResearch.RH.QCovarianceInverse
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse

/-!
# Actual squarefree covariance capacity for the zeta-two law

Source: the user's Q-Gram research program, 13 October 2026. Every finite
system below is the Gram/covariance system of the existing actual Q-Hilbert
residue vectors. The redundant squarefree stage has zero coordinates, so
we use solvable centered normal equations instead of silently applying a
totalized inverse to a singular matrix.

The capacity is independent of the choice of centered solution. Its
divergence is equivalent to literal squarefree closure and to the existing
exact-head bounded-tail property. It implies Mathlib's RiemannHypothesis.
The converse RH-to-squarefree-density analytic provider is NOT proved here.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QSquarefreeCapacity

open ZetaTwoHilbert ZetaTwoOptimizerStage QCovarianceInverse
open RiemannResearch.LinearAlgebra
open RiemannResearch.LinearAlgebra.CenteredNormalEquations
open RiemannResearch.Analysis.ExhaustiveWalk
open ZetaTwoProbability

/-- Replace an illegal squarefree coordinate by the identically zero atom g₁. -/
def conductor (i : ℕ) : ℕ := if Squarefree (i + 2) then i + 2 else 1

theorem squarefreeAtom_eq_residue (i : ℕ) :
    squarefreeAtom i = qResidue (conductor i) := by
  by_cases hs : Squarefree (i + 2)
  · simp [squarefreeAtom, conductor, hs]
  · simp [squarefreeAtom, conductor, hs]

theorem synthesis_eq_combination (n : ℕ) (c : Fin n → ℝ) :
    qSynthesis (fun i : Fin n => conductor i) c =
      finiteSchurCombination (fun i : Fin n => squarefreeAtom i) c := by
  unfold qSynthesis finiteSchurCombination
  apply Finset.sum_congr rfl
  intro i hi
  change c i • qResidue (conductor i) = c i • squarefreeAtom i
  rw [squarefreeAtom_eq_residue]

/-- Actual finite normal-equation coefficients in the masked squarefree model. -/
theorem exists_normal_optimizer (n : ℕ) :
    ∃ c : Fin n → ℝ,
      qSynthesis (fun i : Fin n => conductor i) c = optimizer n ∧
      ∀ i, action (qGram (fun j : Fin n => conductor j)) c i =
        qMean (fun j : Fin n => conductor j) i := by
  obtain ⟨c, hc, hn⟩ := exists_optimizer_coefficients n
  refine ⟨c, (synthesis_eq_combination n c).trans hc, ?_⟩
  intro i
  rw [← qGram_synthesis, synthesis_eq_combination]
  simpa only [qMean, ← squarefreeAtom_eq_residue, real_inner_comm qOne] using hn i

theorem error_eq_of_normal_optimizer (n : ℕ) (c : Fin n → ℝ)
    (hc : qSynthesis (fun i : Fin n => conductor i) c = optimizer n)
    (hn : ∀ i, action (qGram (fun j : Fin n => conductor j)) c i =
      qMean (fun j : Fin n => conductor j) i) :
    error n = 1 - dot (qMean (fun i : Fin n => conductor i)) c := by
  have hquad : quadratic (qGram (fun i : Fin n => conductor i)) c =
      dot (qMean (fun i : Fin n => conductor i)) c := by
    unfold quadratic
    rw [show action (qGram (fun i : Fin n => conductor i)) c =
      qMean (fun i : Fin n => conductor i) from funext hn, dot_comm]
  change ‖qOne - optimizer n‖ ^ 2 = _
  rw [← hc, qError_eq, hquad]
  ring

/-- The information carried by the actual finite squarefree stage. -/
def capacity (n : ℕ) : ℝ := (1 - error n) / error n

/-- A centered solve exists at every actual squarefree optimizer stage. -/
theorem exists_centered_solution (n : ℕ) :
    ∃ u : Fin n → ℝ,
      (∀ i, action (qCov (fun j : Fin n => conductor j)) u i =
        qMean (fun j : Fin n => conductor j) i) ∧
      dot (qMean (fun i : Fin n => conductor i)) u = capacity n := by
  obtain ⟨c, hc, hn⟩ := exists_normal_optimizer n
  have he := error_eq_of_normal_optimizer n c hc hn
  have hne : 1 - dot (qMean (fun i : Fin n => conductor i)) c ≠ 0 := by
    rw [← he]
    exact ne_of_gt (error_pos n)
  refine ⟨fun i => c i / error n, ?_, ?_⟩
  · intro i
    rw [he]
    apply covariance_of_gram_solution
    · intro i
      rw [← qGram_rankOne]
      exact hn i
    · exact hne
  · rw [dot_div]
    unfold capacity
    congr 1
    linarith

/-- Redundant coordinates can change the solution, but never its information. -/
theorem capacity_eq_information (n : ℕ) (u : Fin n → ℝ)
    (hu : ∀ i, action (qCov (fun j : Fin n => conductor j)) u i =
      qMean (fun j : Fin n => conductor j) i) :
    capacity n = dot (qMean (fun i : Fin n => conductor i)) u := by
  obtain ⟨v, hv, he⟩ := exists_centered_solution n
  rw [← he]
  exact information_eq_of_solutions _ _ v u (qCov_symmetric _) hv hu

theorem capacity_nonneg (n : ℕ) : 0 ≤ capacity n := by
  obtain ⟨u, hu, he⟩ := exists_centered_solution n
  rw [← he]
  exact qInformation_nonneg _ u hu

theorem error_eq_reciprocal_capacity (n : ℕ) :
    error n = 1 / (1 + capacity n) := by
  have he : error n ≠ 0 := ne_of_gt (error_pos n)
  have hd : 1 + capacity n ≠ 0 := by
    have h := capacity_nonneg n
    linarith
  apply (eq_div_iff hd).mpr
  unfold capacity
  field_simp [he]
  <;> ring

theorem capacity_tendsto_iff_error_tendsto :
    Tendsto capacity atTop atTop ↔ Tendsto error atTop (𝓝 0) := by
  constructor
  · intro ht
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Filter.Eventually.of_forall (fun n => ha.trans (error_pos n))
    · intro b hb
      filter_upwards [(tendsto_atTop.mp ht) (1 / b)] with n hn
      change 1 / b ≤ (1 - error n) / error n at hn
      have h := (le_div_iff₀ (error_pos n)).mp hn
      have h' : error n / b ≤ 1 - error n := by
        simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using h
      have h'' := (div_le_iff₀ hb).mp h'
      nlinarith [mul_pos hb (error_pos n)]
  · intro he
    apply tendsto_atTop.2
    intro B
    have hp : 0 < max B 0 + 2 := by positivity
    have hε : 0 < 1 / (max B 0 + 2) := by positivity
    filter_upwards [he.eventually (Iio_mem_nhds hε)] with n hn
    change B ≤ (1 - error n) / error n
    apply (le_div_iff₀ (error_pos n)).mpr
    have h := (lt_div_iff₀ hp).mp hn
    have hB := mul_le_mul_of_nonneg_right (le_max_left B 0) (error_pos n).le
    nlinarith [error_pos n]

theorem capacity_tendsto_iff_optimizer_closure :
    Tendsto capacity atTop atTop ↔ qOne ∈ ZetaTwoOptimizerStage.closure :=
  capacity_tendsto_iff_error_tendsto.trans error_tendsto_zero_iff_mem_closure

/-- The exhaustive masked dictionary has precisely the literal squarefree span. -/
theorem optimizer_closure_eq_squarefree_closure :
    ZetaTwoOptimizerStage.closure = qSquarefreeCRTSpan.topologicalClosure := by
  have hs : Submodule.span ℝ (Set.range squarefreeAtom) = qSquarefreeCRTSpan := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      by_cases hi : Squarefree (i + 2)
      · rw [squarefreeAtom, if_pos hi]
        exact Submodule.subset_span ⟨⟨i + 2, by omega, hi⟩, rfl⟩
      · rw [squarefreeAtom, if_neg hi]
        exact Submodule.zero_mem _
    · apply Submodule.span_le.mpr
      rintro _ ⟨d, rfl⟩
      change qResidue d.val ∈ Submodule.span ℝ (Set.range squarefreeAtom)
      have he : d.val - 2 + 2 = d.val := by have := d.property.1; omega
      have hd : squarefreeAtom (d.val - 2) = qResidue d.val := by
        simp [squarefreeAtom, he, d.property.2]
      rw [← hd]
      exact Submodule.subset_span ⟨d.val - 2, rfl⟩
  change (Submodule.span ℝ (Set.range squarefreeAtom)).topologicalClosure = _
  rw [hs]

theorem capacity_tendsto_iff_squarefree_closure :
    Tendsto capacity atTop atTop ↔ qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
  rw [← optimizer_closure_eq_squarefree_closure]
  exact capacity_tendsto_iff_optimizer_closure

theorem capacity_tendsto_iff_exact_head_tail_bound :
    Tendsto capacity atTop atTop ↔ Pareto.SquarefreeExactHeadTailBound :=
  capacity_tendsto_iff_squarefree_closure.trans
    qSquarefreeClosure_iff_exact_head_tail_bound

/-- This conclusion is Mathlib's RH, using the established Mellin obstruction. -/
theorem riemannHypothesis_of_capacity_tendsto
    (h : Tendsto capacity atTop atTop) : RiemannHypothesis := by
  obtain ⟨C, hC⟩ := capacity_tendsto_iff_exact_head_tail_bound.mp h
  choose L F hL hF hhead htail using hC
  apply Pareto.riemannHypothesis_of_squarefree_span_bounded_tail
    id L F tendsto_id hL hF hhead
  refine ⟨C, ?_⟩
  rintro _ ⟨j, rfl⟩
  exact htail j

/-- The exact capacity gain retains the full actual projection increment. -/
theorem capacity_increment (n : ℕ) :
    capacity (n + 1) - capacity n =
      ‖optimizer (n + 1) - optimizer n‖ ^ 2 / (error n * error (n + 1)) := by
  have h := walkError_step squarefreeAtom id qOne n
  change error n = error (n + 1) + ‖optimizer (n + 1) - optimizer n‖ ^ 2 at h
  unfold capacity
  field_simp [ne_of_gt (error_pos n), ne_of_gt (error_pos (n + 1))]
  nlinarith

theorem capacity_monotone : Monotone capacity := by
  apply monotone_nat_of_le_succ
  intro n
  have h := capacity_increment n
  have hp : 0 ≤ ‖optimizer (n + 1) - optimizer n‖ ^ 2 /
      (error n * error (n + 1)) :=
    div_nonneg (sq_nonneg _) (mul_pos (error_pos n) (error_pos (n + 1))).le
  linarith

theorem capacity_accumulated_gain (N : ℕ) :
    (∑ n ∈ Finset.range N,
      ‖optimizer (n + 1) - optimizer n‖ ^ 2 / (error n * error (n + 1))) =
      capacity N - capacity 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, ← capacity_increment]
      ring

/-- Conditional analytic assembly only: `hforward` is the separately required
RH-to-squarefree-Q-density theorem. This module does not prove or postulate
that analytic provider. The opposite implication is the unconditional
Mellin-obstruction consumer `riemannHypothesis_of_capacity_tendsto`. -/
theorem capacity_tendsto_iff_riemannHypothesis
    (hforward : RiemannHypothesis →
      qOne ∈ qSquarefreeCRTSpan.topologicalClosure) :
    Tendsto capacity atTop atTop ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_capacity_tendsto
  · intro hRH
    exact capacity_tendsto_iff_squarefree_closure.mpr (hforward hRH)

end RiemannResearch.RH.QSquarefreeCapacity
