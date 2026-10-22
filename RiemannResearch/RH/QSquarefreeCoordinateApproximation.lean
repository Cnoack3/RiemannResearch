/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QSquarefreeCoordinates
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QSquarefreeInverseCapacity
import RiemannResearch.RH.QCovarianceInverse
import RiemannResearch.RH.ZetaTwoOptimizerStage

/-!
# The squarefree approximation problem in legal Parseval coordinates

Source: the user-directed coordinate discussion. This module transports the existing
actual squarefree optimizer and inverse-covariance criterion through the divisor
Hilbert basis. The underlying squarefree RH criterion is discussed in B. Bagchi,
Remarks 4 and 8, https://arxiv.org/abs/math/0607733.

All finite coordinate/error and closure equivalences here are unconditional.
The RH conclusion requires an explicit coordinate-membership hypothesis.
No divergence, density, or RH-to-density provider is constructed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QSquarefreeCoordinateApproximation
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeCoordinates QCovarianceInverse

/-- The constant target is the first unit coordinate. -/
def target : Coordinates := fullCoordinates qOne

theorem target_apply (r : ℕ+) : target r = if r = 1 then 1 else 0 :=
  fullCoordinates_qOne_apply r

theorem synthesis_coordinate {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (c : ι → ℝ) (r : ℕ+) :
    fullCoordinates (qSynthesis d c) r =
      ∑ i, c i * (qResidueDivisorCoefficient (d i) (r : ℕ) /
        Real.sqrt (qJordanTwo (r : ℕ))) := by
  rw [fullCoordinates_apply]
  simp only [qSynthesis, sum_inner, real_inner_smul_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← fullCoordinates_apply, residue_coordinate]

theorem synthesis_mem_closure {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (c : ι → ℝ) (hd : ∀ i, 2 ≤ d i ∧ Squarefree (d i)) :
    qSynthesis d c ∈ qSquarefreeCRTSpan.topologicalClosure := by
  unfold qSynthesis
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply qSquarefreeCRTSpan.le_topologicalClosure
  exact Submodule.subset_span ⟨⟨d i, hd i⟩, rfl⟩

theorem synthesis_coordinates_legal {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (c : ι → ℝ) (hd : ∀ i, 2 ≤ d i ∧ Squarefree (d i)) :
    fullCoordinates (qSynthesis d c) ∈ coordinateSpace := by
  apply (mem_coordinateSpace _).mpr
  rw [fullCoordinates.symm_apply_apply]
  exact synthesis_mem_closure d c hd

theorem synthesis_coordinate_error {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (c : ι → ℝ) :
    ‖target - fullCoordinates (qSynthesis d c)‖^2 =
      ‖qOne - qSynthesis d c‖^2 := by
  rw [target, fullCoordinates_error]

theorem target_mem_iff_squarefree_closure :
    target ∈ coordinateSpace ↔ qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
  rw [target, mem_coordinateSpace, fullCoordinates.symm_apply_apply]

theorem target_mem_iff_inverseCapacity_tendsto :
    target ∈ coordinateSpace ↔
      Tendsto QSquarefreeInverseCapacity.inverseCapacity atTop atTop :=
  target_mem_iff_squarefree_closure.trans
    QSquarefreeInverseCapacity.inverseCapacity_tendsto_iff_squarefree_closure.symm

theorem candidate_coordinate_error (n : ℕ) :
    ‖target - fullCoordinates (QSquarefreeInverseCapacity.candidate n)‖^2 =
      1 / (1 + QSquarefreeInverseCapacity.inverseCapacity n) := by
  rw [target, fullCoordinates_error, QSquarefreeInverseCapacity.candidate_eq_optimizer]
  exact QSquarefreeInverseCapacity.error_eq_reciprocal n

theorem optimizer_coordinates_tendsto :
    Tendsto (fun n => fullCoordinates (ZetaTwoOptimizerStage.optimizer n)) atTop
      (𝓝 (coordinateSpace.starProjection target)) := by
  have h : Tendsto
      (fun n => fullCoordinates (ZetaTwoOptimizerStage.optimizer n)) atTop
      (𝓝 (fullCoordinates (ZetaTwoOptimizerStage.closure.starProjection qOne))) :=
    fullCoordinates.continuous.continuousAt.tendsto.comp
      ZetaTwoOptimizerStage.optimizer_tendsto
  have hp : coordinateSpace.starProjection target =
      fullCoordinates (ZetaTwoOptimizerStage.closure.starProjection qOne) := by
    simpa only [target, fullCoordinates.symm_apply_apply,
      QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure] using
      coordinate_projection_conjugation target
  rw [hp]
  exact h

/-- Conditional research reduction; target membership is the open arithmetic input. -/
theorem riemannHypothesis_of_target_mem (h : target ∈ coordinateSpace) :
    RiemannHypothesis :=
  QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_squarefree_closure.mpr
      (target_mem_iff_squarefree_closure.mp h))

end RiemannResearch.RH.QSquarefreeCoordinateApproximation
