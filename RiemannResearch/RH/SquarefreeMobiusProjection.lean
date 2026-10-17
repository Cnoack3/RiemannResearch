/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CoordinateProjectionCriterion
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.MobiusHilbertCoordinates
import RiemannResearch.RH.QCovarianceInverse
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QSquarefreeInverseCapacity
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Squarefree Möbius coefficient criteria in Pareto and Q

Source: the user's Pareto-to-squarefree-to-Q request, 17 October 2026.
This specializes the original continuous Möbius coordinate theory to the
squarefree dictionary. P and Q use their own orthogonal projections.

All fixed coefficients stabilize unconditionally. Their identification with
-mu(d), for every squarefree d >= 2, is equivalent to squarefree closure
membership, not an unconditional density theorem. Omitted nonsquarefree
coordinates vanish on that closure and are not approximation obligations.

Bagchi, "On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation
of the Riemann hypothesis", Remarks 4 and 8, arXiv:math/0607733, motivates
the squarefree support restriction. The external analytic RH-to-density
direction is not used as an axiom or proved by this module.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.SquarefreeMobiusProjection
open Pareto Pareto.CoefficientStabilization ZetaTwoHilbert
open ZetaTwoParetoTransfer QParetoEquivalence
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.CoordinateProjectionCriterion

/-- The same physical squarefree dictionary, now with the Pareto encoding. -/
def pAtom (i : ℕ) : ThresholdHilbert :=
  toPareto (ZetaTwoOptimizerStage.squarefreeAtom i)

def pProjection (n : ℕ) : ThresholdHilbert :=
  (walkSpan pAtom id n).starProjection hilbertOne

def pLimitProjection : ThresholdHilbert :=
  (dictionaryClosure pAtom).starProjection hilbertOne

def pCoefficient (n m : ℕ) : ℝ := coefficientCLM m (pProjection n)
def pLimitCoefficient (m : ℕ) : ℝ := coefficientCLM m pLimitProjection

/-- The same physical Möbius coefficient functional, continuous for Q. -/
def qCoefficientCLM (m : ℕ) : QHilbert →L[ℝ] ℝ :=
  (coefficientCLM m).comp toParetoCLM

def qCoefficient (n m : ℕ) : ℝ :=
  qCoefficientCLM m (ZetaTwoOptimizerStage.optimizer n)

def qLimitCoefficient (m : ℕ) : ℝ :=
  qCoefficientCLM m (ZetaTwoOptimizerStage.closure.starProjection qOne)

private theorem pareto_coordinates_separate (f : ThresholdHilbert)
    (hf : ∀ i, coefficientCLM (i + 2) f = 0) : f = 0 := by
  apply eq_zero_of_mobius_coordinates_zero
  intro m hm
  have he : m - 2 + 2 = m := by omega
  have h := hf (m - 2)
  rw [he] at h
  simpa only [coefficientCLM, neg_apply, neg_eq_zero] using h

private theorem q_coordinates_separate (f : QHilbert)
    (hf : ∀ i, qCoefficientCLM (i + 2) f = 0) : f = 0 := by
  apply paretoEquiv.injective
  change toPareto f = toParetoLinear 0
  rw [map_zero]
  exact pareto_coordinates_separate _ hf

private theorem p_target_coordinate (i : ℕ) :
    coefficientCLM (i + 2) hilbertOne =
      -(ArithmeticFunction.moebius (i + 2) : ℝ) := by
  simp only [coefficientCLM, neg_apply, mobius_coordinate_one (i + 2) (by omega)]

theorem q_target_coordinate (m : ℕ) (hm : 0 < m) :
    qCoefficientCLM m qOne = -(ArithmeticFunction.moebius m : ℝ) := by
  change coefficientCLM m (toPareto qOne) = _
  rw [toPareto_qOne]
  simp only [coefficientCLM, neg_apply, mobius_coordinate_one m hm]

private theorem p_omitted_atom_coordinate (i : ℕ)
    (hi : ¬Squarefree (i + 2)) (j : ℕ) :
    coefficientCLM (i + 2) (pAtom j) = 0 := by
  classical
  by_cases hj : Squarefree (j + 2)
  · have hij : i ≠ j := by intro he; exact hi (he.symm ▸ hj)
    simp only [pAtom, ZetaTwoOptimizerStage.squarefreeAtom, if_pos hj,
      toPareto_residueAtom, coefficientCLM_biorthogonal, if_neg hij]
  · change coefficientCLM (i + 2)
      (toParetoLinear (ZetaTwoOptimizerStage.squarefreeAtom j)) = 0
    simp only [ZetaTwoOptimizerStage.squarefreeAtom, if_neg hj, map_zero]

private theorem q_omitted_atom_coordinate (i : ℕ)
    (hi : ¬Squarefree (i + 2)) (j : ℕ) :
    qCoefficientCLM (i + 2) (ZetaTwoOptimizerStage.squarefreeAtom j) = 0 :=
  p_omitted_atom_coordinate i hi j

theorem q_coordinate_biorthogonal (i j : ℕ) :
    qCoefficientCLM (i + 2) (qResidue (j + 2)) =
      if i = j then 1 else 0 := by
  change coefficientCLM (i + 2) (toPareto (qResidue (j + 2))) = _
  rw [toPareto_residueAtom, coefficientCLM_biorthogonal]

/-- Nonsquarefree coordinates vanish on the entire infinite closed span. -/
theorem q_omitted_coordinate_zero (i : ℕ) (hi : ¬Squarefree (i + 2))
    {f : QHilbert} (hf : f ∈ ZetaTwoOptimizerStage.closure) :
    qCoefficientCLM (i + 2) f = 0 :=
  coordinate_zero_on_closure ZetaTwoOptimizerStage.squarefreeAtom
    (qCoefficientCLM (i + 2)) (q_omitted_atom_coordinate i hi) hf

/-- Thus the squarefree closed span is a proper ambient subspace,
independently of the constant-target closure question. -/
theorem q_nonsquarefree_atom_not_mem (i : ℕ) (hi : ¬Squarefree (i + 2)) :
    qResidue (i + 2) ∉ ZetaTwoOptimizerStage.closure := by
  intro h
  have hz := q_omitted_coordinate_zero i hi h
  rw [q_coordinate_biorthogonal, if_pos rfl] at hz
  exact one_ne_zero hz

theorem pCoefficient_tendsto (m : ℕ) :
    Tendsto (fun n => pCoefficient n m) atTop (𝓝 (pLimitCoefficient m)) :=
  walkProjection_map_tendsto pAtom id Function.surjective_id hilbertOne
    (coefficientCLM m)

theorem qCoefficient_tendsto (m : ℕ) :
    Tendsto (fun n => qCoefficient n m) atTop (𝓝 (qLimitCoefficient m)) :=
  (qCoefficientCLM m).continuous.continuousAt.tendsto.comp
    ZetaTwoOptimizerStage.optimizer_tendsto

/-- Identification of the already existing squarefree coefficient limits. -/
theorem q_limit_values_iff_coefficient_limits :
    (∀ i : ℕ, Squarefree (i + 2) →
      qLimitCoefficient (i + 2) = -(ArithmeticFunction.moebius (i + 2) : ℝ)) ↔
    (∀ i : ℕ, Squarefree (i + 2) →
      Tendsto (fun n => qCoefficient n (i + 2)) atTop
        (𝓝 (-(ArithmeticFunction.moebius (i + 2) : ℝ)))) := by
  constructor
  · intro h i hi
    simpa only [h i hi] using qCoefficient_tendsto (i + 2)
  · intro h i hi
    exact tendsto_nhds_unique (qCoefficient_tendsto (i + 2)) (h i hi)

/-- The squarefree Pareto version of the full-dictionary Möbius criterion. -/
theorem p_coefficient_limits_iff_closure :
    (∀ i : ℕ, Squarefree (i + 2) →
      Tendsto (fun n => pCoefficient n (i + 2)) atTop
        (𝓝 (-(ArithmeticFunction.moebius (i + 2) : ℝ)))) ↔
      hilbertOne ∈ dictionaryClosure pAtom := by
  have hskip : ∀ i, i ∉ {i : ℕ | Squarefree (i + 2)} →
      ∀ j, coefficientCLM (i + 2) (pAtom j) = 0 :=
    p_omitted_atom_coordinate
  have hxskip : ∀ i, i ∉ {i : ℕ | Squarefree (i + 2)} →
      coefficientCLM (i + 2) hilbertOne = 0 := by
    intro i hi
    rw [p_target_coordinate, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hi]
    simp
  have h := target_mem_iff_coordinate_limits pAtom
    (fun i => coefficientCLM (i + 2)) {i : ℕ | Squarefree (i + 2)}
    hskip pareto_coordinates_separate hilbertOne hxskip
  simpa only [Set.mem_ofPred_eq, pCoefficient, pProjection, p_target_coordinate] using h.symm

/-- The Q statement uses its own actual least-squares projections. -/
theorem q_coefficient_limits_iff_closure :
    (∀ i : ℕ, Squarefree (i + 2) →
      Tendsto (fun n => qCoefficient n (i + 2)) atTop
        (𝓝 (-(ArithmeticFunction.moebius (i + 2) : ℝ)))) ↔
      qOne ∈ ZetaTwoOptimizerStage.closure := by
  have hskip : ∀ i, i ∉ {i : ℕ | Squarefree (i + 2)} →
      ∀ j, qCoefficientCLM (i + 2) (ZetaTwoOptimizerStage.squarefreeAtom j) = 0 :=
    q_omitted_atom_coordinate
  have hxskip : ∀ i, i ∉ {i : ℕ | Squarefree (i + 2)} →
      qCoefficientCLM (i + 2) qOne = 0 := by
    intro i hi
    rw [q_target_coordinate _ (by omega),
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hi]
    simp
  have ht (i : ℕ) := q_target_coordinate (i + 2) (by omega)
  have h := target_mem_iff_coordinate_limits ZetaTwoOptimizerStage.squarefreeAtom
    (fun i => qCoefficientCLM (i + 2)) {i : ℕ | Squarefree (i + 2)}
    hskip q_coordinates_separate qOne hxskip
  simpa only [Set.mem_ofPred_eq, qCoefficient, ZetaTwoOptimizerStage.optimizer,
    ZetaTwoOptimizerStage.stage, ZetaTwoOptimizerStage.closure, ht] using h.symm

/-- Closure transfer identifies the two criteria; it does not identify their
finite projection coefficients. -/
theorem p_q_coefficient_limits_iff :
    (∀ i : ℕ, Squarefree (i + 2) →
      Tendsto (fun n => pCoefficient n (i + 2)) atTop
        (𝓝 (-(ArithmeticFunction.moebius (i + 2) : ℝ)))) ↔
    (∀ i : ℕ, Squarefree (i + 2) →
      Tendsto (fun n => qCoefficient n (i + 2)) atTop
        (𝓝 (-(ArithmeticFunction.moebius (i + 2) : ℝ)))) := by
  rw [p_coefficient_limits_iff_closure, q_coefficient_limits_iff_closure]
  change hilbertOne ∈ (Submodule.span ℝ (Set.range
    (fun i => toPareto (ZetaTwoOptimizerStage.squarefreeAtom i)))).topologicalClosure ↔
      qOne ∈ (Submodule.span ℝ
        (Set.range ZetaTwoOptimizerStage.squarefreeAtom)).topologicalClosure
  simpa only [toPareto_qOne] using
      (mem_closure_span_iff ZetaTwoOptimizerStage.squarefreeAtom qOne).symm

/-- These continuous coordinates equal the genuine finite covariance-inverse
coefficients of the existing squarefree optimizer. -/
theorem qCoefficient_eq_inverseCapacity_coefficient
    (n : ℕ) (i : QSquarefreeInverseCapacity.Index n) :
    qCoefficient n (QSquarefreeInverseCapacity.conductor n i) =
      QSquarefreeInverseCapacity.coefficients n i := by
  classical
  have hpair (j : QSquarefreeInverseCapacity.Index n) :
      qCoefficientCLM (QSquarefreeInverseCapacity.conductor n i)
        (qResidue (QSquarefreeInverseCapacity.conductor n j)) =
          if i = j then 1 else 0 := by
    change qCoefficientCLM (i.val.val + 2) (qResidue (j.val.val + 2)) = _
    rw [q_coordinate_biorthogonal]
    have he : i.val.val = j.val.val ↔ i = j := by
      constructor
      · intro h
        apply Subtype.ext
        exact Fin.ext h
      · intro h
        exact congrArg (fun k : QSquarefreeInverseCapacity.Index n => k.val.val) h
    simp only [he]
  unfold qCoefficient
  rw [← QSquarefreeInverseCapacity.candidate_eq_optimizer n]
  simp only [QSquarefreeInverseCapacity.candidate, QCovarianceInverse.qSynthesis,
    map_sum, map_smul, hpair, smul_eq_mul]
  simp

/-- Exact residual correction; the correction is not assumed to vanish. -/
theorem qLimitCoefficient_eq_residual (m : ℕ) (hm : 0 < m) :
    qLimitCoefficient m = -(ArithmeticFunction.moebius m : ℝ) +
      mobiusDifferenceCLM m (toPareto ZetaTwoOptimizerStage.limitingResidual) := by
  have h := map_sub (qCoefficientCLM m) qOne
    (ZetaTwoOptimizerStage.closure.starProjection qOne)
  change qCoefficientCLM m ZetaTwoOptimizerStage.limitingResidual =
    qCoefficientCLM m qOne - qLimitCoefficient m at h
  rw [q_target_coordinate m hm] at h
  change -mobiusDifferenceCLM m
    (toPareto ZetaTwoOptimizerStage.limitingResidual) =
      -(ArithmeticFunction.moebius m : ℝ) - qLimitCoefficient m at h
  linarith

theorem qCoefficient_error_bound (n m : ℕ) :
    ‖qLimitCoefficient m - qCoefficient n m‖ ^ 2 ≤
      ‖qCoefficientCLM m‖ ^ 2 *
        (ZetaTwoOptimizerStage.error n -
          ‖ZetaTwoOptimizerStage.limitingResidual‖ ^ 2) := by
  simpa only [qLimitCoefficient, qCoefficient, ZetaTwoOptimizerStage.optimizer,
    ZetaTwoOptimizerStage.closure, ZetaTwoOptimizerStage.stage,
    ZetaTwoOptimizerStage.error, ZetaTwoOptimizerStage.residual,
    ZetaTwoOptimizerStage.limitingResidual, walkError, limitingError] using
      walkProjection_map_error_bound ZetaTwoOptimizerStage.squarefreeAtom id
        qOne n (qCoefficientCLM m)

/-- The coefficient criterion and genuine inverse-capacity criterion coincide. -/
theorem q_coefficient_limits_iff_inverseCapacity :
    (∀ i : ℕ, Squarefree (i + 2) →
      Tendsto (fun n => qCoefficient n (i + 2)) atTop
        (𝓝 (-(ArithmeticFunction.moebius (i + 2) : ℝ)))) ↔
      Tendsto QSquarefreeInverseCapacity.inverseCapacity atTop atTop := by
  rw [q_coefficient_limits_iff_closure,
    QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
  exact QSquarefreeInverseCapacity.inverseCapacity_tendsto_iff_squarefree_closure.symm

/-- Conditional research reduction: simultaneous squarefree Möbius limits
remain the only hypothesis in this implication to Mathlib's actual RH. -/
theorem riemannHypothesis_of_squarefree_coefficient_limits
    (h : ∀ i : ℕ, Squarefree (i + 2) →
      Tendsto (fun n => qCoefficient n (i + 2)) atTop
        (𝓝 (-(ArithmeticFunction.moebius (i + 2) : ℝ)))) : RiemannHypothesis :=
  riemannHypothesis_of_qOne_mem_squarefree_closure
    (q_coefficient_limits_iff_closure.mp h)

end RiemannResearch.RH.SquarefreeMobiusProjection
