/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QParetoClosedProjectionComparison
import RiemannResearch.RH.QShiftedReciprocalBounds
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.RH.QHilbertConvergence
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Matched finite squarefree Q/P projections

Source: Sections B1--B2 of the user's measure-change regularity handoff,
25 October 2026. Both finite projections use exactly the same masked
squarefree dictionary. The signed resolvent forcing is retained.
The final physical head bound is an open premise, not proved here.
-/

noncomputable section



open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoEquivalence QParetoClosedProjectionComparison QShiftedReciprocal
open ZetaTwoOptimizerStage QSquarefreeMeasureRigidity
open QSquarefreeDisplacementRigidity QSquarefreeSmoothedProjection
open RiemannResearch.Analysis.ExhaustiveWalk

def paretoAtom (i : ℕ) : ThresholdHilbert := toPareto (squarefreeAtom i)

def paretoStage (N : ℕ) : Submodule ℝ ThresholdHilbert :=
  walkSpan paretoAtom id N

instance paretoStage_finiteDimensional (N : ℕ) :
    FiniteDimensional ℝ (paretoStage N) := by
  unfold paretoStage
  infer_instance

theorem stage_map_eq (N : ℕ) :
    (stage N).map paretoEquiv.toLinearMap = paretoStage N := by
  exact map_span_range (fun i : Fin N => squarefreeAtom i)

theorem toPareto_mem_paretoStage_iff (N : ℕ) (f : QHilbert) :
    toPareto f ∈ paretoStage N ↔ f ∈ stage N := by
  rw [← stage_map_eq]
  constructor
  · rintro ⟨g, hg, he⟩
    have hgf : g = f := paretoEquiv.injective he
    subst g
    exact hg
  · intro hf
    exact ⟨f, hf, rfl⟩

theorem paretoDictionaryClosure_eq :
    dictionaryClosure paretoAtom = paretoSquarefreeClosure := by
  ext y
  have h := toPareto_mem_paretoSquarefreeClosure_iff (toQ y)
  rw [toPareto_toQ] at h
  have h' := mem_closure_span_iff squarefreeAtom (toQ y)
  rw [toPareto_toQ] at h'
  exact h'.symm.trans h.symm

def finitePFit (N : ℕ) : QHilbert := pFit (paretoStage N) qOne

def finiteDisplacement (N : ℕ) : QHilbert := optimizer N - finitePFit N

theorem finitePFit_mem (N : ℕ) : finitePFit N ∈ stage N :=
  pFit_mem (stage N) (paretoStage N) (toPareto_mem_paretoStage_iff N) qOne

theorem finiteDisplacement_mem (N : ℕ) : finiteDisplacement N ∈ stage N :=
  (stage N).sub_mem ((stage N).starProjection_apply_mem qOne) (finitePFit_mem N)

theorem finitePFit_tendsto :
    Tendsto finitePFit atTop (𝓝 (pFit paretoSquarefreeClosure qOne)) := by
  have hp := walkProjection_tendsto paretoAtom id Function.surjective_id
    (toPareto qOne)
  have hp' : Tendsto (fun N => (paretoStage N).starProjection (toPareto qOne))
      atTop (𝓝 (paretoSquarefreeClosure.starProjection (toPareto qOne))) := by
    simpa only [paretoStage, paretoDictionaryClosure_eq] using hp
  exact toQCLM.continuous.continuousAt.tendsto.comp hp'

theorem finiteDisplacement_tendsto :
    Tendsto finiteDisplacement atTop (𝓝 displacement) :=
  optimizer_tendsto.sub finitePFit_tendsto

theorem finitePResidual_eq (N : ℕ) :
    qOne - finitePFit N = residual N + finiteDisplacement N := by
  unfold ZetaTwoOptimizerStage.residual finiteDisplacement
  abel

theorem finite_witness_mem_orthogonal (N : ℕ) :
    B (qOne - finitePFit N) - finiteDisplacement N ∈ (stage N)ᗮ := by
  apply ((stage N).mem_orthogonal _).mpr
  intro v hv
  have hp : inner ℝ (toPareto v) (toPareto (qOne - finitePFit N)) = 0 := by
    change inner ℝ (toPareto v)
      (toPareto (qOne - pFit (paretoStage N) qOne)) = 0
    rw [toPareto_sub, toPareto_pFit]
    exact Submodule.inner_right_of_mem_orthogonal
      ((toPareto_mem_paretoStage_iff N v).mpr hv)
      (Submodule.sub_starProjection_mem_orthogonal
        (K := paretoStage N) (toPareto qOne))
  rw [pareto_inner_identity] at hp
  have hp' : inner ℝ v (qOne - finitePFit N) -
      inner ℝ v (B (qOne - finitePFit N)) = 0 :=
    (mul_eq_zero.mp hp).resolve_left (ne_of_gt zetaTwo_pos)
  have hq := Submodule.inner_right_of_mem_orthogonal hv (residual_mem_orthogonal N)
  rw [finitePResidual_eq, inner_add_right, hq, zero_add] at hp'
  rw [inner_sub_right, finitePResidual_eq]
  linarith

/-- The finite Q-coordinate change-of-metric equation. -/
theorem finite_resolvent (N : ℕ) :
    finiteDisplacement N - (stage N).starProjection (B (finiteDisplacement N)) =
      movingCorrection N := by
  have he : (stage N).starProjection (B (qOne - finitePFit N)) =
      finiteDisplacement N := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      (finiteDisplacement_mem N)
    intro v hv
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hv (finite_witness_mem_orthogonal N)
  rw [finitePResidual_eq, map_add, map_add] at he
  unfold movingCorrection
  exact sub_eq_iff_eq_add.mpr he.symm

/-- A shared expanding-head bound on matched finite displacements would imply RH.
The common bound is not obtained from their Hilbert norm convergence. -/
theorem riemannHypothesis_of_finiteDisplacement_head_bound
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ N k : ℕ, 0 < k → k ≤ N →
      |qSequence (finiteDisplacement N) k| ≤ C) : RiemannHypothesis := by
  apply riemannHypothesis_of_displacement_bounded C
  intro k
  by_contra h
  have ht := (qSequence_tendsto_of_tendsto
    finiteDisplacement_tendsto k).abs
  have hg := ht.eventually (Ioi_mem_nhds (lt_of_not_ge h))
  have he : ∀ᶠ N in atTop, |qSequence (finiteDisplacement N) k| ≤ C := by
    filter_upwards [eventually_ge_atTop k] with N hN
    by_cases hk : k = 0
    · simpa [hk, qSequence] using hC
    · exact hb N k (Nat.pos_of_ne_zero hk) hN
  obtain ⟨N, hN, hgt⟩ := (he.and hg).exists
  exact (not_lt_of_ge hN) hgt

end RiemannResearch.RH.QSquarefreeFiniteDisplacement

namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement
open ZetaTwoHilbert ZetaTwoOptimizerStage QShiftedReciprocal

theorem finiteDisplacement_energy_bound (N : ℕ) :
    8 * ‖finiteDisplacement N‖ ^ 2 ≤ ‖residual N‖ ^ 2 := by
  apply sharp_displacement_energy_bound
  · exact Submodule.inner_right_of_mem_orthogonal
      (finiteDisplacement_mem N) (residual_mem_orthogonal N)
  · have h := Submodule.inner_right_of_mem_orthogonal
      (finiteDisplacement_mem N) (finite_witness_mem_orthogonal N)
    rw [inner_sub_right, real_inner_self_eq_norm_sq, finitePResidual_eq] at h
    exact sub_eq_zero.mp h

theorem finitePareto_residual_energy_bound (N : ℕ) :
    ‖qOne - finitePFit N‖ ^ 2 ≤ (9 / 8 : ℝ) * ‖residual N‖ ^ 2 := by
  have he := QParetoClosedProjectionComparison.q_trial_identity
    (stage N) (paretoStage N) (toPareto_mem_paretoStage_iff N) qOne
  change ‖qOne - finitePFit N‖ ^ 2 =
    ‖residual N‖ ^ 2 + ‖finiteDisplacement N‖ ^ 2 at he
  nlinarith [finiteDisplacement_energy_bound N]

end RiemannResearch.RH.QSquarefreeFiniteDisplacement

namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open ZetaTwoHilbert ZetaTwoOptimizerStage QShiftedReciprocal
open QSquarefreeResidualTail

theorem displacement_energy_bound :
    8 * ‖displacement‖ ^ 2 ≤ ‖limitingResidual‖ ^ 2 := by
  apply sharp_displacement_energy_bound
  · exact Submodule.inner_right_of_mem_orthogonal
      displacement_mem limitingResidual_mem_squarefree_orthogonal
  · have h := Submodule.inner_right_of_mem_orthogonal displacement_mem
      witness_mem_orthogonal
    rw [witness, inner_sub_right, real_inner_self_eq_norm_sq,
      pResidual_eq_residual_add_displacement] at h
    exact sub_eq_zero.mp h

end RiemannResearch.RH.QSquarefreeDisplacementRigidity
