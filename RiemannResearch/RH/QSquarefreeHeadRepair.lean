/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.Analysis.FiniteConstrainedProjection
import RiemannResearch.Analysis.FiniteFeasibleGramRepair
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QSquarefreeExactHeadAverages
import RiemannResearch.RH.ZetaTwoCoordinateDual
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Complete-Q head repair with dependent observations

Source: user-provided continuation agenda, 22 October 2026, Section 5.
The finite algebra is unconditional. The uniform directional inequality for
actual legal dictionaries remains an explicit open arithmetic provider.
-/

noncomputable section
open scoped BigOperators Topology

namespace RiemannResearch.RH.QSquarefreeHeadRepair

open Analysis.FiniteHilbertGram Analysis.FiniteConstrainedProjection
open Analysis.FiniteFeasibleGramRepair
open ZetaTwoHilbert ZetaTwoProbability

def headObservation (M : ℕ) (i : Fin M) : QHilbert :=
  qSiteRiesz (i.val + 1)

theorem headObservation_inner (M : ℕ) (i : Fin M) (x : QHilbert) :
    inner ℝ (headObservation M i) x = qSequence x (i.val + 1) :=
  qSiteRiesz_inner _ (Nat.succ_pos _) x

theorem legal_synthesis {ι : Type*} [Fintype ι] (v : ι → QHilbert)
    (hv : ∀ i, v i ∈ qSquarefreeCRTSpan) (c : ι → ℝ) :
    Fintype.linearCombination ℝ v c ∈ qSquarefreeCRTSpan := by
  rw [Fintype.linearCombination_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hv i)

theorem projection_residual_sq_le_one {ι : Type*} [Fintype ι]
    {v : ι → QHilbert} (hv : LinearIndependent ℝ v) :
    ‖projectionResidual hv qOne‖ ^ 2 ≤ 1 := by
  have h := residual_completion hv qOne 0
  simp only [map_zero, sub_zero, qOne_norm_sq] at h
  change 1 = ‖projectionResidual hv qOne‖ ^ 2 + _ at h
  nlinarith [sq_nonneg ‖Fintype.linearCombination ℝ v (0 - inverseCoeff hv qOne)‖]

/-- Explicit normal-equation certificates supply legal physical exact heads
and a complete error bound. The observation rows may be dependent. -/
theorem closure_capacity_rh_of_bounded_normal_repairs
    (J : ℕ → ℕ) (v : ∀ M, Fin (J M) → QHilbert)
    (hv : ∀ M, LinearIndependent ℝ (v M))
    (hlegal : ∀ M i, v M i ∈ qSquarefreeCRTSpan)
    (d : ∀ M, Fin M → ℝ) (B : ℝ)
    (hn : ∀ M i, inner ℝ (projectedRow (hv M) (headObservation M) i)
      (Fintype.linearCombination ℝ (projectedRow (hv M) (headObservation M)) (d M)) =
        headMismatch (hv M) (headObservation M) qOne i)
    (hcost : ∀ M, ∑ i, d M i * headMismatch (hv M) (headObservation M) qOne i ≤ B) :
    qOne ∈ qSquarefreeCRTSpan.topologicalClosure ∧
      Filter.Tendsto QSquarefreeCapacity.capacity Filter.atTop Filter.atTop ∧
        RiemannHypothesis := by
  let F : ℕ → QHilbert := fun M =>
    Fintype.linearCombination ℝ (v M) (inverseCoeff (hv M) qOne) +
      Fintype.linearCombination ℝ (projectedRow (hv M) (headObservation M)) (d M)
  apply QSquarefreeExactHeadAverages.squarefree_closure_capacity_and_rh_of_bounded_exact_heads
    F (B := 1 + B)
  · intro M
    apply Submodule.add_mem
    · exact legal_synthesis _ (hlegal M) _
    · apply legal_synthesis
      intro i
      exact legal_synthesis _ (hlegal M) _
  · intro M
    have he := repaired_error_identity (hv M) (headObservation M) qOne (d M) (hn M)
    change ‖qOne - F M‖ ^ 2 = _ at he
    rw [he]
    exact add_le_add (projection_residual_sq_le_one (hv M)) (hcost M)
  · intro M k hk hkM
    let i : Fin M := ⟨k - 1, by omega⟩
    have he := repaired_observation (hv M) (headObservation M) qOne (d M) (hn M) i
    change inner ℝ (headObservation M i) (F M) = _ at he
    rw [headObservation_inner, headObservation_inner] at he
    have hi : i.val + 1 = k := by dsimp [i]; omega
    rw [hi, qSequence_qOne] at he
    simpa [qOneSequence, Nat.ne_of_gt hk] using he

/-- The exact directional dual is sufficient; it bounds only the correction
needed for the target, rather than every direction of the head inverse. -/
theorem closure_capacity_rh_of_directional_normal_repairs
    (J : ℕ → ℕ) (v : ∀ M, Fin (J M) → QHilbert)
    (hv : ∀ M, LinearIndependent ℝ (v M))
    (hlegal : ∀ M i, v M i ∈ qSquarefreeCRTSpan)
    (d : ∀ M, Fin M → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hn : ∀ M i, inner ℝ (projectedRow (hv M) (headObservation M) i)
      (Fintype.linearCombination ℝ (projectedRow (hv M) (headObservation M)) (d M)) =
        headMismatch (hv M) (headObservation M) qOne i)
    (hdual : ∀ M c, (∑ i, c i * headMismatch (hv M) (headObservation M) qOne i) ^ 2 ≤
      B * ‖Fintype.linearCombination ℝ
        (projectedRow (hv M) (headObservation M)) c‖ ^ 2) :
    qOne ∈ qSquarefreeCRTSpan.topologicalClosure ∧
      Filter.Tendsto QSquarefreeCapacity.capacity Filter.atTop Filter.atTop ∧
        RiemannHypothesis := by
  apply closure_capacity_rh_of_bounded_normal_repairs J v hv hlegal d B hn
  intro M
  rw [← normal_energy _ _ (d M) (hn M)]
  exact (normal_energy_le_iff _ _ (d M) (hn M) B hB).mpr (hdual M)

/-- A single directional estimate supplies feasibility as well as the
uniform complete repair bound. No independent rank or normal-solution
hypothesis remains in this conditional arithmetic reduction. -/
theorem closure_capacity_rh_of_uniform_directional_repairs
    (J : ℕ → ℕ) (v : ∀ M, Fin (J M) → QHilbert)
    (hv : ∀ M, LinearIndependent ℝ (v M))
    (hlegal : ∀ M i, v M i ∈ qSquarefreeCRTSpan)
    (B : ℝ) (hB : 0 ≤ B)
    (hdual : ∀ M c, (∑ i, c i * headMismatch (hv M) (headObservation M) qOne i) ^ 2 ≤
      B * ‖Fintype.linearCombination ℝ
        (projectedRow (hv M) (headObservation M)) c‖ ^ 2) :
    qOne ∈ qSquarefreeCRTSpan.topologicalClosure ∧
      Filter.Tendsto QSquarefreeCapacity.capacity Filter.atTop Filter.atTop ∧
        RiemannHypothesis := by
  have hex : ∀ M, ∃ d : Fin M → ℝ,
      (∀ i, inner ℝ (projectedRow (hv M) (headObservation M) i)
        (Fintype.linearCombination ℝ (projectedRow (hv M) (headObservation M)) d) =
          headMismatch (hv M) (headObservation M) qOne i) ∧
        ‖Fintype.linearCombination ℝ (projectedRow (hv M) (headObservation M)) d‖ ^ 2 ≤ B :=
    fun M => (bounded_normal_iff_directional _ _ B hB).mpr (hdual M)
  choose d hn hb using hex
  apply closure_capacity_rh_of_bounded_normal_repairs J v hv hlegal d B hn
  intro M
  rw [← normal_energy _ _ (d M) (hn M)]
  exact hb M

end RiemannResearch.RH.QSquarefreeHeadRepair
