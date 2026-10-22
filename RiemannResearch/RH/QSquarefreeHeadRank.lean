/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeHeadRepair
import RiemannResearch.RH.QSquarefreeJumpDistance
import RiemannResearch.Analysis.FiniteHilbertConstraints
import RiemannResearch.Analysis.FiniteConstrainedProjection
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# The unavoidable rank defect of squarefree physical heads

Source: user-provided continuation agenda, 22 October 2026, Section 5,
and the existing checked square-jump identity. These corollaries identify
why full-row independence cannot be used for actual physical heads of
length at least four. They do not obstruct the constant-one target, which
satisfies the same relation and has the existing legal affine baselines.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QSquarefreeHeadRank

open ZetaTwoHilbert ZetaTwoProbability SquarefreeRadicalDifference
open QSquarefreeJumpDistance QSquarefreeHeadRepair
open Analysis.FiniteHilbertGram Analysis.FiniteHilbertConstraints
open Analysis.FiniteConstrainedProjection

/-- Every legal dictionary has the nonzero signed physical row relation
`row 4 - row 3 = row 2 - row 1`, before any Gram inverse is considered. -/
theorem four_head_relation (F : QHilbert) (hF : F ∈ qSquarefreeCRTSpan) :
    qSequence F 4 - qSequence F 3 = qSequence F 2 - qSequence F 1 := by
  have h := squareJumpWitness_inner_eq_zero 2 (by decide) F
    (qSquarefreeCRTSpan.le_topologicalClosure hF)
  rw [squareJumpWitness_inner 2 (by decide)] at h
  change (qSequence F 4 - qSequence F 3) -
    (qSequence F 2 - qSequence F 1) = 0 at h
  exact sub_eq_zero.mp h

/-- The physical head map is not onto once the first four sites are included.
In particular, coordinate-unit interpolants cannot certify full row rank. -/
theorem not_all_legal_heads (M : ℕ) (hM : 4 ≤ M) :
    ¬ ∀ b : Fin M → ℝ, ∃ F : QHilbert, F ∈ qSquarefreeCRTSpan ∧
      ∀ i : Fin M, qSequence F (i.val + 1) = b i := by
  intro h
  obtain ⟨F, hF, hh⟩ := h (fun i => if i.val = 0 then 1 else 0)
  have h1 := hh ⟨0, by omega⟩
  have h2 := hh ⟨1, by omega⟩
  have h3 := hh ⟨2, by omega⟩
  have h4 := hh ⟨3, by omega⟩
  change qSequence F 1 = 1 at h1
  change qSequence F 2 = 0 at h2
  change qSequence F 3 = 0 at h3
  change qSequence F 4 = 0 at h4
  have hr := four_head_relation F hF
  linarith

/-- The complete projected physical rows are dependent for every legal
dictionary when `M ≥ 4`. Thus their Gram `C G⁻¹ Cᵀ` must be treated on its
feasible range, using rank-free repair or independent reduced observations. -/
theorem not_independent_projected_heads {ι : Type*} [Fintype ι]
    {v : ι → QHilbert} (hv : LinearIndependent ℝ v)
    (hlegal : ∀ i, v i ∈ qSquarefreeCRTSpan) (M : ℕ) (hM : 4 ≤ M) :
    ¬ LinearIndependent ℝ (projectedRow hv (headObservation M)) := by
  intro hr
  apply not_all_legal_heads M hM
  intro b
  refine ⟨minimumVector hr b, ?_, ?_⟩
  · unfold minimumVector
    apply legal_synthesis
    intro i
    exact legal_synthesis v hlegal _
  · intro i
    rw [← headObservation_inner M i]
    unfold minimumVector
    rw [projectedRow_pairing_rowSynthesis]
    exact minimumVector_observation hr b i

end RiemannResearch.RH.QSquarefreeHeadRank
