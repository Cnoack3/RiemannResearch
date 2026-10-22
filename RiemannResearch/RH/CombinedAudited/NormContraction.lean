/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Tactic.Linarith

/-!
# Norm Contraction

Adapted from the user-provided archive `combined_audited_lean_sources.zip`,
which describes these declarations as extracted from
`combined_audited_manuscript(4).pdf`. The manuscript itself was not bundled
with this continuation, so this module records archive provenance rather than
claiming page-level source verification.
-/

open Filter

namespace RiemannResearch.RH.CombinedAudited

variable {E F G : Type*} [SeminormedAddCommGroup E]
  [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]

/-- A deliberately structure-free formulation of a norm contraction. -/
def IsNormContraction (T : E → F) : Prop := ∀ x, ‖T x‖ ≤ ‖x‖

@[simp] theorem isNormContraction_id :
    IsNormContraction (fun x : E => x) := by
  intro x
  rfl

/-- Contractions are closed under composition. -/
theorem IsNormContraction.comp {S : F → G} {T : E → F}
    (hS : IsNormContraction S) (hT : IsNormContraction T) :
    IsNormContraction (fun x => S (T x)) := by
  intro x
  exact le_trans (hS (T x)) (hT x)

/-- The norm and squared-norm forms of the contraction condition are equivalent. -/
theorem isNormContraction_iff_sq (T : E → F) :
    IsNormContraction T ↔ ∀ x, ‖T x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  constructor
  · intro h x
    have hx := h x
    nlinarith [norm_nonneg (T x), norm_nonneg x]
  · intro h x
    have hx := h x
    nlinarith [norm_nonneg (T x), norm_nonneg x]

/-- A pointwise limit of norm contractions is again a norm contraction. This
is the finite-cutoff-to-completed-operator closure step, separate from proving
that any concrete cutoff operator is contractive. -/
theorem isNormContraction_of_pointwise_limit
    (Tn : ℕ → E → F) (T : E → F)
    (hcontract : ∀ n, IsNormContraction (Tn n))
    (hlim : ∀ x, Tendsto (fun n => Tn n x) atTop (nhds (T x))) :
    IsNormContraction T := by
  intro x
  have hnorm :
      Tendsto (fun n => ‖Tn n x‖) atTop (nhds ‖T x‖) :=
    continuous_norm.continuousAt.tendsto.comp (hlim x)
  exact le_of_tendsto hnorm
    (Filter.Eventually.of_forall (fun n => hcontract n x))

end RiemannResearch.RH.CombinedAudited
