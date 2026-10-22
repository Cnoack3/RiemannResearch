/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.OrderClosed

/-!
# Limits Positivity

Adapted from the user-provided archive `combined_audited_lean_sources.zip`,
which describes these declarations as extracted from
`combined_audited_manuscript(4).pdf`. The manuscript itself was not bundled
with this continuation, so this module records archive provenance rather than
claiming page-level source verification.
-/

open Filter

namespace RiemannResearch.RH.CombinedAudited

/-- A limit of nonnegative real numbers is nonnegative. -/
theorem nonnegative_limit {u : ℕ → ℝ} {L : ℝ}
    (hu : ∀ n, 0 ≤ u n) (hlim : Tendsto u atTop (nhds L)) : 0 ≤ L := by
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall hu)

/-- A vanishing correction cannot manufacture positivity in the limit. -/
theorem corrected_nonnegative_limit {q k : ℕ → ℝ} {Q : ℝ}
    (hnonneg : ∀ n, 0 ≤ q n + k n)
    (hq : Tendsto q atTop (nhds Q))
    (hk : Tendsto k atTop (nhds 0)) : 0 ≤ Q := by
  have hsum : Tendsto (fun n => q n + k n) atTop (nhds (Q + 0)) := hq.add hk
  have h := nonnegative_limit hnonneg hsum
  simpa using h

/-- Positivity on an exact family of compressions implies pointwise positivity. -/
theorem positivity_of_exact_cover {E ι : Type*} (q : E → ℝ) (P : ι → E → E)
    (hcover : ∀ x, ∃ i, P i x = x)
    (hpositive : ∀ i x, 0 ≤ q (P i x)) :
    ∀ x, 0 ≤ q x := by
  intro x
  obtain ⟨i, hi⟩ := hcover x
  rw [← hi]
  exact hpositive i x

/-- Positivity of convergent compressions passes to the limit. Unlike
`positivity_of_exact_cover`, this needs only convergence, but explicitly
requires continuity of the quadratic functional. -/
theorem positivity_of_convergent_compressions
    {X : Type*} [TopologicalSpace X]
    (q : X → ℝ) (P : ℕ → X → X)
    (hq : Continuous q)
    (hP : ∀ x, Tendsto (fun n => P n x) atTop (nhds x))
    (hpositive : ∀ n x, 0 ≤ q (P n x)) :
    ∀ x, 0 ≤ q x := by
  intro x
  have hlim : Tendsto (fun n => q (P n x)) atTop (nhds (q x)) :=
    hq.continuousAt.tendsto.comp (hP x)
  exact ge_of_tendsto hlim
    (Filter.Eventually.of_forall (fun n => hpositive n x))

end RiemannResearch.RH.CombinedAudited
