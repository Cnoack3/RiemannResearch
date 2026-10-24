/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteFeasibleGramRepair
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.Analysis.FiniteConstrainedProjection
import Mathlib.Tactic.Linarith

/-!
# Complete-norm competitors and enlargement of feasible head repair

Source: exact-head averaging research agenda, priorities 2 and 5, 24 October 2026.
These comparisons use complete Hilbert norms and allow dependent observations.
They identify which quantity decreases when a dictionary is enlarged: total
constrained error. The correction cost alone need not decrease.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteFeasibleGramRepair

open FiniteHilbertGram FiniteConstrainedProjection

variable {ι κ η H : Type*} [Fintype ι] [Fintype κ] [Fintype η]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [Fintype η] in
/-- Adding compatible observations cannot decrease minimum normal energy.
No independence or injectivity of the observation indexing is needed. -/
theorem normal_energy_mono_of_constraints
    (u : ι → H) (v : κ → H) (b d : ι → ℝ) (c e : κ → ℝ)
    (hd : ∀ i, inner ℝ (u i) (Fintype.linearCombination ℝ u d) = b i)
    (he : ∀ i, inner ℝ (v i) (Fintype.linearCombination ℝ v e) = c i)
    (f : ι → κ) (hf : ∀ i, v (f i) = u i) (hsource : ∀ i, c (f i) = b i) :
    (∑ i, d i * b i) ≤ ∑ i, e i * c i := by
  rw [← normal_energy u b d hd, ← normal_energy v c e he]
  apply feasible_minimizes u b d hd (Fintype.linearCombination ℝ v e)
  intro i
  rw [← hf i]
  exact (he (f i)).trans (hsource i)

omit [Fintype η] in
/-- A finite exact-head competitor bounds the signed target correction cost.
The projection error is subtracted, rather than discarded. -/
theorem normal_cost_le_competitor_error_sub {v : ι → H}
    (hv : LinearIndependent ℝ v) (h : κ → H) (x : H) (d : κ → ℝ)
    (hn : ∀ i, inner ℝ (projectedRow hv h i)
      (Fintype.linearCombination ℝ (projectedRow hv h) d) = headMismatch hv h x i)
    (c : ι → ℝ)
    (hc : ∀ i, inner ℝ (h i) (Fintype.linearCombination ℝ v c) = inner ℝ (h i) x) :
    (∑ i, d i * headMismatch hv h x i) ≤
      ‖x - Fintype.linearCombination ℝ v c‖ ^ 2 - ‖projectionResidual hv x‖ ^ 2 := by
  have he := repaired_error_completion hv h x d hn c hc
  have hp := sq_nonneg ‖Fintype.linearCombination ℝ v c -
    (Fintype.linearCombination ℝ v (inverseCoeff hv x) +
      Fintype.linearCombination ℝ (projectedRow hv h) d)‖
  linarith only [he, hp]

omit [Fintype η] in
/-- A verified competitor supplies the actual target-direction budget.
No inverse of the head Gram or independence of its rows is needed. -/
theorem directional_bound_of_competitor {v : ι → H}
    (hv : LinearIndependent ℝ v) (h : κ → H) (x : H) (d : κ → ℝ)
    (hn : ∀ i, inner ℝ (projectedRow hv h i)
      (Fintype.linearCombination ℝ (projectedRow hv h) d) = headMismatch hv h x i)
    (c : ι → ℝ)
    (hc : ∀ i, inner ℝ (h i) (Fintype.linearCombination ℝ v c) = inner ℝ (h i) x)
    (a : κ → ℝ) :
    (∑ i, a i * headMismatch hv h x i) ^ 2 ≤
      (‖x - Fintype.linearCombination ℝ v c‖ ^ 2 - ‖projectionResidual hv x‖ ^ 2) *
        ‖Fintype.linearCombination ℝ (projectedRow hv h) a‖ ^ 2 := by
  have hb := normal_cost_le_competitor_error_sub hv h x d hn c hc
  rw [← normal_energy (projectedRow hv h) (headMismatch hv h x) d hn] at hb
  exact (normal_direction_bound (projectedRow hv h) (headMismatch hv h x) d a hn).trans
    (mul_le_mul_of_nonneg_right hb (sq_nonneg _))

/-- Enlarging the dictionary cannot increase the sum of projection error and
normal correction cost, for the same target and observation constraints. -/
theorem constrained_error_antitone_of_span_le {v : ι → H} {w : η → H}
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w)
    (h : κ → H) (x : H) (d e : κ → ℝ)
    (hd : ∀ i, inner ℝ (projectedRow hv h i)
      (Fintype.linearCombination ℝ (projectedRow hv h) d) = headMismatch hv h x i)
    (he : ∀ i, inner ℝ (projectedRow hw h i)
      (Fintype.linearCombination ℝ (projectedRow hw h) e) = headMismatch hw h x i)
    (hvw : synthesisSpan v ≤ synthesisSpan w) :
    ‖projectionResidual hw x‖ ^ 2 + ∑ i, e i * headMismatch hw h x i ≤
      ‖projectionResidual hv x‖ ^ 2 + ∑ i, d i * headMismatch hv h x i := by
  let y : H := Fintype.linearCombination ℝ v (inverseCoeff hv x) +
    Fintype.linearCombination ℝ (projectedRow hv h) d
  have hymem : y ∈ synthesisSpan v := by
    apply Submodule.add_mem
    · exact synthesis_mem _ _
    · rw [Fintype.linearCombination_apply]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (synthesis_mem _ _)
  have hyw := hvw hymem
  rw [synthesisSpan, ← Fintype.range_linearCombination] at hyw
  obtain ⟨c, hc⟩ := hyw
  have hcobs : ∀ i, inner ℝ (h i) (Fintype.linearCombination ℝ w c) =
      inner ℝ (h i) x := by
    intro i
    rw [hc]
    exact repaired_observation hv h x d hd i
  have hb := normal_cost_le_competitor_error_sub hw h x e he c hcobs
  have hyerr := repaired_error_identity hv h x d hd
  change ‖x - y‖ ^ 2 = _ at hyerr
  rw [hc] at hb
  linarith only [hb, hyerr]

/-- The correction cost may increase, but its increase is bounded by the
decrease in the unconstrained projection error. -/
theorem normal_cost_variation_le_projection_gain {v : ι → H} {w : η → H}
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w)
    (h : κ → H) (x : H) (d e : κ → ℝ)
    (hd : ∀ i, inner ℝ (projectedRow hv h i)
      (Fintype.linearCombination ℝ (projectedRow hv h) d) = headMismatch hv h x i)
    (he : ∀ i, inner ℝ (projectedRow hw h i)
      (Fintype.linearCombination ℝ (projectedRow hw h) e) = headMismatch hw h x i)
    (hvw : synthesisSpan v ≤ synthesisSpan w) :
    (∑ i, e i * headMismatch hw h x i) - (∑ i, d i * headMismatch hv h x i) ≤
      ‖projectionResidual hv x‖ ^ 2 - ‖projectionResidual hw x‖ ^ 2 := by
  have hb := constrained_error_antitone_of_span_le hv hw h x d e hd he hvw
  linarith only [hb]

end RiemannResearch.Analysis.FiniteFeasibleGramRepair
