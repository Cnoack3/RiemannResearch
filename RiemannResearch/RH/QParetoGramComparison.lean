/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.Analysis.FiniteGramMetricComparison
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Complete Gram and inverse-Gram comparison between Q and Pareto

Source: the user's Pareto-to-Q transfer request, 15 October 2026.
All families below are arbitrary finite actual Q vectors; legal residue,
CRT carry, signed packet and constrained-family applications are included.

Inverse comparison uses the SAME right-hand side b in both Gram inverses.
The actual Q target mean is not asserted equal to the Pareto target mean.
The finite least-squares comparison instead retains each metric's own
normal equations and its own optimizer.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QParetoGramComparison
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoEquivalence
open QParetoMetric
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteGramCapacity

variable {ι : Type*}

def paretoFamily (v : ι → QHilbert) (i : ι) : ThresholdHilbert := toPareto (v i)

theorem paretoFamily_independent {v : ι → QHilbert} (hv : LinearIndependent ℝ v) :
    LinearIndependent ℝ (paretoFamily v) := by
  change LinearIndependent ℝ (toParetoLinear ∘ v)
  exact hv.map' toParetoLinear (LinearMap.ker_eq_bot.mpr paretoEquiv.injective)

/-- Every matrix entry has its exact signed correction. -/
theorem gramMatrix_entry_identity (v : ι → QHilbert) (i j : ι) :
    zetaTwo * gramMatrix v i j =
      gramMatrix (paretoFamily v) i j + metricPairing (v i) (v j) :=
  inner_identity (v i) (v j)

variable [Fintype ι]

theorem toPareto_synthesis (v : ι → QHilbert) (c : ι → ℝ) :
    toPareto (Fintype.linearCombination ℝ v c) =
      Fintype.linearCombination ℝ (paretoFamily v) c := by
  change toParetoLinear (∑ i, c i • v i) = _
  simp only [map_sum, map_smul]
  rfl

/-- Exact complete quadratic identity precedes the comparison bounds. -/
theorem gram_energy_identity (v : ι → QHilbert) (c : ι → ℝ) :
    zetaTwo * (∑ i, c i * gram v c i) =
      (∑ i, c i * gram (paretoFamily v) c i) +
        metricCorrection (Fintype.linearCombination ℝ v c) := by
  rw [← gram_quadratic, ← gram_quadratic, ← toPareto_synthesis]
  exact norm_identity _

theorem gram_energy_bounds (v : ι → QHilbert) (c : ι → ℝ) :
    ‖Fintype.linearCombination ℝ (paretoFamily v) c‖ ^ 2 ≤
        zetaTwo * ‖Fintype.linearCombination ℝ v c‖ ^ 2 ∧
      zetaTwo * ‖Fintype.linearCombination ℝ v c‖ ^ 2 ≤
        2 * ‖Fintype.linearCombination ℝ (paretoFamily v) c‖ ^ 2 := by
  rw [← toPareto_synthesis]
  exact ⟨toPareto_norm_sq_le _, zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq _⟩

/-- Every inverse-Gram source is controlled, including coordinate and capacity sources. -/
theorem capacity_bounds {v : ι → QHilbert} (hv : LinearIndependent ℝ v) (b : ι → ℝ) :
    (zetaTwo / 2) * capacity (paretoFamily_independent hv) b ≤ capacity hv b ∧
      capacity hv b ≤ zetaTwo * capacity (paretoFamily_independent hv) b := by
  have hupper := capacity_le_mul_of_energy_le (paretoFamily_independent hv) hv
    zetaTwo_pos.le (fun c => (gram_energy_bounds v c).1) b
  have henergy (c : ι → ℝ) :
      ‖Fintype.linearCombination ℝ v c‖ ^ 2 ≤
        (2 / zetaTwo) * ‖Fintype.linearCombination ℝ (paretoFamily v) c‖ ^ 2 := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ zetaTwo_pos).mpr
    simpa only [mul_comm] using (gram_energy_bounds v c).2
  have hlower := capacity_le_mul_of_energy_le hv (paretoFamily_independent hv)
    (show 0 ≤ 2 / zetaTwo by positivity [zetaTwo_pos]) henergy b
  refine ⟨?_, hupper⟩
  rw [div_mul_eq_mul_div] at hlower ⊢
  have hh := (le_div_iff₀ zetaTwo_pos).mp hlower
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  nlinarith only [hh]

/-- Literal matrix inverse quadratic forms, with no postulated inverse. -/
theorem inverse_matrix_quadratic_bounds [DecidableEq ι] {v : ι → QHilbert}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) :
    (zetaTwo / 2) * dotProduct b ((gramMatrix (paretoFamily v))⁻¹.mulVec b) ≤
        dotProduct b ((gramMatrix v)⁻¹.mulVec b) ∧
      dotProduct b ((gramMatrix v)⁻¹.mulVec b) ≤
        zetaTwo * dotProduct b ((gramMatrix (paretoFamily v))⁻¹.mulVec b) := by
  have he {w : ι → QHilbert} (hw : LinearIndependent ℝ w) :
      dotProduct b ((gramMatrix w)⁻¹.mulVec b) = capacity hw b := by
    rw [gramMatrix_inverseSource hw]
    unfold dotProduct capacity
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [he hv, he (paretoFamily_independent hv)] using capacity_bounds hv b

/-- Optimal full errors compare even though the two coefficient vectors differ. -/
theorem optimizer_error_bounds {v : ι → QHilbert} (hv : LinearIndependent ℝ v)
    (x : QHilbert) :
    ‖toPareto x - Fintype.linearCombination ℝ (paretoFamily v)
        (inverseCoeff (paretoFamily_independent hv) (toPareto x))‖ ^ 2 ≤
      zetaTwo * ‖x - Fintype.linearCombination ℝ v (inverseCoeff hv x)‖ ^ 2 ∧
    zetaTwo * ‖x - Fintype.linearCombination ℝ v (inverseCoeff hv x)‖ ^ 2 ≤
      2 * ‖toPareto x - Fintype.linearCombination ℝ (paretoFamily v)
        (inverseCoeff (paretoFamily_independent hv) (toPareto x))‖ ^ 2 := by
  let cq := inverseCoeff hv x
  let cp := inverseCoeff (paretoFamily_independent hv) (toPareto x)
  have hseq (c : ι → ℝ) :
      toPareto (x - Fintype.linearCombination ℝ v c) =
        toPareto x - Fintype.linearCombination ℝ (paretoFamily v) c := by
    change toParetoLinear (x - Fintype.linearCombination ℝ v c) = _
    rw [map_sub]
    change toPareto x - toPareto (Fintype.linearCombination ℝ v c) = _
    rw [toPareto_synthesis]
  have hqmin :
      ‖x - Fintype.linearCombination ℝ v cq‖ ^ 2 ≤
        ‖x - Fintype.linearCombination ℝ v cp‖ ^ 2 := by
    rw [residual_completion hv x cp]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hpmin :
      ‖toPareto x - Fintype.linearCombination ℝ (paretoFamily v) cp‖ ^ 2 ≤
        ‖toPareto x - Fintype.linearCombination ℝ (paretoFamily v) cq‖ ^ 2 := by
    rw [residual_completion (paretoFamily_independent hv) (toPareto x) cq]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hpq := toPareto_norm_sq_le (x - Fintype.linearCombination ℝ v cq)
  rw [hseq] at hpq
  have hqp := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq
    (x - Fintype.linearCombination ℝ v cp)
  rw [hseq] at hqp
  exact ⟨hpmin.trans hpq,
    (mul_le_mul_of_nonneg_left hqmin zetaTwo_pos.le).trans hqp⟩

end RiemannResearch.RH.QParetoGramComparison
