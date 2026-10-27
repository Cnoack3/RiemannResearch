/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QBoundedSubspaceEvaluation
import RiemannResearch.RH.QBoundedResidueProjection
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.Analysis.SingleDirectionProjection
import RiemannResearch.Analysis.LogSquareTail
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.QSingleConductorProjection
import RiemannResearch.RH.QSingleConductorPrerequisites
import RiemannResearch.RH.QPolylogTailEnergy
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform response of one conductor over a fixed finite bounded space

Source: `SingleConductorProjectionBound.md`.

The physical logarithmic estimate holds uniformly in the conductor and in
all unit inputs, strengthening the paper's constant-target statement. It
implies a complete weighted-energy bound with four logarithmic powers.
The final corollaries use the actual canonical squarefree legal stage;
boundedness of that stage is proved, not assumed as an arithmetic provider.
The constants may depend on the fixed stage, so these results do not
supply the growing-stage estimate required by the RH criterion.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSingleConductorUniform
open ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal
open QBoundedSubspaceEvaluation QBoundedResidueProjection
open QSingleConductorProjection QSingleConductorPrerequisites
open RiemannResearch.Analysis.SingleDirectionProjection
open QPolylogTailEnergy
open RiemannResearch.Analysis

/-- Project the smoothed orthogonal residual onto a fixed space extended by
one genuine residue atom. -/
def response (U : Submodule ℝ QHilbert) [FiniteDimensional ℝ U]
    (d : ℕ) (f : QHilbert) : QHilbert :=
  (U ⊔ Submodule.span ℝ ({qResidue d} : Set QHilbert)).starProjection
    (B (f - (U ⊔ Submodule.span ℝ ({qResidue d} : Set QHilbert)).starProjection f))

/-- Uniform logarithmic physical response for every input. This is stronger
than the constant-target theorem in the source paper. -/
theorem exists_uniform_response_physical_bound
    (U : Submodule ℝ QHilbert) [FiniteDimensional ℝ U]
    (hbounded : ∀ u : QHilbert, u ∈ U →
      ∃ C : ℝ, ∀ n : ℕ, |qSequence u n| ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℕ, 2 ≤ d → ∀ f : QHilbert, ∀ n : ℕ,
      |qSequence (response U d f) n| ≤ C * ‖f‖ * (1 + Real.log (n : ℝ)) := by
  obtain ⟨M, hM, hb⟩ := exists_uniform_physical_bound U hbounded
  obtain ⟨D, hD⟩ := exists_residue_residual_norm_sq_lower_threshold U M hM hb
  obtain ⟨Csmall, hCs, hsmall⟩ :=
    exists_finite_conductor_projection_physical_bound U hbounded D
  let Clarge := M + 4 * (zetaTwo + M) * (2 + 4 * M ^ 2 / zetaTwo)
  have hzeta := zetaTwo_pos
  have hCl : 0 ≤ Clarge := by dsimp [Clarge]; positivity
  refine ⟨max Csmall Clarge, (le_max_left _ _).trans' hCs, ?_⟩
  intro d hd f n
  by_cases hn : n = 0
  · subst n
    simp only [qSequence_zero, abs_zero, Nat.cast_zero, Real.log_zero, add_zero, mul_one]
    exact mul_nonneg ((le_max_left _ _).trans' hCs) (norm_nonneg f)
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hnpos)
  by_cases hDd : D ≤ d
  · have hl := response_bound_of_residual_lower U M hM hb d hd (hD d hDd).2 f n hnpos
    exact hl.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right Csmall Clarge) (norm_nonneg f))
      (by linarith))
  · have hnorm : ‖B (f -
        (U ⊔ Submodule.span ℝ ({qResidue d} : Set QHilbert)).starProjection f)‖ ≤ ‖f‖ :=
      (B_norm_le _).trans (residual_norm_le _ f)
    calc
      _ ≤ Csmall * ‖B (f -
          (U ⊔ Submodule.span ℝ ({qResidue d} : Set QHilbert)).starProjection f)‖ :=
        hsmall d (by omega) _ n
      _ ≤ Csmall * ‖f‖ := mul_le_mul_of_nonneg_left hnorm hCs
      _ ≤ max Csmall Clarge * ‖f‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg f)
      _ ≤ max Csmall Clarge * ‖f‖ * (1 + Real.log (n : ℝ)) := by
        have hp : 0 ≤ max Csmall Clarge * ‖f‖ :=
          mul_nonneg ((le_max_left _ _).trans' hCs) (norm_nonneg f)
        nlinarith

/-- The complete weighted energy is bounded by a constant times input energy,
uniformly over the newly adjoined conductor. -/
theorem exists_uniform_response_weighted_energy_bound
    (U : Submodule ℝ QHilbert) [FiniteDimensional ℝ U]
    (hbounded : ∀ u : QHilbert, u ∈ U →
      ∃ C : ℝ, ∀ n : ℕ, |qSequence u n| ≤ C) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ d : ℕ, 2 ≤ d → ∀ f : QHilbert,
      Summable (polylogWeightedEnergyTerm 4 (response U d f)) ∧
      (∑' n : ℕ, polylogWeightedEnergyTerm 4 (response U d f) n) ≤ E * ‖f‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_response_physical_bound U hbounded
  have hzeta := zetaTwo_pos
  let S := ∑' n : ℕ, 1 / ((n : ℝ) * (6 + Real.log (n : ℝ)) ^ 2)
  have hS : 0 ≤ S := tsum_nonneg (fun n => by positivity)
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) * (6 + Real.log (n : ℝ)) ^ 2)) := by
    simpa only [Real.rpow_two] using summable_shifted_log_square
  refine ⟨(C ^ 2 / zetaTwo) * S, mul_nonneg (by positivity) hS, ?_⟩
  intro d hd f
  have hCf : 0 ≤ C * ‖f‖ := mul_nonneg hC (norm_nonneg f)
  have henv (n : ℕ) : |qSequence (response U d f) n| ≤
      (C * ‖f‖) * (6 + Real.log (n : ℝ)) ^ 1 := by
    simpa only [pow_one] using (hb d hd f n).trans
      (mul_le_mul_of_nonneg_left (by linarith :
        1 + Real.log (n : ℝ) ≤ 6 + Real.log (n : ℝ)) hCf)
  have hsum : Summable (polylogWeightedEnergyTerm 4 (response U d f)) := by
    simpa only [show 2 * 1 + 2 = (4 : ℕ) by omega] using
      polylogWeightedEnergyTerm_summable (response U d f) 1 (C * ‖f‖) hCf henv
  refine ⟨hsum, ?_⟩
  have hterm (n : ℕ) : polylogWeightedEnergyTerm 4 (response U d f) n ≤
      ((C * ‖f‖) ^ 2 / zetaTwo) *
        (1 / ((n : ℝ) * (6 + Real.log (n : ℝ)) ^ 2)) := by
    simpa only [show 2 * 1 + 2 = (4 : ℕ) by omega] using
      polylogWeightedEnergyTerm_le_log_square (response U d f) 1 n (C * ‖f‖) (henv n)
  calc
    _ ≤ ∑' n : ℕ, ((C * ‖f‖) ^ 2 / zetaTwo) *
        (1 / ((n : ℝ) * (6 + Real.log (n : ℝ)) ^ 2)) :=
      hsum.tsum_le_tsum hterm (hs.mul_left _)
    _ = ((C * ‖f‖) ^ 2 / zetaTwo) * S := tsum_mul_left
    _ = _ := by ring

/-- The fixed canonical squarefree legal stage supplies all boundedness
hypotheses. The existential constant is allowed to depend on N. -/
theorem stage_uniform_response_physical_bound (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℕ, 2 ≤ d → ∀ f : QHilbert, ∀ n : ℕ,
      |qSequence (response (ZetaTwoOptimizerStage.stage N) d f) n| ≤
        C * ‖f‖ * (1 + Real.log (n : ℝ)) :=
  exists_uniform_response_physical_bound (ZetaTwoOptimizerStage.stage N)
    (stage_physical_bounded N)

/-- Uniform complete weighted energy for one extra conductor over each fixed
canonical squarefree stage, with no assumed arithmetic estimate. -/
theorem stage_uniform_response_weighted_energy_bound (N : ℕ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ d : ℕ, 2 ≤ d → ∀ f : QHilbert,
      Summable (polylogWeightedEnergyTerm 4
        (response (ZetaTwoOptimizerStage.stage N) d f)) ∧
      (∑' n : ℕ, polylogWeightedEnergyTerm 4
        (response (ZetaTwoOptimizerStage.stage N) d f) n) ≤ E * ‖f‖ ^ 2 :=
  exists_uniform_response_weighted_energy_bound (ZetaTwoOptimizerStage.stage N)
    (stage_physical_bounded N)

end RiemannResearch.RH.QSingleConductorUniform
