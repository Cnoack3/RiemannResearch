/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimorialMatchedGram
import RiemannResearch.RH.QParetoDisplacementBounds
import RiemannResearch.Analysis.FiniteProjectionForcingCertificate

/-!
# Complete Pareto-first forcing on each primorial stage

Source: Pareto First Projections and Transfer to Q Research Draft,
11 November 2026, Priority 2. The full Pareto Gram and reciprocal Gram
have different roles. Both solves use the same complete divisor dictionary.
No decay of these finite forcing energies is assumed or concluded.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QParetoPrimorialForcing
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer
open QPrimorialMatchedGram QPrimorialMatchedDisplacement QParetoEquivalence
open QSquarefreePrimorialCofinality
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteProjectionForcingCertificate

theorem synthesisSpan_eq (n : ℕ) :
    synthesisSpan (paretoDivisorAtom n) = paretoStage n := by
  unfold synthesisSpan paretoStage paretoDivisorAtom
  rw [← divisor_span_eq_primorialStage]
  exact (map_span_range _).symm

def residual (n : ℕ) : ThresholdHilbert :=
  hilbertOne - (paretoStage n).starProjection hilbertOne

def forcing (n : ℕ) : ThresholdHilbert :=
  (paretoStage n).starProjection (reciprocalD (residual n))

def rhs (n : ℕ) : DivisorIndex n → ℝ :=
  cross (paretoDivisorAtom n) (reciprocalD (residual n))

def reciprocalGram (n : ℕ) : Matrix (DivisorIndex n) (DivisorIndex n) ℝ :=
  fun i j => inner ℝ (paretoDivisorAtom n i) (reciprocalD (paretoDivisorAtom n j))

theorem pareto_projection_expansion (n : ℕ) :
    (paretoStage n).starProjection hilbertOne =
      Fintype.linearCombination ℝ (paretoDivisorAtom n) (paretoCoefficients n) := by
  simpa only [paretoCoefficients, toPareto_qOne, synthesisSpan_eq n] using
    (synthesis_inverseCoeff_eq_projection (paretoDivisorAtom_independent n)
      (toPareto qOne)).symm

/-- The complete signed forcing row is the reciprocal source minus J times the P solve. -/
theorem rhs_signed (n : ℕ) (i : DivisorIndex n) :
    rhs n i = inner ℝ (paretoDivisorAtom n i) (reciprocalD hilbertOne) -
      ∑ j, reciprocalGram n i j * paretoCoefficients n j := by
  unfold rhs cross residual
  rw [pareto_projection_expansion, Fintype.linearCombination_apply, map_sub,
    inner_sub_right, map_sum, inner_sum]
  simp only [map_smul, real_inner_smul_right, reciprocalGram]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The canonical finite forcing energy uses the inverse of the complete P Gram. -/
theorem forcing_energy_inverseGram (n : ℕ) :
    ‖forcing n‖ ^ 2 =
      dotProduct (rhs n) ((gramMatrix (paretoDivisorAtom n))⁻¹.mulVec (rhs n)) := by
  simpa only [synthesisSpan_eq n, forcing, rhs] using
    projection_energy_inverseGram (paretoDivisorAtom_independent n)
      (reciprocalD (residual n))

theorem residual_eq_physical (n : ℕ) :
    residual n = toPareto (qOne - pOptimizer n) := by
  simp only [residual, pOptimizer, QParetoClosedProjectionComparison.toPareto_sub,
    QParetoClosedProjectionComparison.toPareto_pFit, toPareto_qOne]

/-- Both normal-equation errors are independently measured against the full Gram. -/
theorem forcing_upper_from_two_solves (n : ℕ) (c t : DivisorIndex n → ℝ)
    (e₁ e₂ : ℝ) (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂)
    (hfirst : defectEnergy (paretoDivisorAtom_independent n) hilbertOne c ≤ e₁ ^ 2)
    (hsecond : defectEnergy (paretoDivisorAtom_independent n)
      (reciprocalD (hilbertOne -
        Fintype.linearCombination ℝ (paretoDivisorAtom n) c)) t ≤ e₂ ^ 2) :
    ‖forcing n‖ ≤
      ‖Fintype.linearCombination ℝ (paretoDivisorAtom n) t‖ + e₂ + e₁ := by
  simpa only [synthesisSpan_eq n, one_mul, forcing, residual] using
    two_solve_upper (paretoDivisorAtom_independent n) reciprocalD 1 (by norm_num)
      (fun x => by simpa only [one_mul] using reciprocalD_norm_le x)
      hilbertOne c t e₁ e₂ he₁ he₂ hfirst hsecond

/-- Full trial-energy and full normal-error intervals certify the actual P error. -/
theorem pError_interval (n : ℕ) (c : DivisorIndex n → ℝ)
    (elo ehi dlo dhi : ℝ)
    (helo : elo ≤ ‖hilbertOne -
      Fintype.linearCombination ℝ (paretoDivisorAtom n) c‖ ^ 2)
    (hehi : ‖hilbertOne -
      Fintype.linearCombination ℝ (paretoDivisorAtom n) c‖ ^ 2 ≤ ehi)
    (hdlo : dlo ≤ defectEnergy (paretoDivisorAtom_independent n) hilbertOne c)
    (hdhi : defectEnergy (paretoDivisorAtom_independent n) hilbertOne c ≤ dhi) :
    elo - dhi ≤ pError n ∧ pError n ≤ ehi - dlo := by
  have h := minimum_error_interval (paretoDivisorAtom_independent n)
    hilbertOne c elo ehi dlo dhi helo hehi hdlo hdhi
  rw [pError, ← residual_eq_physical]
  simpa only [synthesisSpan_eq n, residual] using h

end RiemannResearch.RH.QParetoPrimorialForcing
