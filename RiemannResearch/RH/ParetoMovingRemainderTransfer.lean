/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MovingOrthogonalEnergy
import RiemannResearch.Analysis.WeightedScalarEnergy
import RiemannResearch.RH.ParetoFirstSitePrimeContrastPerturbations
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Conditional transfer from moving Hilbert remainders to the actual CRT contrasts

Source: user-provided October 1, 2026 Route B argument and the exact signed
identities in ParetoFirstSitePrimeContrastPerturbations. The generic analytic
provider is MovingOrthogonalEnergy.moving_pairing_summable.

The amplitude uses the complete signed moving CRT pairing and its actual
prime Schur energy. Its square is exactly the existing certificate, including
zero denominator cases. No proxy weights or raw rows are substituted.

CONDITIONAL RESEARCH REDUCTION. Open: construct a square-nonsummable arithmetic
model, an exact complete remainder representation, its orthonormal tests, and
a summable absolute total variation bound. Axiom audits do not discharge these
local mathematical hypotheses. This module does not prove unconditional RH.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.MovingOrthogonalEnergy
open RiemannResearch.Analysis.WeightedScalarEnergy

def primeMovingCRTAmplitude (j : ℕ) (f : ℕ → ℕ → ℝ) : ℝ :=
  primeBlockMovingCRTContrastPairing (2^j) (2^j) (f j) /
    Real.sqrt (primeBlockContrastEnergy (2^j) (2^j) (f j))

theorem primeMovingCRTAmplitude_sq (j : ℕ) (f : ℕ → ℕ → ℝ) :
    (primeMovingCRTAmplitude j f)^2 =
      primeBlockMovingCRTContrastCertificate (2^j) (2^j) (f j) := by
  unfold primeMovingCRTAmplitude primeBlockMovingCRTContrastCertificate
  rw [div_pow, Real.sq_sqrt]
  exact square_nonneg _ _ _ (fun i _ => primeSchurWeight_nonneg (2^j+i))

/-- CONDITIONAL RESEARCH REDUCTION: model divergence, the complete
signed representation, orthonormality and total variation remain explicit. -/
theorem riemannHypothesis_of_moving_remainder_model
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : ℕ → ℕ → ℝ) (m : ℕ → ℝ) (v R : ℕ → H)
    (hv : Orthonormal ℝ v)
    (hmodel : ¬ Summable (fun j => (m j)^2))
    (hrep : ∀ j, primeMovingCRTAmplitude j f - m j = inner ℝ (v j) (R j))
    (hvar : Summable (fun j => ‖R (j+1)-R j‖)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_movingCRTContrast_not_summable f
  intro hs
  have ha : Summable (fun j => (primeMovingCRTAmplitude j f)^2) := by
    simpa only [primeMovingCRTAmplitude_sq] using hs
  have he : Summable (fun j => (primeMovingCRTAmplitude j f-m j)^2) := by
    simpa only [hrep] using moving_pairing_summable v R hv hvar
  have hm := model_square_summable (fun _ : ℕ => (1 : ℝ))
    (fun j => primeMovingCRTAmplitude j f) m (fun _ => by norm_num)
    (by simpa only [one_mul] using ha) (by simpa only [one_mul] using he)
  exact hmodel (by simpa only [one_mul] using hm)
end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
