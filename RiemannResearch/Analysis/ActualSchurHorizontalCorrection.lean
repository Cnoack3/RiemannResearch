/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.FiniteRationalCoshSchur
import RiemannResearch.Analysis.ActualGrowingPhaseGram

/-!
# Rational Schur coefficient for the complete zeta phase correction

The central bound uses the proved finite Schur certificate for every displacement
up to its fixed reference. The actual multiplicity-normalized tail retains its
finite harmonic cap. One dimension threshold works at every height.
-/

noncomputable section
open Filter Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments

open ActualZeroOrdinate FiniteHyperbolicHarmonicCap

theorem eventually_landauPhase_schur_finite_budget :
    ∀ᶠ d : ℕ in atTop, ∀ T : ℝ,
      ‖landauGram T d - phaseGram T d‖ ≤
        rationalSchurCoefficient * (1 + (d : ℝ)) * displacementMoment T 2 +
        strictTail T (1 / 10000000) / (Ncount 0 T : ℝ) * harmonicHyperbolicCap d := by
  filter_upwards [rationalSchurCertificate.eventually_copyCoshCorrection] with d hd T
  apply landauPhase_norm_le_moment_of_copy_bound T d (1 / 10000000)
    (rationalSchurCoefficient * (1 + (d : ℝ)))
    (mul_nonneg rationalSchurCertificate.coefficient_nonneg (by positivity))
  intro ρ _ hρ
  exact hd ρ hρ

end RiemannResearch.Analysis.ActualZeroPhaseMoments
