/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusBoundaryEnergy
import RiemannResearch.RH.QSquarefreeSublinearHeads
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.RH.QMobiusExactHead

/-!
# Complete Q energy of Möbius trials, including the measure correction
Source: the user's Mellin--Plancherel proposal, 30 October 2026.
The Pareto spectral integral alone is not the Q energy. The exact positive
Radon--Nikodym correction is retained.
-/

namespace RiemannResearch.RH.QMobiusBoundaryEnergy
open MeasureTheory
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer Pareto QParetoMetric
theorem exactHead_boundary_energy (N : ℕ) (hN : 0 < N) :
    zetaTwo * ‖QMobiusExactHead.exactHead N‖ ^ 2 =
      (1 / (2 * Real.pi)) * (∫ t : ℝ,
        (‖riemannZeta (MellinFrequency.criticalPoint t)‖ ^ 2 / (1 / 4 + t ^ 2)) *
          ‖correctedMobiusSymbol N (MellinFrequency.criticalPoint t)‖ ^ 2)
      + metricCorrection (QMobiusExactHead.exactHead N) := by
  rw [norm_identity, QSquarefreeSublinearHeads.toPareto_exactHead,
    canonicalMobius_boundary_zeta_energy N hN]
end RiemannResearch.RH.QMobiusBoundaryEnergy
