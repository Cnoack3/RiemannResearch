/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.DilationWaveletAlgebra
import RiemannResearch.RH.ArithmeticCumulativeEnergy

/-!
# Normalized residue vectors in the Pareto Hilbert space

Source: user-provided Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md,
Section 5. These declarations are moved verbatim from `Analysis/MellinNormalizedResidue`.
The vector and its sequence identity are used by arithmetic and Hilbert-space
modules independently of the analytic Mellin identities.
-/
noncomputable section
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative

/-- The physical generator g_d(n) = (n mod d)/d in the actual Hilbert space. -/
def normalizedResidueHilbert (d : ℕ) (hd : 0 < d) : ThresholdHilbert :=
  (1 / (d : ℝ)) • digitHilbert d 1 hd (by omega)

theorem normalizedResidueHilbert_sequence (d : ℕ) (hd : 0 < d) :
    hilbertSequence (normalizedResidueHilbert d hd) = residueFraction d := by
  change hilbertSequenceLinear ((1 / (d : ℝ)) • digitHilbert d 1 hd (by omega)) = _
  rw [map_smul]
  change (1 / (d : ℝ)) • hilbertSequence (digitHilbert d 1 hd (by omega)) = _
  rw [hilbertSequence_digitHilbert]
  funext n
  simp [residueFraction, digitSequence, smul_eq_mul, div_eq_mul_inv, mul_comm]

end RiemannResearch.RH.Pareto
