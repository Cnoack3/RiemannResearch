/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimeResamplingPoincare
import RiemannResearch.RH.QPrimeProjectionSharpness
import RiemannResearch.RH.QPrimeJumpEnergyIdentity
import RiemannResearch.RH.QPairVariance
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Data.ENNReal.Real

/-!
# Sharpness for the actual complete countable prime Dirichlet energy

Source: the centered dyadic equality witness in the user's prime-resampling
agenda. The witness saturates the actual infinite-kernel comparison, with
strictly positive finite pair variance and Dirichlet energy.
-/

noncomputable section
open scoped ENNReal
namespace RiemannResearch.RH.QPrimeResampling
open ZetaTwoHilbert QPairVariance PrimeResampling

/-- Exact pair variance of the centered actual conductor-two atom. -/
theorem pairVariance_dyadicCenteredAtom :
    pairVariance (qSequence dyadicCenteredAtom) =
      ENNReal.ofReal (‖dyadicCenteredAtom‖ ^ 2) := by
  rw [pairVariance_qSequence, dyadicCenteredAtom_mean_zero, zero_pow (by decide : 2 ≠ 0),
    sub_zero]

/-- Its full arithmetic-prime Dirichlet energy equals the same finite value. -/
theorem dirichletEnergy_dyadicCenteredAtom :
    dirichletEnergy (qSequence dyadicCenteredAtom) =
      ENNReal.ofReal (‖dyadicCenteredAtom‖ ^ 2) := by
  rw [dirichletEnergy_qSequence_eq]
  exact primeProjectionEnergy_dyadicCenteredAtom

theorem pairVariance_dyadicCenteredAtom_pos :
    0 < pairVariance (qSequence dyadicCenteredAtom) := by
  rw [pairVariance_dyadicCenteredAtom]
  exact ENNReal.ofReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr dyadicCenteredAtom_ne_zero))

/-- A strictly positive actual-sequence equality witness proves the gap-one
constant is sharp for the complete countable arithmetic kernel. -/
theorem prime_resampling_poincare_equality_witness :
    ∃ g : ℕ → ℝ, pairVariance g = dirichletEnergy g ∧ 0 < pairVariance g := by
  refine ⟨qSequence dyadicCenteredAtom, ?_, pairVariance_dyadicCenteredAtom_pos⟩
  rw [pairVariance_dyadicCenteredAtom, dirichletEnergy_dyadicCenteredAtom]

end RiemannResearch.RH.QPrimeResampling
