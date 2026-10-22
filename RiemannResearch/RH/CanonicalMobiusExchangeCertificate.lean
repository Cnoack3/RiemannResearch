/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusTriangular
import RiemannResearch.RH.BalancedSquarefreeCrossing

/-!
# Pointwise canonical exchange and exact common-head cancellation

Source: user-provided CRT and Four Improvements continuation, 6–7 October 2026.
The extensions retain complete signed identities and correction squares.


This supplies the pointwise exchange requested in the attached affine
candidate from the existing Hilbert-vector exchange, retaining its boundary
coefficient. The exchange vanishes on every previously matched head site.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto.BalancedSquarefree
open RiemannResearch.RH.ArithmeticCumulative

theorem trial_successor_exchange (Y j : ℕ) :
    trial (Y+1) j - trial Y j = mobiusReciprocalSum (Y+1) *
      (((Y+2 : ℕ) : ℝ) * residueFraction (Y+2) j -
        ((Y+1 : ℕ) : ℝ) * residueFraction (Y+1) j) := by
  have he := congrArg (fun x => hilbertSequenceLinear x j)
    (canonicalMobiusHilbert_succ_sub Y)
  simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at he
  change hilbertSequence (canonicalMobiusHilbert (Y+1)) j -
    hilbertSequence (canonicalMobiusHilbert Y) j =
    mobiusReciprocalSum (Y+1) * hilbertSequence (consecutiveResidueHilbert Y) j at he
  simpa only [canonicalMobiusHilbert_sequence, consecutiveResidueHilbert_sequence,
    trial] using he

theorem trial_successor_exchange_head_zero (Y j : ℕ) (hj : j ≤ Y) :
    trial (Y+1) j - trial Y j = 0 := by
  have he := congrArg (fun x => hilbertSequenceLinear x j)
    (canonicalMobiusHilbert_succ_sub Y)
  simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at he
  change hilbertSequence (canonicalMobiusHilbert (Y+1)) j -
    hilbertSequence (canonicalMobiusHilbert Y) j =
    mobiusReciprocalSum (Y+1) * hilbertSequence (consecutiveResidueHilbert Y) j at he
  simpa only [canonicalMobiusHilbert_sequence, consecutiveResidueHilbert_head_zero Y j hj,
    mul_zero, trial] using he

end RiemannResearch.RH.Pareto.BalancedSquarefree
