/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.StretchedTailWeights
import RiemannResearch.RH.QPhysicalTailEnergy
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Tactic.Positivity

/-!
# Stretched-weight tails of reciprocal-smoothed Q vectors

Source: the user-provided squarefree moving-head continuation, 26 October 2026.
The complete physical tail bound for any smoothed Q vector is multiplied by
the vanishing arithmetic decay. No squarefree or RH hypothesis is used.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QStretchedTailEnergy
open ZetaTwoHilbert ZetaTwoProbability QAnnihilatorTailEscape QShiftedReciprocal
open RiemannResearch.Analysis.StretchedTailWeights

/-- The unprojected reciprocal correction is negligible even at the
critical stretched tail weight. -/
theorem arithmeticWeight_B_tail_tendsto_zero (a : ℝ) (ha : 0 < a)
    (u : QHilbert) :
    Tendsto (fun N => arithmeticWeight a N * ‖tail N (B u)‖ ^ 2)
      atTop (𝓝 0) := by
  let C : ℝ := 2 * (Real.sqrt zetaTwo * ‖u‖) ^ 2 / zetaTwo
  have hlim : Tendsto (fun N => arithmeticDecay a N * C) atTop (𝓝 0) := by
    simpa only [zero_mul] using (arithmeticDecay_tendsto_zero a ha).mul_const C
  apply squeeze_zero
    (fun N => mul_nonneg (arithmeticWeight_nonneg a N) (sq_nonneg _)) _ hlim
  intro N
  have h := scaled_tail_energy_le_of_bounded (B u) N
    (Real.sqrt zetaTwo * ‖u‖) (by positivity) (B_physical_bound u)
  have hm := mul_le_mul_of_nonneg_left h (arithmeticDecay_pos a N).le
  simpa only [arithmeticWeight, arithmeticDecay, C, mul_assoc, mul_left_comm,
    mul_comm] using hm

end RiemannResearch.RH.QStretchedTailEnergy
