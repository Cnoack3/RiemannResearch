import RiemannResearch.Analysis.ShiftedLiftDefect
import RiemannResearch.RH.NoorRegularizedGram

/-!
# Exact arithmetic shifted-lift defect

Source: the supplied shifted-lift handoff and elementary square completion.
This module specializes the identity to the actual canonical minimizer.
All Gram matrices, signed sources, and full Hilbert norms are retained.
No arithmetic rate or unconditional RH conclusion is asserted.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto.Noor
open RiemannResearch.Analysis.CoefficientShift
open RiemannResearch.Analysis.ShiftedLift
open RiemannResearch.Analysis.ExhaustiveWalk
open CoefficientStabilization

/-- The exact square completion at the canonical arithmetic minimizer. -/
theorem finiteMinimum_defect (N : ℕ) (t r : ℝ) (ht : 0 < t)
    (hparam : r*t^2 = (1-r)^2) :
    r * finiteMinimum N t = r * (1-r) * energy N +
      ‖rightShiftLinear (finiteMinimizer N t) -
        r • (finiteMinimizer N t - finiteTarget N)‖^2 := by
  have htarget : ‖finiteTarget N‖^2 = energy N := by
    simp only [finiteTarget, hardyCoordinates.norm_map, energy, walkError,
      projection, finiteSpace]
  have h := regularizedEnergy_defect rightShiftLinear rightShift_norm
    (finiteTarget N) (finiteMinimizer N t)
    (finiteTarget_orthogonal N _ (finiteMinimizer_mem N t)) t r hparam
  rw [finiteMinimizer_energy N t ht, htarget] at h
  exact h

/-- Exact inverse-gain defect, retaining the complete finite arithmetic data. -/
theorem finiteInverseGain_defect (N : ℕ) (t r : ℝ) (ht : 0 < t)
    (hparam : r*t^2 = (1-r)^2) :
    r * (r * energy N - dotProduct (finiteShiftedSource N)
      ((finiteRegularizedGram N t)⁻¹.mulVec (finiteShiftedSource N))) =
      ‖rightShiftLinear (finiteMinimizer N t) -
        r • (finiteMinimizer N t - finiteTarget N)‖^2 := by
  have h := finiteMinimum_defect N t r ht hparam
  rw [finiteMinimum_eq_inverseGram N t ht] at h
  nlinarith [h]

/-- The matched-parameter gain obstruction is stronger than the preceding
`energy N / (1+t)` bound when r is the root in (0,1). -/
theorem finiteInverseGain_le_matched (N : ℕ) (t r : ℝ)
    (ht : 0 < t) (hr : 0 < r) (hparam : r*t^2 = (1-r)^2) :
    dotProduct (finiteShiftedSource N)
      ((finiteRegularizedGram N t)⁻¹.mulVec (finiteShiftedSource N)) ≤ r * energy N := by
  have h := finiteInverseGain_defect N t r ht hparam
  have hsq := sq_nonneg ‖rightShiftLinear (finiteMinimizer N t) -
    r • (finiteMinimizer N t - finiteTarget N)‖
  by_contra hnot
  have hpos : 0 < dotProduct (finiteShiftedSource N)
      ((finiteRegularizedGram N t)⁻¹.mulVec (finiteShiftedSource N)) - r * energy N :=
    sub_pos.mpr (lt_of_not_ge hnot)
  have hp := mul_pos hr hpos
  nlinarith

/-- Exact divided finite minimum with a full norm-square remainder. -/
theorem finiteMinimum_div_parameterized (N : ℕ) (s : ℝ)
    (hs : 0 < s) (hs1 : s < 1) :
    finiteMinimum N ((1-s^2)/s) / ((1-s^2)/s) =
      s * energy N +
      ‖rightShiftLinear (finiteMinimizer N ((1-s^2)/s)) -
        s^2 • (finiteMinimizer N ((1-s^2)/s) - finiteTarget N)‖^2 /
          (s * (1-s^2)) := by
  have ht : 0 < (1-s^2)/s := div_pos (by nlinarith) hs
  have htarget : ‖finiteTarget N‖^2 = energy N := by
    simp only [finiteTarget, hardyCoordinates.norm_map, energy, walkError,
      projection, finiteSpace]
  have h := regularizedEnergy_div_parameterized rightShiftLinear rightShift_norm
    (finiteTarget N) (finiteMinimizer N ((1-s^2)/s))
    (finiteTarget_orthogonal N _ (finiteMinimizer_mem N _)) s hs hs1
  rw [finiteMinimizer_energy N _ ht, htarget] at h
  exact h

end RiemannResearch.RH.Pareto.Noor
