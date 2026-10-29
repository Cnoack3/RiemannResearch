/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTInnovationGain
import RiemannResearch.RH.QCRTMinimumEnergy
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.RH.QCRTMovingPredictionGain
import RiemannResearch.RH.QSquarefreeHeadStep
import RiemannResearch.RH.QSquarefreeEnergyTransitions
import RiemannResearch.RH.QSquarefreeGapHeadCost
import RiemannResearch.RH.QSquarefreeAffineHead
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.QCRTCoprimeApproximation
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.Analysis.OrthogonalObservationInnovation
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Prime support of gains on the actual dense CRT schedule

Source: arithmetic continuation of the user-provided moving-prediction
agenda, 29 October 2026. Between cutoffs 2i+2 and 2i+4 only 2i+3 can
be prime. Seed independence then identifies the actual complete-Q minima.
These exact zero-gain statements do not bound costs on the other stages.
-/

namespace RiemannResearch.RH.QCRTDensePrimeSupport
noncomputable section
open ZetaTwoHilbert QSquarefreeLatticePackets QResidueHeadSpace QSquarefreeAffineHead
open QCRTPeriodHeadBalance QSquarefreeHeadStep QCRTMovingPredictionGain
open QSquarefreeEnergyTransitions QSquarefreeGapHeadCost QCRTCoprimeApproximation
open QCRTMinimumEnergy QCRTInnovationGain

theorem dense_primorial_eq_of_nonprime (i : ℕ) (hp : ¬ Nat.Prime (2 * i + 3)) :
    primorial (denseSchedule (i + 1) + 2) =
      primorial (denseSchedule i + 2) := by
  have he : ¬ Nat.Prime (2 * i + 4) := by
    intro hh
    rcases hh.eq_two_or_odd with hh | hh <;> omega
  change primorial (2 * (i + 1) + 2) = primorial (2 * i + 2)
  rw [show 2 * (i + 1) + 2 = (2 * i + 2 + 1) + 1 by omega]
  simp only [primorial_eq_prod_primesLE, Nat.primesLE_succ]
  simp only [show ¬ Nat.Prime (2 * i + 2 + 1 + 1) by convert he using 1,
    show ¬ Nat.Prime (2 * i + 2 + 1) by convert hp using 1,
    ↓reduceIte]

theorem dense_minimum_eq_of_nonprime (i : ℕ) (hp : ¬ Nat.Prime (2 * i + 3)) :
    minimumAt (denseSchedule i) (i + 1) =
      minimumAt (denseSchedule (i + 1)) (i + 1) := by
  have he := dense_primorial_eq_of_nonprime i hp
  have hn := seed_mem_dictionary (denseSchedule (i + 1))
  rw [he] at hn
  unfold minimumAt
  rw [he]
  symm
  apply exactHeadAdjustment_seed_independent _ (i + 1)
    (approximant (denseSchedule i)) (approximant (denseSchedule (i + 1)))
    (seed_mem_dictionary _) hn
  intro k hk hki
  rw [approximant_exact_head _ k hk (by dsimp [denseSchedule]; omega),
    approximant_exact_head _ k hk (by dsimp [denseSchedule]; omega)]

theorem dense_displacement_zero_of_nonprime (i : ℕ) (hp : ¬ Nat.Prime (2 * i + 3)) :
    denseDisplacement i = 0 := by
  rw [denseDisplacement, dense_minimum_eq_of_nonprime i hp, sub_self]

theorem dense_gain_zero_of_nonprime (i : ℕ) (hp : ¬ Nat.Prime (2 * i + 3)) :
    periodGain denseSchedule i = 0 := by
  change ‖denseDisplacement i‖ ^ 2 = 0
  rw [dense_displacement_zero_of_nonprime i hp, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]

theorem dense_prediction_eq_of_nonprime (i : ℕ) (hp : ¬ Nat.Prime (2 * i + 3)) :
    nextMismatch i = oldMismatch i := by
  unfold nextMismatch oldMismatch
  rw [dense_minimum_eq_of_nonprime i hp]

theorem dense_innovation_zero_of_nonprime (i : ℕ) (hp : ¬ Nat.Prime (2 * i + 3)) :
    innovationCapacity i = 0 := by
  have hk := stepNormal_mem (i + 2)
    (primorial (denseSchedule (i + 1) + 2)) (squarefreeAnchor i) (denseAnchor_mem i)
  have hd := zeroHeadSpan_le_dictionary _ (i + 2 - 1) (squarefreeAnchor i)
    (denseAnchor_mem i) hk
  have hh := zeroHeadSpan_le_headNull _ (i + 2 - 1) (squarefreeAnchor i)
    (by have := (squarefreeAnchor_spec i).1; omega) hk
  have hm : denseNormal i ∈ oldTangent i := by
    constructor
    · change denseNormal i ∈ dictionary
        (conductors (primorial (denseSchedule (i + 1) + 2))) at hd
      rw [dense_primorial_eq_of_nonprime i hp] at hd
      exact hd
    · intro k hk hki
      exact hh k hk (by omega)
  have hproj := Submodule.starProjection_eq_self_iff.mpr hm
  simp only [innovationCapacity, innovationNormal,
    RiemannResearch.Analysis.OrthogonalObservationInnovation.innovation,
    hproj, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]

theorem dense_energy_eq_of_nonprime_nonsquarefree (i : ℕ)
    (hp : ¬ Nat.Prime (2 * i + 3)) (hsf : ¬ Squarefree (i + 2)) :
    stageEnergy denseSchedule (i + 1) = stageEnergy denseSchedule i := by
  rw [stageEnergy_step denseSchedule denseSchedule_monotone denseSchedule_head,
    dense_gain_zero_of_nonprime i hp,
    headCost_eq_zero_of_nonsquarefree denseSchedule i (denseSchedule_head (i + 1)) hsf]
  ring

end
end RiemannResearch.RH.QCRTDensePrimeSupport
