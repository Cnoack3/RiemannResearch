/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteSpectralResolvent
import RiemannResearch.RH.ParetoCompactTrialEnergy
import RiemannResearch.RH.ParetoActualSpectralLimits
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Actual conductor-scale source escape

Source: user-requested actual-source contrast work, 7 October 2026.
Exact full physical regularization, actual head source mass, compact charge
decay and the complete fourfold trial energy provide unconditional source
escape estimates at every fixed positive multiple of the conductor.
All actual weights and eigenvalues occur. The sufficient bounded-tail RH
consumer, with its arithmetic obligation still Open, is separated into
ParetoConductorTailCriterion.lean.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis
open FiniteSpectralBudget FiniteHeadTailSpectralRealization

/-- Actual complete source deficit versus any full-conductor legal trial.
Both complete physical squares and the literal negative head-error term remain. -/
theorem stageSourceDeficit_le_legal_trial (n N : ℕ) (hN : n+1 ≤ N)
    (v u : ThresholdHilbert) (hu : u ∈ finiteSpace n)
    (t : ℝ) (ht : 0 < t) :
    sourceDeficit Finset.univ
      (sourceWeight (stageSpectralHead n N hN) v) (stageEigenvalue n N hN) t ≤
      ‖v - compactHead N u‖^2 + ‖u - compactHead N u‖^2 / t -
        ‖v - (stageHeadSpace n N).starProjection v‖^2 := by
  let x : stageHeadSpace n N := stageHeadEquiv n N hN ⟨u, hu⟩
  let J := stageHeadInclusion n N
  let A := stageTailLift n N hN
  have hhead : J x = compactHead N u := by
    rfl
  have hlift : stageHeadLift n N hN x = u := by
    change ((stageHeadEquiv n N hN).symm
      ((stageHeadEquiv n N hN) ⟨u, hu⟩) : ThresholdHilbert) = u
    rw [LinearEquiv.symm_apply_apply]
  have htail : A x = u - compactHead N u := by
    change stageHeadLift n N hN x - (x : ThresholdHilbert) = _
    rw [hlift]
    exact congrArg (fun y : ThresholdHilbert => u-y) hhead
  have hid := physical_regularized_loss_identity J A t v x ht
  rw [headResolvent_smul, headResolvent_eq_frame_sourceResolvent] at hid
  have hrem : 0 ≤ regularizedEnergy A t
      (regularizedHead A t (t • J.toContinuousLinearMap.adjoint v) - x) := by
    unfold regularizedEnergy
    exact add_nonneg (mul_nonneg ht.le (sq_nonneg _)) (sq_nonneg _)
  have hD := sourceDeficit_eq_mass_sub_resolvent Finset.univ
    (sourceWeight (stageSpectralHead n N hN) v) (stageEigenvalue n N hN) t
    (fun i _ => eigenvalue_nonneg (stageTailLift n N hN) i) ht
  rw [actualSourceMass_eq_targetNorm_sub_headError n N hN v] at hD
  rw [hhead, htail] at hid
  change t * ‖v - compactHead N u‖^2 + ‖u - compactHead N u‖^2 =
    t * ‖v‖^2 - t^2 * sourceResolvent Finset.univ
      (sourceWeight (stageSpectralHead n N hN) v) (stageEigenvalue n N hN) t +
      regularizedEnergy A t
        (regularizedHead A t (t • J.toContinuousLinearMap.adjoint v) - x) at hid
  have hmul : t * (sourceDeficit Finset.univ
      (sourceWeight (stageSpectralHead n N hN) v) (stageEigenvalue n N hN) t +
      ‖v - (stageHeadSpace n N).starProjection v‖^2) ≤
      t * ‖v - compactHead N u‖^2 + ‖u - compactHead N u‖^2 := by
    rw [hD]
    nlinarith only [hid, hrem]
  have hbound : sourceDeficit Finset.univ
      (sourceWeight (stageSpectralHead n N hN) v) (stageEigenvalue n N hN) t +
      ‖v - (stageHeadSpace n N).starProjection v‖^2 ≤
      ‖v - compactHead N u‖^2 + ‖u - compactHead N u‖^2 / t := by
    calc
      _ = (t * (sourceDeficit Finset.univ
        (sourceWeight (stageSpectralHead n N hN) v) (stageEigenvalue n N hN) t +
        ‖v - (stageHeadSpace n N).starProjection v‖^2)) / t := by
          field_simp [ne_of_gt ht]
      _ ≤ (t * ‖v - compactHead N u‖^2 + ‖u - compactHead N u‖^2) / t :=
        div_le_div_of_nonneg_right hmul ht.le
      _ = _ := by field_simp [ne_of_gt ht]
  linarith only [hbound]

/-- The compact source's moving regularization loss has a supplied arithmetic
upper bound, using the actual corrected trial and its entire full norm. -/
theorem compactSpectrum_fourfold_sourceDeficit_le_trial (m : ℕ)
    (t : ℝ) (ht : 0 < t) :
    sourceDeficit Finset.univ (compactSpectrumWeight (4*m))
      (compactSpectrumEigenvalue (4*m)) t ≤
      (compactReciprocalSum (4*m+4))^2 +
        ‖compactCorrectedHilbert (4*m+4) (by omega)‖^2 / t := by
  let u := compactCorrectedHilbert (4*m+4) (by omega)
  have hu : u ∈ finiteSpace (4*m+3) := by
    have h := compactCorrectedHilbert_mem_conductorStage (4*m+4) (by omega)
    simpa only [show 4*m+4-1=4*m+3 by omega] using h
  have hD := stageSourceDeficit_le_legal_trial (4*m+3) (4*m+4) (by omega)
    twoThreeDual u hu t ht
  have hhead : ‖twoThreeDual-compactHead (4*m+4) u‖^2 ≤
      (compactReciprocalSum (4*m+4))^2 := by
    have h := compactCorrectedHilbert_head_energy_le_charge_sq (4*m+4) (by omega)
    rw [compactHead_sub, compactHead_twoThreeDual (4*m+4) (by omega)] at h
    exact h
  have htail : ‖u-compactHead (4*m+4) u‖^2 ≤ ‖u‖^2 := by
    have h := compactHead_pythagoras (4*m+4) u
    nlinarith [sq_nonneg ‖compactHead (4*m+4) u‖]
  have htdiv := div_le_div_of_nonneg_right htail ht.le
  change sourceDeficit Finset.univ (compactSpectrumWeight (4*m))
    (compactSpectrumEigenvalue (4*m)) t ≤ _ at hD
  change sourceDeficit Finset.univ (compactSpectrumWeight (4*m))
    (compactSpectrumEigenvalue (4*m)) t ≤ (compactReciprocalSum (4*m+4))^2 +
      ‖u‖^2 / t
  nlinarith only [hD, hhead, htdiv,
    sq_nonneg ‖twoThreeDual - (stageHeadSpace (4*m+3) (4*m+4)).starProjection twoThreeDual‖]

private theorem fourfold_cutoff_tendsto :
    Tendsto (fun m : ℕ => 4*m+4) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop n] with m hm
  omega

/-- Unconditional actual source escape is negligible at every fixed positive
multiple of the conductor scale, along an explicit cofinal sequence. -/
theorem compactSpectrum_fourfold_sourceDeficit_conductor_tendsto_zero
    (c : ℝ) (hc : 0 < c) :
    Tendsto (fun m : ℕ => sourceDeficit Finset.univ
      (compactSpectrumWeight (4*m)) (compactSpectrumEigenvalue (4*m))
      (c * (4*m+4 : ℕ))) atTop (𝓝 0) := by
  have hcharge : Tendsto (fun m : ℕ => (compactReciprocalSum (4*m+4))^2)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_pow (by norm_num : 2 ≠ 0)] using
      (compactReciprocalSum_tendsto_zero.comp fourfold_cutoff_tendsto).pow 2
  have henergy : Tendsto (fun m : ℕ =>
      ‖compactCorrectedHilbert (4*m+4) (by omega)‖^2 / (c * (4*m+4 : ℕ)))
      atTop (𝓝 0) := by
    have h := compactCorrectedHilbert_fourfold_sublinear.div_const c
    simpa only [div_div, mul_comm, zero_div] using h
  have hlim : Tendsto (fun m : ℕ => (compactReciprocalSum (4*m+4))^2 +
      ‖compactCorrectedHilbert (4*m+4) (by omega)‖^2 / (c * (4*m+4 : ℕ)))
      atTop (𝓝 0) := by simpa only [zero_add] using hcharge.add henergy
  apply squeeze_zero (fun m => sourceDeficit_nonneg Finset.univ
    (compactSpectrumWeight (4*m)) (compactSpectrumEigenvalue (4*m))
    (c * (4*m+4 : ℕ))
    (fun i _ => compactSpectrumWeight_nonneg (4*m) i)
    (fun i _ => compactSpectrumEigenvalue_nonneg (4*m) i) (by positivity))
    (fun m => compactSpectrum_fourfold_sourceDeficit_le_trial m
      (c * (4*m+4 : ℕ)) (by positivity)) hlim

/-- All actual source weights above the moving conductor threshold vanish.
No fixed-threshold tightness or RH conclusion is claimed. -/
theorem compactSpectrum_fourfold_highMass_conductor_tendsto_zero
    (c : ℝ) (hc : 0 < c) :
    Tendsto (fun m : ℕ => highMass Finset.univ
      (compactSpectrumWeight (4*m)) (compactSpectrumEigenvalue (4*m))
      (c * (4*m+4 : ℕ))) atTop (𝓝 0) := by
  have hlim : Tendsto (fun m : ℕ => 2 * sourceDeficit Finset.univ
      (compactSpectrumWeight (4*m)) (compactSpectrumEigenvalue (4*m))
      (c * (4*m+4 : ℕ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (compactSpectrum_fourfold_sourceDeficit_conductor_tendsto_zero c hc).const_mul 2
  apply squeeze_zero _ _ hlim
  · intro m
    unfold highMass
    apply Finset.sum_nonneg
    intro i hi
    split_ifs
    · exact compactSpectrumWeight_nonneg (4*m) i
    · norm_num
  · intro m
    exact highMass_le_two_mul_sourceDeficit Finset.univ
      (compactSpectrumWeight (4*m)) (compactSpectrumEigenvalue (4*m))
      (c * (4*m+4 : ℕ))
      (fun i _ => compactSpectrumWeight_nonneg (4*m) i)
      (fun i _ => compactSpectrumEigenvalue_nonneg (4*m) i) (by positivity)

end RiemannResearch.RH.Pareto.CoefficientStabilization
