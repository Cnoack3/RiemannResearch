import RiemannResearch.RH.ParetoResidueMicroscopicSource
import RiemannResearch.RH.ParetoLCMAugmentedProbe
import RiemannResearch.RH.ParetoLCMZeroCertificate
import RiemannResearch.RH.ParetoBeurlingMellinObstruction
import RiemannResearch.RH.ParetoResidueAtomTests
import RiemannResearch.RH.MellinCriticalPoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Moving microscopic certificates on the full LCM tower

Source: Sections 10--13 of the user-provided Ramanujan DPP / LCM handoff,
9 November 2026. The microscopic row margin now supplies certificate decay.
The remaining complete augmented vacancy has the same limit as the full
legal projection error. A vanishing upper bound on it, or on complete
shifted legal trials, is still an open arithmetic input.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.ResidueMellin
open MellinFrequency (criticalPoint criticalPoint_ne_one)
open ParetoBeurlingMellinObstruction (normalizedResidueSpan)

variable (κ : ℕ → Type*) [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) (γ : ∀ j, κ j → ℝ)
    (hγ : ∀ j, Function.Injective (γ j)) (hpos : ∀ j i, 0 < γ j i)
    (hz : ∀ j i, riemannZeta (criticalPoint (γ j i)) = 0)
    (d : ℝ) (hd : 0 ≤ d) (hd' : d < 1 / 2)
    (hrow : ∀ᶠ j in atTop, ∀ i,
      microscopicRealRowBudget (γ j) (lcmResidueIndex (M j)) i ≤ d)

include hM hγ hpos hz hd hd' hrow

theorem lcm_moving_certificate_tendsto_of_microscopic :
    Tendsto (fun j => certificateEnergy (lcmResidueIndex (M j))
      (fun i => criticalPoint (γ j i))) atTop (𝓝 0) :=
  critical_certificate_tendsto_of_microscopic_actual_zeros κ
    (fun j => lcmResidueIndex (M j)) (lcmResidueIndex_tendsto.comp hM)
    γ hγ hpos hz d hd hd' hrow

/-- Moving admissible zero tests remove a vanishing amount from the full error. -/
theorem lcm_moving_remainder_tendsto_limit_of_microscopic :
    Tendsto (fun j => lcmRemainder (fun i => criticalPoint (γ j i)) (M j))
      atTop (𝓝 (‖hilbertOne -
        normalizedResidueSpan.topologicalClosure.starProjection hilbertOne‖ ^ 2)) := by
  have hc := lcm_moving_certificate_tendsto_of_microscopic κ M hM γ hγ hpos hz d hd hd' hrow
  have hm := multiples_mass_tendsto_zero.comp (lcmResidueIndex_tendsto.comp hM)
  have h := (lcmError_tendsto.comp hM).sub (hm.add hc)
  simp only [Function.comp_def, zero_add, sub_zero] at h
  refine h.congr (fun j => ?_)
  rw [lcmError, lcm_best_error_eq (M j) (fun i => criticalPoint (γ j i))
    (fun i => by simp) (fun i => criticalPoint_ne_one (γ j i)) (hz j)]
  ring

/-- Only the complete remainder upper bound remains as a vanishing input. -/
theorem riemannHypothesis_of_microscopic_remainder_upper
    (B : ℕ → ℝ) (hB : Tendsto B atTop (𝓝 0))
    (hub : ∀ᶠ j in atTop,
      lcmRemainder (fun i => criticalPoint (γ j i)) (M j) ≤ B j) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_augmented_vacancy κ M hM
    (fun j i => criticalPoint (γ j i))
    (fun j i => by simp) (fun j i => criticalPoint_ne_one (γ j i)) hz
  · exact lcm_moving_certificate_tendsto_of_microscopic κ M hM γ hγ hpos hz d hd hd' hrow
  · exact squeeze_zero' (Eventually.of_forall (fun j => sq_nonneg _)) hub hB

/-- A complete shifted legal trial can supply the remaining upper bound. -/
theorem riemannHypothesis_of_microscopic_shifted_trials
    (f : ℕ → ThresholdHilbert)
    (hf : ∀ j, f j ∈ trialSpace (Nat.lcmUpto (M j)))
    (B : ℕ → ℝ) (hB : Tendsto B atTop (𝓝 0))
    (hub : ∀ᶠ j in atTop, ‖errorVector (lcmResidueIndex (M j)) (f j) -
      certificateVector (lcmResidueIndex (M j)) (fun i => criticalPoint (γ j i))‖ ^ 2 ≤ B j) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_microscopic_remainder_upper κ M hM γ hγ hpos hz d hd hd' hrow B hB
  filter_upwards [hub] with j hj
  rw [lcm_shifted_trial_norm_sq (M j) (hf j) (fun i => criticalPoint (γ j i))
    (fun i => by simp) (fun i => criticalPoint_ne_one (γ j i)) (hz j)] at hj
  linarith [sq_nonneg ‖f j - lcmBest (M j)‖]

end RiemannResearch.RH.Pareto.ResidueMellin
