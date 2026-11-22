import RiemannResearch.Analysis.ProjectionTrialEnergy
import RiemannResearch.RH.ParetoGroupedResidueMass
import RiemannResearch.RH.MixedConductorCaptureGains
import RiemannResearch.RH.MixedMobiusWindow
import RiemannResearch.RH.CenteredMeanSnake
import Mathlib.Tactic.Linarith

/-!
# Finite trials for the centered parity packet

The finite approximants in the Pareto–von Mangoldt continuation can be
tested with the complete Pareto error. We use the mixed windows and variance
from `MixedConductorCaptureGains` and the boundary identity in `MixedMobiusWindow`.
-/

noncomputable section
open Filter
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CaptureGains
open CoefficientStabilization

/-- The squared error of any finite mixed fit retains exactly the squared
distance from the optimal coefficient fit in that same window. -/
theorem centeredParity_trial_error_sq (N : ℕ) (m : ThresholdHilbert)
    (hm : m ∈ mixedSpace (Finset.Icc 2 N)) :
    ‖centeredParity - m‖ ^ 2 =
      Real.log 2 - (Real.log 2) ^ 2 -
        ‖(mixedSpace (Finset.Icc 2 N)).starProjection (ramanujanPacketHilbert 2)‖ ^ 2 +
        ‖(mixedSpace (Finset.Icc 2 N)).starProjection (ramanujanPacketHilbert 2) - m‖ ^ 2 := by
  have h := RiemannResearch.Analysis.projection_trial_energy
    (mixedSpace (Finset.Icc 2 N)) centeredParity m hm
  change ‖centeredParity - m‖ ^ 2 = deficit N +
    ‖(mixedSpace (Finset.Icc 2 N)).starProjection centeredParity - m‖ ^ 2 at h
  rw [project_centeredParity] at h
  linarith only [h, deficit_add_capture N]

/-- Membership of the ambient constant in the legal space is equivalent to
arbitrarily accurate finite mixed fits to centered parity in the full norm. -/
theorem one_mem_iff_centeredParity_finite_trials :
    hilbertOne ∈ closedSpace ↔ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∃ m ∈ mixedSpace (Finset.Icc 2 N), ‖centeredParity - m‖ ^ 2 < ε := by
  rw [← CenteredMeanSnake.boundary_eq_zero_iff_one_mem,
    ← MixedMobiusTesting.centeredParity_mem_iff_boundary]
  let stage (N : ℕ) := mixedSpace (Finset.Icc 2 N)
  have hmono : Monotone stage := fun _ _ h =>
    mixedSpace_mono (Finset.Icc_subset_Icc le_rfl h)
  change centeredParity ∈ closure ((⨆ N, stage N : Submodule ℝ ThresholdHilbert) :
    Set ThresholdHilbert) ↔ _
  rw [Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨m, hm, hd⟩ := h (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
    obtain ⟨N, hN⟩ := (Submodule.mem_iSup_of_directed stage hmono.directed_le).mp hm
    refine ⟨N, m, hN, ?_⟩
    rw [dist_eq_norm] at hd
    simpa only [Real.sq_sqrt hε.le] using
      (sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg ε)).mpr hd
  · intro h ε hε
    obtain ⟨N, m, hm, hd⟩ := h (ε ^ 2) (sq_pos_of_pos hε)
    refine ⟨m, (le_iSup stage N) hm, ?_⟩
    rw [dist_eq_norm]
    exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hd

/-- On this route the only remaining premise is the displayed complete-error
arithmetic estimate with finite mixed packets. -/
theorem riemannHypothesis_of_centeredParity_finite_trials
    (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ m ∈ mixedSpace (Finset.Icc 2 N),
      ‖centeredParity - m‖ ^ 2 < ε) : RiemannHypothesis :=
  riemannHypothesis_of_normalizedScreenedTwo
    (one_mem_closedSpace_iff_normalizedScreenedTwo.mp
      (one_mem_iff_centeredParity_finite_trials.mpr h))

/-- The independent conductor-241 certificate gives a mixed fit throughout
every sufficiently large window for each tolerance above its complete-error
bound. The cutoff can depend on the tolerance. -/
theorem eventually_centeredParity_finite_trials_of_conductor241 (ε : ℝ)
    (hε : (628101568132839 : ℝ) / 64908898431867161 * (Real.log 2) ^ 2 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, ∃ m ∈ mixedSpace (Finset.Icc 2 N),
      ‖centeredParity - m‖ ^ 2 < ε := by
  have hbound : ‖hilbertOne - normalizedScreenedTwo‖ ^ 2 * (Real.log 2) ^ 2 < ε :=
    (mul_le_mul_of_nonneg_right
      RiemannResearch.RH.GroupedResidueMass.Conductor241.screenedTwo_squared_distance_le_mod30
      (sq_nonneg _)).trans_lt hε
  have ht := (((tendsto_const_nhds (x := hilbertOne)).sub
    fixedTwoTrial_tendsto).norm.pow 2).mul_const ((Real.log 2) ^ 2)
  filter_upwards [ht.eventually_lt_const hbound] with N hN
  let p := (mixedSpace (Finset.Icc 2 N)).starProjection (ramanujanPacketHilbert 2)
  have hp : p ∈ mixedSpace (Finset.Icc 2 N) :=
    (mixedSpace (Finset.Icc 2 N)).starProjection_apply_mem _
  refine ⟨p, hp, ?_⟩
  have hL : (Real.log 2) ^ 2 ≠ 0 := pow_ne_zero 2 (Real.log_pos (by norm_num)).ne'
  have he := (eq_div_iff hL).mp (fixedTwoTrial_error_eq_capture N)
  rw [centeredParity_trial_error_sq N p hp]
  change Real.log 2 - (Real.log 2) ^ 2 - ‖p‖ ^ 2 + ‖p - p‖ ^ 2 < ε
  have hvalue : ‖hilbertOne - fixedTwoTrial N‖ ^ 2 * (Real.log 2) ^ 2 =
      Real.log 2 - (Real.log 2) ^ 2 - ‖p‖ ^ 2 := he
  rw [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero, ← hvalue]
  exact hN

end RiemannResearch.RH.Pareto.PrimePowerSchur.CaptureGains
