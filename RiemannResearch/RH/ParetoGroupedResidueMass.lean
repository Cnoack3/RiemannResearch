import RiemannResearch.RH.ParetoRawTrial
import RiemannResearch.RH.ParetoGroupedResidueMassData
import RiemannResearch.RH.MixedConductorRankOne
import Mathlib.Tactic

/-! # Conductor-241 complete Pareto residual and normalized screened direction

The grouped raw-residue trial uses 147 nonzero integer coefficients, 65536
positive sites and a periodic tail envelope conditioned on their common residue modulo 30. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.GroupedResidueMass.Conductor241
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer

/-- Refining the tail alone cannot remove the positive loss on the certified
head for these specific coefficients. -/
theorem fixed_trial_head_loss_ge :
    (8592900483 : ℝ)/10^12 ≤ ∑ k ∈ Finset.range 65536,
      positiveWeight (k+1) * ((difference (k+1) : ℝ)/1000000)^2 := by
  have h := ParetoRawTrial.rounded_head_loss_lower rows 512
  have hU : (∑ j ∈ Finset.range 512, ParetoRawTrial.block rows j) = 8592966019 :=
    head_units_total
  have hlen : (512 * 128 : ℕ) = 65536 := by decide
  rw [hU, hlen] at h
  have hfloor : ((8592966019 : ℕ) : ℝ) - ((65536 : ℕ) : ℝ) = 8592900483 := by norm_num
  rw [hfloor] at h
  simpa only [difference, ParetoRawTrial.difference] using h

/-- The canonical mass dominates this complete physical trial at every larger cutoff. -/
theorem packetError_le_conductor_241_mod30 (n : ℕ) (hn : 240 ≤ n) :
    1-packetMass n ≤ (628101568132839 : ℝ)/65537000000000000 := by
  have h := ParetoRawTrial.packet_error_le_of_certificate 240 n hn rows 512 8592966019 8058806
    rows_range scaled_abs_bound_mod30 head_units_total.le
  convert h using 1
  norm_num

/-- The centered covariance signal-to-noise ratio at every larger cutoff. -/
theorem centered_mass_ratio_ge_conductor_241_mod30 (n : ℕ) (hn : 240 ≤ n) :
    (64908898431867161 : ℝ)/628101568132839 ≤ packetMass n / (1-packetMass n) := by
  apply (div_le_div_iff₀ (by norm_num) (sub_pos.mpr (packetMass_bounds n).2)).mpr
  linarith [packetError_le_conductor_241_mod30 n hn]

theorem limitEnergy_le_conductor_241_mod30 :
    limitEnergy ≤ (628101568132839 : ℝ)/65537000000000000 := by
  have h : (1:ℝ)-628101568132839/65537000000000000 ≤ 1-limitEnergy :=
    ge_of_tendsto packetMass_tendsto (eventually_atTop.2 ⟨240,fun n hn => by
      linarith [packetError_le_conductor_241_mod30 n hn]⟩)
  linarith

/-- The certified distance of the normalized mixed-screened seed from the constant, squared. -/
theorem screenedTwo_squared_distance_le_mod30 :
    ‖hilbertOne - PrimePowerSchur.normalizedScreenedTwo‖^2 ≤
        (628101568132839 : ℝ)/64908898431867161 := by
  rw [norm_sub_rev, PrimePowerSchur.normalizedScreenedTwo_error_sq_eq_limitEnergy]
  apply (div_le_div_iff₀ (by linarith [limitEnergy_le_conductor_241_mod30] : 0 < 1 - limitEnergy)
    (by norm_num : (0:ℝ) < 64908898431867161)).mpr
  linarith [limitEnergy_le_conductor_241_mod30]

/-- Complete-error bound from the original unconditioned envelope. -/
theorem packetError_le_conductor_241 (n : ℕ) (hn : 240 ≤ n) :
    1-packetMass n ≤ (643505167532007 : ℝ)/65537000000000000 :=
  (packetError_le_conductor_241_mod30 n hn).trans (by norm_num)

/-- Centered ratio from the original unconditioned envelope. -/
theorem centered_mass_ratio_ge_conductor_241 (n : ℕ) (hn : 240 ≤ n) :
    (64893494832467993 : ℝ)/643505167532007 ≤ packetMass n / (1-packetMass n) :=
  le_trans (by norm_num) (centered_mass_ratio_ge_conductor_241_mod30 n hn)

theorem limitEnergy_le_conductor_241 :
    limitEnergy ≤ (643505167532007 : ℝ)/65537000000000000 :=
  limitEnergy_le_conductor_241_mod30.trans (by norm_num)

theorem screenedTwo_squared_distance_le :
    ‖hilbertOne - PrimePowerSchur.normalizedScreenedTwo‖^2 ≤
        (643505167532007 : ℝ)/64893494832467993 :=
  screenedTwo_squared_distance_le_mod30.trans (by norm_num)

theorem screenedTwo_squared_distance_lt_one_percent :
    ‖hilbertOne - PrimePowerSchur.normalizedScreenedTwo‖^2 < (1:ℝ)/100 :=
  lt_of_le_of_lt screenedTwo_squared_distance_le_mod30 (by norm_num)

/--
info: 'RiemannResearch.RH.GroupedResidueMass.Conductor241.screenedTwo_squared_distance_lt_one_percent' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms screenedTwo_squared_distance_lt_one_percent

end RiemannResearch.RH.GroupedResidueMass.Conductor241
