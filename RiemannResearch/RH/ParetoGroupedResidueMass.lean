import RiemannResearch.RH.ParetoRawTrial
import RiemannResearch.RH.ParetoGroupedResidueMassData
import RiemannResearch.RH.MixedConductorRankOne
import Mathlib.Tactic

/-! # Conductor-241 complete Pareto residual and normalized screened direction

The grouped raw-residue trial uses 147 nonzero integer coefficients, 65536
positive sites and a rigorously periodic tail envelope. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.GroupedResidueMass.Conductor241
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer

/-- The canonical mass dominates this complete physical trial at every larger cutoff. -/
theorem packetError_le_conductor_241 (n : ℕ) (hn : 240 ≤ n) :
    1-packetMass n ≤ (643505167532007 : ℝ)/65537000000000000 := by
  have h := ParetoRawTrial.packet_error_le_of_certificate 240 n hn rows 512 8592966019 8963702
    rows_range scaled_abs_bound head_units_total.le
  convert h using 1 <;> norm_num

/-- The centered covariance signal-to-noise ratio at every larger cutoff. -/
theorem centered_mass_ratio_ge_conductor_241 (n : ℕ) (hn : 240 ≤ n) :
    (64893494832467993 : ℝ)/643505167532007 ≤ packetMass n / (1-packetMass n) := by
  apply (div_le_div_iff₀ (by norm_num) (sub_pos.mpr (packetMass_bounds n).2)).mpr
  linarith [packetError_le_conductor_241 n hn]

theorem limitEnergy_le_conductor_241 :
    limitEnergy ≤ (643505167532007 : ℝ)/65537000000000000 := by
  have h : (1:ℝ)-643505167532007/65537000000000000 ≤ 1-limitEnergy :=
    ge_of_tendsto packetMass_tendsto (eventually_atTop.2 ⟨240,fun n hn => by
      linarith [packetError_le_conductor_241 n hn]⟩)
  linarith

/-- The certified distance of the normalized mixed-screened seed from the constant, squared. -/
theorem screenedTwo_squared_distance_le :
    ‖hilbertOne - PrimePowerSchur.normalizedScreenedTwo‖^2 ≤
        (643505167532007 : ℝ)/64893494832467993 := by
  rw [norm_sub_rev, PrimePowerSchur.normalizedScreenedTwo_error_sq_eq_limitEnergy]
  apply (div_le_div_iff₀ (by linarith [limitEnergy_le_conductor_241] : 0 < 1 - limitEnergy)
    (by norm_num : (0:ℝ) < 64893494832467993)).mpr
  linarith [limitEnergy_le_conductor_241]

theorem screenedTwo_squared_distance_lt_one_percent :
    ‖hilbertOne - PrimePowerSchur.normalizedScreenedTwo‖^2 < (1:ℝ)/100 :=
  lt_of_le_of_lt screenedTwo_squared_distance_le (by norm_num)

/--
info: 'RiemannResearch.RH.GroupedResidueMass.Conductor241.screenedTwo_squared_distance_lt_one_percent' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms screenedTwo_squared_distance_lt_one_percent

end RiemannResearch.RH.GroupedResidueMass.Conductor241
