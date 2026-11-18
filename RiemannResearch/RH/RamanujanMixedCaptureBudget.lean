import RiemannResearch.RH.RamanujanOrdinateNormalEquations
import RiemannResearch.RH.RamanujanSixMass
import RiemannResearch.RH.RamanujanResidueMass
import RiemannResearch.RH.MixedConductorRankOne
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# From certified Pareto mass to mixed-conductor capture

The full mixed projection of the fixed packet at two controls the RH endpoint.
Each finite lower bound on the captured mass of the constant gives an upper
bound on the missing mixed energy. The fully screened rank-one identity is
essential to this transfer.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization RamanujanCanonicalOptimizer RamanujanSixMass
open RiemannResearch.RH.RamanujanOrdinateNormalEquations

/-- Captured squared norm of the fixed packet at two under full mixed screening. -/
def fullTwoCapture : ℝ := ‖mixedClosure.starProjection (ramanujanPacketHilbert 2)‖^2

private theorem mixed_capture_tendsto :
    Tendsto (fun B : ℕ =>
      ‖(mixedSpace (Finset.Icc 2 B)).starProjection (ramanujanPacketHilbert 2)‖^2)
      atTop (𝓝 fullTwoCapture) := by
  have hmono : Monotone (fun B : ℕ => mixedSpace (Finset.Icc 2 B)) :=
    fun _ _ h => mixedSpace_mono (Finset.Icc_subset_Icc le_rfl h)
  exact (Submodule.starProjection_tendsto_closure_iSup
    (fun B : ℕ => mixedSpace (Finset.Icc 2 B)) hmono (ramanujanPacketHilbert 2)).norm.pow 2

/-- The entire missing mixed energy is the canonical residual odds multiplied
by the squared mark of the seed. -/
theorem fullTwoCapture_deficit :
    Real.log 2 - (Real.log 2)^2 - fullTwoCapture =
      (Real.log 2)^2 * (limitEnergy / (1-limitEnergy)) := by
  let l := Real.log 2
  have htrial : Tendsto (fun B : ℕ => ‖hilbertOne - fixedTwoTrial B‖^2)
      atTop (𝓝 (‖hilbertOne - normalizedScreenedTwo‖^2)) :=
    (tendsto_const_nhds.sub fixedTwoTrial_tendsto).norm.pow 2
  have hcap : Tendsto (fun B : ℕ =>
      (l-l^2 - ‖(mixedSpace (Finset.Icc 2 B)).starProjection (ramanujanPacketHilbert 2)‖^2)/l^2)
      atTop (𝓝 ((l-l^2-fullTwoCapture)/l^2)) :=
    (tendsto_const_nhds.sub mixed_capture_tendsto).div_const _
  have he := tendsto_nhds_unique htrial (hcap.congr
    (fun B => (fixedTwoTrial_error_eq_capture B).symm))
  rw [norm_sub_rev, normalizedScreenedTwo_error_sq_eq_limitEnergy] at he
  have hl : l ≠ 0 := (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'
  exact ((eq_div_iff (pow_ne_zero 2 hl)).mp he).symm.trans (mul_comm _ _)

/-- Any finite complete normal-equation mass gives a bound on the infinite
mixed projection. The two stage indices need not coincide. -/
theorem fullTwoCapture_deficit_le_of_mass {n : ℕ} (hn : 0 < packetMass n) :
    Real.log 2 - (Real.log 2)^2 - fullTwoCapture ≤
      (Real.log 2)^2 * ((1-packetMass n)/packetMass n) := by
  have hle : packetMass n ≤ 1-limitEnergy :=
    ge_of_tendsto packetMass_tendsto
      ((eventually_ge_atTop n).mono fun _ h => packetMass_monotone h)
  rw [fullTwoCapture_deficit]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply (div_le_div_iff₀ (hn.trans_le hle) hn).mpr
  nlinarith

/-- An upper bound on the terminal Pareto loss gives a lower bound on the
mixed capture itself. -/
theorem fullTwoCapture_lower_of_budget {b : ℝ} (hb : limitEnergy ≤ b) (hb1 : b < 1) :
    Real.log 2 - (Real.log 2)^2 * (1/(1-b)) ≤ fullTwoCapture := by
  have hp : 0 < 1-limitEnergy := by linarith
  have hp' := sub_pos.mpr hb1
  have he : limitEnergy / (1-limitEnergy) ≤ b/(1-b) := by
    apply (div_le_div_iff₀ hp hp').mpr
    nlinarith
  have hd := mul_le_mul_of_nonneg_left he (sq_nonneg (Real.log 2))
  rw [← fullTwoCapture_deficit] at hd
  have hcoef : 1/(1-b) = 1 + b/(1-b) := by
    field_simp [hp'.ne']
    <;> ring
  rw [hcoef]
  nlinarith

theorem fullTwoCapture_six_lower :
    Real.log 2 - (Real.log 2)^2 * ((10^15 : ℝ)/963791965363034) ≤ fullTwoCapture := by
  convert fullTwoCapture_lower_of_budget limitEnergy_le_six (by norm_num) using 1 <;> norm_num

/-- The larger dictionary forces a strictly stronger bound on full mixed capture. -/
theorem fullTwoCapture_124_lower :
    Real.log 2 - (Real.log 2)^2 * (2979000000000000/2942259781198441 : ℝ) ≤ fullTwoCapture := by
  convert fullTwoCapture_lower_of_budget RamanujanResidueMass.limitEnergy_le_conductor_124
    (by norm_num) using 1 <;> norm_num

/-- A rational lower bound on the fraction of the RH capture target. -/
theorem fullTwoCapture_fraction :
    (971793053/1000000000 : ℝ) * (Real.log 2 - (Real.log 2)^2) ≤ fullTwoCapture := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcoef : 0 ≤ (1-971793053/1000000000 : ℝ) - Real.log 2 *
      (2979000000000000/2942259781198441 - 971793053/1000000000) := by
    linarith [Real.log_two_lt_d9]
  nlinarith [mul_nonneg hl.le hcoef, fullTwoCapture_124_lower]

/-- Finite mixed spans eventually capture strictly more than 97.17 percent
of the RH target. The mixed cutoff here is existential. -/
theorem eventually_mixed_capture_above_9717 :
    ∀ᶠ B : ℕ in atTop,
      (9717/10000 : ℝ) * (Real.log 2 - (Real.log 2)^2) <
        ‖(mixedSpace (Finset.Icc 2 B)).starProjection (ramanujanPacketHilbert 2)‖^2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htarget : 0 < Real.log 2 - (Real.log 2)^2 := by
    have hsmall : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    nlinarith [mul_pos hl (sub_pos.mpr hsmall)]
  apply mixed_capture_tendsto.eventually_const_lt
  exact (mul_lt_mul_of_pos_right (by norm_num : (9717/10000:ℝ) < 971793053/1000000000)
    htarget).trans_le fullTwoCapture_fraction

/-- A mass reached at arbitrarily large heights at a single fixed stage
bounds the full mixed projection from below. -/
theorem fullTwoCapture_lower_of_frequent_ordinate_mass {p n : ℕ} (hp : p.Prime)
    {b : ℝ} (hb : 0 < b)
    (h : ∃ᶠ T : ℝ in atTop, b ≤ capturedMass n (rawRow p T)) :
    Real.log 2 - (Real.log 2)^2 * (1/b) ≤ fullTwoCapture := by
  have hn : b ≤ packetMass n := by
    by_contra! hlt
    exact h (((raw_mass_tendsto hp n).eventually_lt_const hlt).mono
      (fun _ h' => not_le_of_gt h'))
  have hu : packetMass n ≤ 1-limitEnergy :=
    ge_of_tendsto packetMass_tendsto
      ((eventually_ge_atTop n).mono fun _ hk => packetMass_monotone hk)
  have he : limitEnergy ≤ 1-b := by linarith
  have H := fullTwoCapture_lower_of_budget he (by linarith : 1-b < 1)
  rwa [show 1-(1-b)=b by ring] at H

/-- At a fixed stage containing conductors through 124, the actual zero
ordinates eventually certify this rational threshold without rounding. -/
theorem eventually_ordinate_mass_above_9876669289 {p : ℕ} (hp : p.Prime)
    (n : ℕ) (hn : 123 ≤ n) :
    ∀ᶠ T : ℝ in atTop, (9876669289/10000000000 : ℝ) < capturedMass n (rawRow p T) := by
  apply (raw_mass_tendsto hp n).eventually_const_lt
  linarith [RamanujanResidueMass.packetError_le_conductor_124 n hn]

end RiemannResearch.RH.Pareto.PrimePowerSchur

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.eventually_mixed_capture_above_9717' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.RH.Pareto.PrimePowerSchur.eventually_mixed_capture_above_9717
