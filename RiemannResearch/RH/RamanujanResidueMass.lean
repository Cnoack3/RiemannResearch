import RiemannResearch.RH.ParetoRawTrial
import RiemannResearch.RH.RamanujanResidueMassData
import RiemannResearch.RH.ParetoHiddenNoiseMoments
import Mathlib.Tactic

/-!
# A complete physical upper bound on the Pareto residual

An integer combination of raw residues through conductor 124 is tested on
the first 32768 positive sites. A uniform range estimate and the exact
Pareto tail probability enclose all remaining terms.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.RamanujanResidueMass
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer Certificate

private def lo (s : List (ℕ × ℤ)) : ℤ :=
  (s.map fun t => min 0 (t.2 * ((t.1-1 : ℕ) : ℤ))).sum

private def hi (s : List (ℕ × ℤ)) : ℤ :=
  (s.map fun t => max 0 (t.2 * ((t.1-1 : ℕ) : ℤ))).sum

private theorem signal_bounds (s : List (ℕ × ℤ))
    (hs : ∀ t ∈ s, 2 ≤ t.1) (k : ℕ) : lo s ≤ signal s k ∧ signal s k ≤ hi s := by
  induction s with
  | nil => simp [lo, hi, signal]
  | cons t s ih =>
    obtain ⟨d,z⟩ := t
    have hd : 2 ≤ d := hs (d,z) (by simp)
    have hh := ih (fun t ht => hs t (by simp [ht]))
    have hmod : (0 : ℤ) ≤ ((k%d : ℕ) : ℤ) := by positivity
    have hmax : ((k%d : ℕ) : ℤ) ≤ ((d-1 : ℕ) : ℤ) := by
      exact_mod_cast (show k%d ≤ d-1 by have := Nat.mod_lt k (by omega : 0<d); omega)
    have h0 : (0 : ℤ) ≤ ((d-1 : ℕ) : ℤ) := by positivity
    have hrow : min 0 (z*((d-1 : ℕ) : ℤ)) ≤ z*((k%d : ℕ) : ℤ) ∧
        z*((k%d : ℕ) : ℤ) ≤ max 0 (z*((d-1 : ℕ) : ℤ)) := by
      rcases le_total 0 z with hz | hz
      · exact ⟨(min_le_left _ _).trans (mul_nonneg hz hmod),
          (mul_le_mul_of_nonneg_left hmax hz).trans (le_max_right _ _)⟩
      · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hmax hz),
          (mul_nonpos_of_nonpos_of_nonneg hz hmod).trans (le_max_left _ _)⟩
    exact ⟨add_le_add hrow.1 hh.1, add_le_add hrow.2 hh.2⟩

private theorem rows_range : ∀ t ∈ rows, 2 ≤ t.1 ∧ t.1 ≤ 124 := by decide

private theorem scaled_abs_bound (k : ℕ) : |difference k| ≤ 7063991 := by
  have h := signal_bounds rows (fun t ht => (rows_range t ht).1) k
  have hlo : lo rows = -6063991 := by decide
  have hhi : hi rows = 8063935 := by decide
  rw [hlo,hhi] at h
  unfold difference
  rw [abs_le]
  omega

/-- The canonical mass dominates this complete physical trial at every larger cutoff. -/
theorem packetError_le_conductor_124 (n : ℕ) (hn : 123 ≤ n) :
    1-packetMass n ≤ (36740218801559 : ℝ)/2979000000000000 := by
  have h := ParetoRawTrial.packet_error_le_of_certificate 123 n hn rows 256 10810291372 7063991
    rows_range scaled_abs_bound head_units_total.le
  convert h using 1 <;> norm_num

/-- The centered covariance signal-to-noise ratio at every larger cutoff. -/
theorem centered_mass_ratio_ge_conductor_124 (n : ℕ) (hn : 123 ≤ n) :
    (2942259781198441 : ℝ)/36740218801559 ≤ packetMass n / (1-packetMass n) := by
  apply (div_le_div_iff₀ (by norm_num) (sub_pos.mpr (packetMass_bounds n).2)).mpr
  linarith [packetError_le_conductor_124 n hn]

theorem limitEnergy_le_conductor_124 :
    limitEnergy ≤ (36740218801559 : ℝ)/2979000000000000 := by
  have h : (1:ℝ)-36740218801559/2979000000000000 ≤ 1-limitEnergy :=
    ge_of_tendsto packetMass_tendsto (eventually_atTop.2 ⟨123,fun n hn => by
      linarith [packetError_le_conductor_124 n hn]⟩)
  linarith

end RiemannResearch.RH.RamanujanResidueMass

/--
info: 'RiemannResearch.RH.RamanujanResidueMass.limitEnergy_le_conductor_124' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.RH.RamanujanResidueMass.limitEnergy_le_conductor_124
