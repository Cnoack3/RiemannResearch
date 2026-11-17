import RiemannResearch.RH.ExactHeadAtomMoment
import RiemannResearch.RH.ParetoRationalWeightIntervals
import Mathlib.Tactic

/-!
# Kernel certificate for the complete cutoff-five centered moment probe

Source: the user's exact-head handoff and its externally proposed rational
correction, rounded here to six decimal places. Acceptance recomputes all
29 residues with proved complete progression intervals. No external numerical
claim or inverse-matrix accuracy is a premise.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadAtomStageFiveMoment
open RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.RH.ExactHeadGreenProfile
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.RH.MobiusAffineProfile
open RiemannResearch.NumberTheory.DivisorIncidence
open ExactHeadAtomOptimizer

theorem probe_formula (r : ℕ) :
    fittedMomentProbe 5 r =
      (111 * (r : ℝ) - 7 * (r / 2 : ℕ) - 125 * (r / 3 : ℕ) -
        361 * (r / 5 : ℕ)) / 191 := by
  have h1 : ArithmeticFunction.moebius 1 = 1 := ArithmeticFunction.moebius_apply_one
  have h2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have h3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_three
  have h4 : ArithmeticFunction.moebius 4 = 0 := by decide
  have h5 : ArithmeticFunction.moebius 5 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  norm_num [fittedMomentProbe, affineMomentDual, mass, energy, weight,
    sum_Icc_one, Finset.sum_range_succ, h1, h2, h3, h4, h5, grid]
  ring

def probeCorrection (r : ℕ) : ℝ :=
  (349246 / 1000000) * atom 30 6 r -
    (1152475 / 1000000) * atom 30 10 r -
      (1432725 / 1000000) * atom 30 15 r

theorem probeCorrection_mem : probeCorrection ∈ upperSpan 30 5 (atom 30) := by
  have h6 : atom 30 6 ∈ upperSpan 30 5 (atom 30) :=
    Submodule.subset_span ⟨6, by decide, rfl⟩
  have h10 : atom 30 10 ∈ upperSpan 30 5 (atom 30) :=
    Submodule.subset_span ⟨10, by decide, rfl⟩
  have h15 : atom 30 15 ∈ upperSpan 30 5 (atom 30) :=
    Submodule.subset_span ⟨15, by decide, rfl⟩
  exact (upperSpan 30 5 (atom 30)).sub_mem
    ((upperSpan 30 5 (atom 30)).sub_mem
      ((upperSpan 30 5 (atom 30)).smul_mem (349246 / 1000000 : ℝ) h6)
      ((upperSpan 30 5 (atom 30)).smul_mem (1152475 / 1000000 : ℝ) h10))
    ((upperSpan 30 5 (atom 30)).smul_mem (1432725 / 1000000 : ℝ) h15)

def centeredProbe (r : ℕ) : ℝ :=
  fittedMomentProbe 5 r - (1 / 2) * target 30 r - probeCorrection r

private def count (P d r : ℕ) : ℕ :=
  ((Finset.Icc 1 r).filter (fun n => Nat.gcd n P = d)).card

private theorem atom_eq_count (P d r : ℕ) : atom P d r = (count P d r : ℝ) := by
  simp [atom, count]

private def numerator (r : ℕ) : ℤ :=
  2000000 * (111 * (r : ℤ) - 7 * (r / 2 : ℕ) - 125 * (r / 3 : ℕ) -
    361 * (r / 5 : ℕ)) - 191000000 * ((count 30 1 r : ℤ) - 1) -
      382 * (349246 * (count 30 6 r : ℤ) - 1152475 * (count 30 10 r : ℤ) -
        1432725 * (count 30 15 r : ℤ))

private def numData : ℕ → ℤ
  | 0 => 191000000
  | 1 => 222000000
  | 2 => 430000000
  | 3 => 402000000
  | 4 => 610000000
  | 5 => 110000000
  | 6 => -65411972
  | 7 => -34411972
  | 8 => 173588028
  | 9 => 145588028
  | 10 => 71833478
  | 11 => 102833478
  | 12 => -72578494
  | 13 => -41578494
  | 14 => 166421506
  | 15 => -36277544
  | 16 => 171722456
  | 17 => 202722456
  | 18 => 27310484
  | 19 => 58310484
  | 20 => -15444066
  | 21 => -43444066
  | 22 => 164555934
  | 23 => 195555934
  | 24 => 20143962
  | 25 => -479856038
  | 26 => -271856038
  | 27 => -299856038
  | 28 => -91856038
  | 29 => -60856038
  | _ => 0

private theorem data_check : ∀ r : Fin 30, numerator r.val = numData r.val := by decide

private theorem residual_data (r : ℕ) (hr : r < 30) :
    centeredProbe r = (numData r : ℝ) / 382000000 := by
  have hn := data_check ⟨r, hr⟩
  change numerator r = numData r at hn
  rw [← hn]
  simp only [centeredProbe, probe_formula, probeCorrection, target,
    atom_eq_count, numerator]
  generalize r / 2 = r2
  generalize r / 3 = r3
  generalize r / 5 = r5
  push_cast
  ring

private def data (r : ℕ) : ℚ := (numData r : ℚ) / 382000000

private def probeEnergyInterval : RatInterval :=
  RatInterval.sum (Finset.range 29) (fun j =>
    RatInterval.mul (elementaryProgressionInterval 30 (j + 1) 8)
      (RatInterval.point (data (j + 1) ^ 2)))

private theorem data_cast (r : ℕ) (hr : r < 30) :
    (data r : ℝ) = centeredProbe r := by
  rw [residual_data r hr]
  simp [data]

private theorem probeEnergyInterval_contains :
    probeEnergyInterval.Contains
      (energy (Finset.Icc 1 29) (progressionWeight 30) centeredProbe) := by
  unfold probeEnergyInterval energy
  rw [sum_Icc_one]
  apply RatInterval.contains_sum
  intro j hj
  have hr : j + 1 < 30 := by have hh := Finset.mem_range.mp hj; omega
  have hw := elementaryProgressionInterval_contains 30 (j + 1) 8 (by norm_num) (by omega)
  have hp := RatInterval.contains_point (data (j + 1) ^ 2)
  simpa only [Rat.cast_pow, data_cast (j + 1) hr] using RatInterval.contains_mul hw hp

set_option maxHeartbeats 10000000 in
-- Exact finite sums require rational arithmetic with large denominators.
set_option maxRecDepth 100000 in
private theorem endpoint_checks :
    ((6288 / 10000) : ℚ) ≤ probeEnergyInterval.lo ∧
      probeEnergyInterval.hi ≤ ((63 / 100) : ℚ) := by
  norm_num [probeEnergyInterval, elementaryProgressionInterval,
    RatInterval.sum, RatInterval.mul, RatInterval.point,
    data, numData, Finset.sum_range_succ]

/-- A complete kernel-checked energy enclosure for an explicit legal correction. -/
theorem centered_probe_energy_interval :
    ((6288 / 10000) : ℝ) ≤
        energy (Finset.Icc 1 29) (progressionWeight 30) centeredProbe ∧
      energy (Finset.Icc 1 29) (progressionWeight 30) centeredProbe ≤ ((63 / 100) : ℝ) := by
  obtain ⟨hl, hu⟩ := endpoint_checks
  have he := probeEnergyInterval_contains
  constructor
  · exact (show ((6288 / 10000) : ℝ) ≤ (probeEnergyInterval.lo : ℝ) by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using ((Rat.cast_le (K := ℝ)).2 hl)).trans he.1
  · exact he.2.trans (by simpa only [Rat.cast_div, Rat.cast_ofNat] using
      ((Rat.cast_le (K := ℝ)).2 hu))

/-- This is an actual fitted-moment bound, not a trial-optimizer statement. -/
theorem fitted_moment_five_deficit :
    atomFittedMoment 30 5 ≤ (3 / 4) * atomEnergy 30 5 + 63 / 100 := by
  have h := fitted_moment_deficit_of_probe_bound 30 5 (1 / 2) (63 / 100) (1 / 4)
    (by norm_num) (by norm_num) probeCorrection probeCorrection_mem
    centered_probe_energy_interval.2
  norm_num at h ⊢
  exact h

end RiemannResearch.RH.Pareto.ExactHeadAtomStageFiveMoment
