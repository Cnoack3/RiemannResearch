import RiemannResearch.RH.MobiusHeadGreenNormal
import RiemannResearch.RH.ExactHeadAtomStageFiveMoment
import RiemannResearch.RH.ExactHeadAtomCertification
import RiemannResearch.RH.ParetoRationalWeightIntervals
import RiemannResearch.LinearAlgebra.RationalLinearSolveCertificate
import Mathlib.Tactic

/-!
# Kernel certificate for the actual cutoff-five Green energy
Every nonterminal residue and every infinite progression tail is retained.
The rational trial coefficients are proposals only. The proved normal-defect
enclosure, followed by exact rational endpoint checks, certifies the optimizer.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadAtomStageFive
open RiemannResearch
open RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.NumberTheory.DivisorIncidence
open ExactHeadAtomOptimizer

private def count (P d r : ℕ) : ℕ :=
  ((Finset.Icc 1 r).filter (fun n => Nat.gcd n P = d)).card

private theorem atom_eq_count (P d r : ℕ) : atom P d r = (count P d r : ℝ) := by
  simp [atom,count]

def trialCoeff (d : ℕ) : ℝ :=
  if d = 6 then 743144 / 1000000 else
  if d = 10 then 974745 / 1000000 else
  if d = 15 then 1068929 / 1000000 else 0

private def numerator (r : ℕ) : ℤ :=
  1000000 * (count 30 1 r : ℤ) - 1000000 -
    743144 * (count 30 6 r : ℤ) - 974745 * (count 30 10 r : ℤ) -
      1068929 * (count 30 15 r : ℤ)

private def numData : ℕ → ℤ
  | 0 => -1000000
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => -743144
  | 7 => 256856
  | 8 => 256856
  | 9 => 256856
  | 10 => -717889
  | 11 => 282111
  | 12 => -461033
  | 13 => 538967
  | 14 => 538967
  | 15 => -529962
  | 16 => -529962
  | 17 => 470038
  | 18 => -273106
  | 19 => 726894
  | 20 => -247851
  | 21 => -247851
  | 22 => -247851
  | 23 => 752149
  | 24 => 9005
  | 25 => 9005
  | 26 => 9005
  | 27 => 9005
  | 28 => 9005
  | 29 => 1009005
  | _ => 0

private theorem data_check : ∀ r : Fin 30, numerator r.val = numData r.val := by decide

private theorem divisor_check : properUpperDivisors 30 5 = {6,10,15} := by decide

private theorem trial_data (r : ℕ) (hr : r < 30) :
    trialResidual 30 5 trialCoeff r = (numData r : ℝ) / 1000000 := by
  have hn := data_check ⟨r,hr⟩
  change numerator r = numData r at hn
  rw [← hn]
  norm_num [trialResidual, synthesis, divisor_check, target, trialCoeff,
    atom_eq_count, numerator]
  ring

private theorem atom_column (d r : ℕ) (hd : d ∈ ({6,10,15} : Finset ℕ)) (hr : r < 30) :
    atom 30 d r = (r / d : ℕ) := by
  have hc : ∀ r : Fin 30,
      count 30 6 r.val = r.val / 6 ∧ count 30 10 r.val = r.val / 10 ∧
        count 30 15 r.val = r.val / 15 := by decide
  obtain ⟨h6,h10,h15⟩ := hc ⟨r,hr⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl
  · rw [atom_eq_count]
    exact_mod_cast h6
  · rw [atom_eq_count]
    exact_mod_cast h10
  · rw [atom_eq_count]
    exact_mod_cast h15

private def data (r : ℕ) : ℚ := (numData r : ℚ) / 1000000

private def energyInterval : RatInterval :=
  RatInterval.sum (Finset.range 29) (fun j =>
    RatInterval.mul (elementaryProgressionInterval 30 (j+1) 8)
      (RatInterval.point (data (j+1) ^ 2)))

private def defectInterval (K d : ℕ) : RatInterval :=
  RatInterval.sum (Finset.range 29) (fun j =>
    RatInterval.mul (elementaryProgressionInterval 30 (j+1) K)
      (RatInterval.point (data (j+1) * (((j+1)/d : ℕ) : ℚ))))

private theorem data_cast (r : ℕ) (hr : r < 30) :
    (data r : ℝ) = trialResidual 30 5 trialCoeff r := by
  rw [trial_data r hr]
  simp [data]

private theorem energyInterval_contains :
    energyInterval.Contains (trialEnergy 30 5 trialCoeff) := by
  unfold energyInterval trialEnergy energy
  norm_num only [Nat.reduceSub]
  rw [sum_Icc_one]
  apply RatInterval.contains_sum
  intro j hj
  have hr : j+1 < 30 := by have hh := Finset.mem_range.mp hj; omega
  have hw := elementaryProgressionInterval_contains 30 (j+1) 8 (by norm_num) (by omega)
  have hp := RatInterval.contains_point (data (j+1) ^ 2)
  simpa only [Rat.cast_pow, data_cast (j+1) hr] using RatInterval.contains_mul hw hp

private theorem defectInterval_contains (K d : ℕ) (hd : d ∈ ({6,10,15} : Finset ℕ)) :
    (defectInterval K d).Contains (normalDefect 30 5 trialCoeff d) := by
  unfold defectInterval normalDefect pairing
  norm_num only [Nat.reduceSub]
  rw [sum_Icc_one]
  apply RatInterval.contains_sum
  intro j hj
  have hr : j+1 < 30 := by have hh := Finset.mem_range.mp hj; omega
  have hw := elementaryProgressionInterval_contains 30 (j+1) K (by norm_num) (by omega)
  have hp := RatInterval.contains_point (data (j+1) * (((j+1)/d : ℕ) : ℚ))
  have he : ((data (j+1) * (((j+1)/d : ℕ) : ℚ) : ℚ) : ℝ) =
      trialResidual 30 5 trialCoeff (j+1) * atom 30 d (j+1) := by
    push_cast
    rw [data_cast (j+1) hr, atom_column d (j+1) hd hr]
  simpa only [he, mul_assoc] using RatInterval.contains_mul hw hp

set_option maxHeartbeats 10000000 in
-- Exact finite interval sums require large rational arithmetic, with no numerical oracle.
set_option maxRecDepth 100000 in
private theorem endpoint_checks :
    ((3798 / 100000) : ℚ) ≤ energyInterval.lo ∧ energyInterval.hi ≤ ((3807 / 100000) : ℚ) ∧
    RatInterval.absBound (defectInterval 8 6) ≤ ((15 / 100000) : ℚ) ∧
    RatInterval.absBound (defectInterval 8 10) ≤ ((75 / 1000000) : ℚ) ∧
    RatInterval.absBound (defectInterval 8 15) ≤ ((37 / 1000000) : ℚ) := by
  norm_num [energyInterval, defectInterval, elementaryProgressionInterval,
    RatInterval.sum, RatInterval.mul, RatInterval.point, RatInterval.absBound,
    data, numData, Finset.sum_range_succ]

/-- Complete actual optimizer enclosure, checked entirely by Lean. -/
theorem primorial_five_energy_interval :
    ((379 / 10000) : ℝ) ≤ atomEnergy (MobiusHeadGreen.greenPeriod 5) 5 ∧
      atomEnergy (MobiusHeadGreen.greenPeriod 5) 5 ≤ ((381 / 10000) : ℝ) := by
  have hP : MobiusHeadGreen.greenPeriod 5 = 30 := by decide
  rw [hP]
  obtain ⟨heLo,heHi,h6,h10,h15⟩ := endpoint_checks
  have he := energyInterval_contains
  have helo : ((3798 / 100000) : ℝ) ≤ trialEnergy 30 5 trialCoeff :=
    (show ((3798 / 100000) : ℝ) ≤ (energyInterval.lo : ℝ) by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using
        ((Rat.cast_le (K := ℝ)).2 heLo)).trans he.1
  have hehi : trialEnergy 30 5 trialCoeff ≤ ((3807 / 100000) : ℝ) :=
    he.2.trans (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ((Rat.cast_le (K := ℝ)).2 heHi))
  have hb6 : |normalDefect 30 5 trialCoeff 6| ≤ ((15 / 100000) : ℝ) :=
    (RatInterval.abs_le_absBound (defectInterval_contains 8 6 (by simp))).trans
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ((Rat.cast_le (K := ℝ)).2 h6))
  have hb10 : |normalDefect 30 5 trialCoeff 10| ≤ ((75 / 1000000) : ℝ) :=
    (RatInterval.abs_le_absBound (defectInterval_contains 8 10 (by simp))).trans
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ((Rat.cast_le (K := ℝ)).2 h10))
  have hb15 : |normalDefect 30 5 trialCoeff 15| ≤ ((37 / 1000000) : ℝ) :=
    (RatInterval.abs_le_absBound (defectInterval_contains 8 15 (by simp))).trans
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ((Rat.cast_le (K := ℝ)).2 h15))
  have hs6 : normalDefect 30 5 trialCoeff 6 ^ 2 ≤ ((15 / 100000) : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 hb6
  have hs10 : normalDefect 30 5 trialCoeff 10 ^ 2 ≤ ((75 / 1000000) : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 hb10
  have hs15 : normalDefect 30 5 trialCoeff 15 ^ 2 ≤ ((37 / 1000000) : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 hb15
  have hb := trial_energy_enclosure 30 5 (by norm_num) trialCoeff
  norm_num [divisor_check] at hb
  constructor <;> nlinarith [hb.1,hb.2]

private def probeData (r : ℕ) : ℚ :=
  (111 * (r : ℚ) - 7 * (r / 2 : ℕ) - 125 * (r / 3 : ℕ) -
    361 * (r / 5 : ℕ)) / 191

private theorem probeData_cast (r : ℕ) :
    (probeData r : ℝ) = fittedMomentProbe 5 r := by
  rw [ExactHeadAtomStageFiveMoment.probe_formula]
  norm_num [probeData]

private def momentInterval : RatInterval :=
  RatInterval.sum (Finset.range 29) (fun j =>
    RatInterval.mul (elementaryProgressionInterval 30 (j+1) 16)
      (RatInterval.point (data (j+1) * probeData (j+1))))

private def probeNormInterval : RatInterval :=
  RatInterval.sum (Finset.range 29) (fun j =>
    RatInterval.mul (elementaryProgressionInterval 30 (j+1) 8)
      (RatInterval.point (probeData (j+1) ^ 2)))

private theorem momentInterval_contains :
    momentInterval.Contains (trialFittedMoment 30 5 trialCoeff) := by
  unfold momentInterval trialFittedMoment pairing
  norm_num only [Nat.reduceSub]
  rw [sum_Icc_one]
  apply RatInterval.contains_sum
  intro j hj
  have hr : j+1 < 30 := by have hh := Finset.mem_range.mp hj; omega
  have hw := elementaryProgressionInterval_contains 30 (j+1) 16 (by norm_num) (by omega)
  have hp := RatInterval.contains_point (data (j+1) * probeData (j+1))
  simpa only [Rat.cast_mul, data_cast (j+1) hr, probeData_cast, mul_assoc] using
    RatInterval.contains_mul hw hp

private theorem probeNormInterval_contains :
    probeNormInterval.Contains
      (energy (Finset.Icc 1 29) (progressionWeight 30) (fittedMomentProbe 5)) := by
  unfold probeNormInterval energy
  rw [sum_Icc_one]
  apply RatInterval.contains_sum
  intro j hj
  have hw := elementaryProgressionInterval_contains 30 (j+1) 8 (by norm_num) (by omega)
  have hp := RatInterval.contains_point (probeData (j+1) ^ 2)
  simpa only [Rat.cast_pow, probeData_cast] using RatInterval.contains_mul hw hp

set_option maxHeartbeats 20000000 in
-- Sixteen complete-weight prefix terms resolve the strict signed-moment margin.
set_option maxRecDepth 100000 in
private theorem moment_endpoint_checks :
    ((2665 / 100000) : ℚ) ≤ momentInterval.lo ∧
    momentInterval.hi ≤ ((2668 / 100000) : ℚ) ∧
    probeNormInterval.hi ≤ ((71 / 100) : ℚ) ∧
    RatInterval.absBound (defectInterval 16 6) ≤ ((4 / 100000) : ℚ) ∧
    RatInterval.absBound (defectInterval 16 10) ≤ ((2 / 100000) : ℚ) ∧
    RatInterval.absBound (defectInterval 16 15) ≤ ((1 / 100000) : ℚ) := by
  norm_num [momentInterval, probeNormInterval, defectInterval, elementaryProgressionInterval,
    RatInterval.sum, RatInterval.mul, RatInterval.point, RatInterval.absBound,
    data, numData, probeData, Finset.sum_range_succ]

/-- Complete actual moment enclosure, with certified optimizer error. -/
theorem fitted_moment_five_interval :
    ((251 / 10000) : ℝ) ≤ atomFittedMoment 30 5 ∧
      atomFittedMoment 30 5 ≤ ((282 / 10000) : ℝ) := by
  obtain ⟨hl,hu,hp,h6,h10,h15⟩ := moment_endpoint_checks
  have hm := momentInterval_contains
  have hmlo : ((2665 / 100000) : ℝ) ≤ trialFittedMoment 30 5 trialCoeff :=
    (show ((2665 / 100000) : ℝ) ≤ (momentInterval.lo : ℝ) by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using ((Rat.cast_le (K := ℝ)).2 hl)).trans hm.1
  have hmhi : trialFittedMoment 30 5 trialCoeff ≤ ((2668 / 100000) : ℝ) :=
    hm.2.trans (by simpa only [Rat.cast_div, Rat.cast_ofNat] using
      ((Rat.cast_le (K := ℝ)).2 hu))
  have hphi : energy (Finset.Icc 1 29) (progressionWeight 30) (fittedMomentProbe 5) ≤
      ((71 / 100) : ℝ) := probeNormInterval_contains.2.trans
        (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ((Rat.cast_le (K := ℝ)).2 hp))
  have hd6 : |normalDefect 30 5 trialCoeff 6| ≤ ((4 / 100000) : ℝ) :=
    (RatInterval.abs_le_absBound (defectInterval_contains 16 6 (by simp))).trans
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ((Rat.cast_le (K := ℝ)).2 h6))
  have hd10 : |normalDefect 30 5 trialCoeff 10| ≤ ((2 / 100000) : ℝ) :=
    (RatInterval.abs_le_absBound (defectInterval_contains 16 10 (by simp))).trans
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ((Rat.cast_le (K := ℝ)).2 h10))
  have hd15 : |normalDefect 30 5 trialCoeff 15| ≤ ((1 / 100000) : ℝ) :=
    (RatInterval.abs_le_absBound (defectInterval_contains 16 15 (by simp))).trans
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using
        ((Rat.cast_le (K := ℝ)).2 h15))
  have hs6 : normalDefect 30 5 trialCoeff 6 ^ 2 ≤ ((4 / 100000) : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 hd6
  have hs10 : normalDefect 30 5 trialCoeff 10 ^ 2 ≤ ((2 / 100000) : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 hd10
  have hs15 : normalDefect 30 5 trialCoeff 15 ^ 2 ≤ ((1 / 100000) : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 hd15
  have hbudget : defectBudget 30 5 trialCoeff ≤ ((31 / 10000000) : ℝ) := by
    norm_num [defectBudget, divisor_check]
    nlinarith only [hs6,hs10,hs15]
  have hs := trial_fitted_moment_error_sq_le 30 5 (by norm_num) trialCoeff
  have hprod := mul_le_mul hbudget hphi
    (energy_nonneg _ _ _ (fun r _ => progressionWeight_nonneg 30 r)) (by norm_num)
  have hsquare : (trialFittedMoment 30 5 trialCoeff - atomFittedMoment 30 5) ^ 2 ≤
      ((3 / 2000) : ℝ) ^ 2 := by
    norm_num only [Nat.reduceSub] at hs
    nlinarith only [hs,hprod]
  have habs : |trialFittedMoment 30 5 trialCoeff - atomFittedMoment 30 5| ≤
      ((3 / 2000) : ℝ) :=
    (sq_le_sq₀ (abs_nonneg _) (by norm_num)).1 (by simpa only [sq_abs] using hsquare)
  obtain ⟨hleft,hright⟩ := abs_le.mp habs
  constructor <;> linarith

/-- The finite proportional signed-moment target now has a kernel-checked provider. -/
theorem primorial_five_signed_moment_deficit :
    atomFittedMoment (MobiusHeadGreen.greenPeriod 5) 5 ≤
      (3 / 4) * atomEnergy (MobiusHeadGreen.greenPeriod 5) 5 := by
  have hP : MobiusHeadGreen.greenPeriod 5 = 30 := by decide
  have hq := primorial_five_energy_interval.1
  rw [hP] at hq ⊢
  linarith [fitted_moment_five_interval.2]

end RiemannResearch.RH.Pareto.ExactHeadAtomStageFive
