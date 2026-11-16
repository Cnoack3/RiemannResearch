import RiemannResearch.RH.MobiusHeadGreenNormal
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

private def defectInterval (d : ℕ) : RatInterval :=
  RatInterval.sum (Finset.range 29) (fun j =>
    RatInterval.mul (elementaryProgressionInterval 30 (j+1) 8)
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

private theorem defectInterval_contains (d : ℕ) (hd : d ∈ ({6,10,15} : Finset ℕ)) :
    (defectInterval d).Contains (normalDefect 30 5 trialCoeff d) := by
  unfold defectInterval normalDefect pairing
  norm_num only [Nat.reduceSub]
  rw [sum_Icc_one]
  apply RatInterval.contains_sum
  intro j hj
  have hr : j+1 < 30 := by have hh := Finset.mem_range.mp hj; omega
  have hw := elementaryProgressionInterval_contains 30 (j+1) 8 (by norm_num) (by omega)
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
    RatInterval.absBound (defectInterval 6) ≤ ((15 / 100000) : ℚ) ∧
    RatInterval.absBound (defectInterval 10) ≤ ((75 / 1000000) : ℚ) ∧
    RatInterval.absBound (defectInterval 15) ≤ ((37 / 1000000) : ℚ) := by
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
    (RatInterval.abs_le_absBound (defectInterval_contains 6 (by simp))).trans
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ((Rat.cast_le (K := ℝ)).2 h6))
  have hb10 : |normalDefect 30 5 trialCoeff 10| ≤ ((75 / 1000000) : ℝ) :=
    (RatInterval.abs_le_absBound (defectInterval_contains 10 (by simp))).trans
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using ((Rat.cast_le (K := ℝ)).2 h10))
  have hb15 : |normalDefect 30 5 trialCoeff 15| ≤ ((37 / 1000000) : ℝ) :=
    (RatInterval.abs_le_absBound (defectInterval_contains 15 (by simp))).trans
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

end RiemannResearch.RH.Pareto.ExactHeadAtomStageFive
