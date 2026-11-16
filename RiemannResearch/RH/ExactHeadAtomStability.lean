import RiemannResearch.RH.ExactHeadAtomCertification
import Mathlib.Tactic

/-!
# Certified observations of the exact-head atom optimizer
An actual normal-equation defect controls the complete residual energy error,
every proper coefficient, every sample, and every linear profile statistic.
This transfers rational trial data to the actual optimizer without an inverse.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer
open RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.RH.ExactHeadGreenProfile
open RiemannResearch.Analysis.FiniteProfileEnergy
open ExactHeadAtomCoercivity

def defectBudget (P x : ℕ) (u : ℕ → ℝ) : ℝ :=
  (4 * ∑ d ∈ properUpperDivisors P x, (d : ℝ) ^ 2) *
    ∑ d ∈ properUpperDivisors P x, normalDefect P x u d ^ 2

theorem residual_error_energy_eq_gap (P x : ℕ) (u : ℕ → ℝ) :
    energy (Finset.Icc 1 (P - 1)) (progressionWeight P)
      (fun r => trialResidual P x u r - atomResidual P x r) =
        trialEnergy P x u - atomEnergy P x := by
  rw [trial_energy_split, add_sub_cancel_left]
  unfold energy
  apply Finset.sum_congr rfl
  intro r hr
  dsimp only
  rw [trial_decomposition_on P x u r (by
    have hh := Finset.mem_Icc.mp hr; omega)]
  congr 2
  ring

theorem residual_error_energy_le (P x : ℕ) (hP : 0 < P) (u : ℕ → ℝ) :
    energy (Finset.Icc 1 (P - 1)) (progressionWeight P)
      (fun r => trialResidual P x u r - atomResidual P x r) ≤ defectBudget P x u := by
  rw [residual_error_energy_eq_gap]
  have h := (trial_energy_enclosure P x hP u).2
  change trialEnergy P x u ≤ atomEnergy P x + defectBudget P x u at h
  linarith

/-- Any fixed linear statistic can be certified from the same normal defect. -/
theorem trial_observation_error_sq_le (P x : ℕ) (hP : 0 < P)
    (u phi : ℕ → ℝ) :
    (pairing (Finset.Icc 1 (P - 1)) (progressionWeight P) (trialResidual P x u) phi -
      pairing (Finset.Icc 1 (P - 1)) (progressionWeight P) (atomResidual P x) phi) ^ 2 ≤
        defectBudget P x u *
          energy (Finset.Icc 1 (P - 1)) (progressionWeight P) phi := by
  have heq :
      pairing (Finset.Icc 1 (P - 1)) (progressionWeight P) (trialResidual P x u) phi -
      pairing (Finset.Icc 1 (P - 1)) (progressionWeight P) (atomResidual P x) phi =
      pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
        (fun r => trialResidual P x u r - atomResidual P x r) phi := by
    unfold pairing
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [heq]
  exact (pairing_sq_le _ _ _ _ (fun r _ => progressionWeight_nonneg P r)).trans
    (mul_le_mul_of_nonneg_right (residual_error_energy_le P x hP u)
      (energy_nonneg _ _ _ (fun r _ => progressionWeight_nonneg P r)))

theorem trial_coefficient_error_sq_le (P x : ℕ) (hP : 0 < P) (u : ℕ → ℝ)
    (d : ℕ) (hd : d ∈ properUpperDivisors P x) :
    (atomNormalCoefficients P x d - u d) ^ 2 ≤
      4 * (d : ℝ) ^ 2 * defectBudget P x u := by
  have hD := properUpperDivisors_properties P x d hd
  have hc := coefficient_sq_le_energy P hP (properUpperDivisors P x)
    (fun e => atomNormalCoefficients P x e - u e) d hd hD.1 hD.2.1 hD.2.2
  have he : energy (Finset.Icc 1 (P - 1)) (progressionWeight P)
      (synthesis P (properUpperDivisors P x)
        (fun e => atomNormalCoefficients P x e - u e)) ≤ defectBudget P x u := by
    have hs := trial_energy_split P x u
    have hb := (trial_energy_enclosure P x hP u).2
    change trialEnergy P x u ≤ atomEnergy P x + defectBudget P x u at hb
    linarith
  exact hc.trans (mul_le_mul_of_nonneg_left he (by positivity))

theorem trial_sample_error_sq_le (P x : ℕ) (hP : 0 < P) (u : ℕ → ℝ)
    (r : ℕ) (hr : r < P) :
    (trialResidual P x u r - atomResidual P x r) ^ 2 ≤
      (r : ℝ) * ((r : ℝ) + 1) * defectBudget P x u := by
  have he := residual_error_energy_le P x hP u
  have hz : trialResidual P x u 0 - atomResidual P x 0 = 0 := by
    rw [trial_decomposition_on P x u 0 hP, synthesis_zero]
    ring
  exact (sample_sq_le_energy P hP
    (fun n => trialResidual P x u n - atomResidual P x n) hz r hr).trans
      (mul_le_mul_of_nonneg_left he (by positivity))

def trialProfile (P x : ℕ) (u : ℕ → ℝ) (d : ℕ) : ℝ :=
  (d : ℝ) * score (Finset.Icc 1 (P - 1)) (progressionWeight P) (trialResidual P x u) d

/-- Complete error bound for each actual Green-profile coordinate. -/
theorem trial_profile_error_sq_le (P x : ℕ) (hP : 0 < P)
    (u : ℕ → ℝ) (d : ℕ) :
    (trialProfile P x u d - atomProfile P x d) ^ 2 ≤
      defectBudget P x u *
        energy (Finset.Icc 1 (P - 1)) (progressionWeight P)
          (fun r => (d : ℝ) * grid d r) := by
  have h := trial_observation_error_sq_le P x hP u (fun r => (d : ℝ) * grid d r)
  convert h using 1
  congr 1
  unfold trialProfile atomProfile score pairing
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro r hr <;> ring

end RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer
