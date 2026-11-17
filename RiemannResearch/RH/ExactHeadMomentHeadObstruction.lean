import RiemannResearch.RH.ExactHeadAtomMoment
import RiemannResearch.RH.ExactHeadAtomStageFiveMoment
import RiemannResearch.RH.ParetoPeriodicRegrouping
import Mathlib.Tactic

/-!
# The part of a centered moment probe that upper corrections cannot change

The head obstruction is a necessary test for the user's R5 proposal. It can
be evaluated using only the cutoff x, without forming the primorial period.
This is an exact finite lower bound; it supplies no asymptotic upper bound.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer
open RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.Analysis.FiniteProfileEnergy
open MobiusHeadGreen
open RiemannResearch.NumberTheory.DivisorIncidence

theorem upper_span_zero_on_head (P x r : ℕ) (hr : r ≤ x)
    (v : ℕ → ℝ) (hv : v ∈ upperSpan P x (atom P)) : v r = 0 := by
  let ev : (ℕ → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => f r
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : upperSpan P x (atom P) ≤ ev.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨d, hd, rfl⟩
    change atom P d r = 0
    exact atom_zero_of_lt P d r (hr.trans_lt (Finset.mem_filter.mp hd).2)
  exact hle hv

theorem primorial_target_zero_on_head (x r : ℕ) (hr : r ∈ Finset.Icc 1 x) :
    target (greenPeriod x) r = 0 := by
  obtain ⟨hr1, hrx⟩ := Finset.mem_Icc.mp hr
  have hrP : r ∈ Finset.Icc 1 (greenPeriod x - 1) :=
    Finset.mem_Icc.mpr ⟨hr1, by have hp := greenPeriod_gt x; omega⟩
  have hz := residual_head (greenPeriod x) x (greenPeriod_gt x).le
    (primorialNormalCoefficients x) (primorialNormalCoefficients_spec x).1 r hr1 hrx
  rw [primorial_residual_eq_atomResidual x r hrP] at hz
  have hd := upper_span_zero_on_head (greenPeriod x) x r hrx
    (atomResidual (greenPeriod x) x - target (greenPeriod x))
    (atomResidual_sub_target_mem (greenPeriod x) x)
  change atomResidual (greenPeriod x) x r - target (greenPeriod x) r = 0 at hd
  linarith

def probeHeadEnergy (x : ℕ) : ℝ :=
  energy (Finset.Icc 1 x) positiveWeight (fittedMomentProbe x)

/-- Every alpha and every legal upper-span correction retain this whole head. -/
theorem probe_head_energy_le_centered (x : ℕ) (alpha : ℝ) (v : ℕ → ℝ)
    (hv : v ∈ upperSpan (greenPeriod x) x (atom (greenPeriod x))) :
    probeHeadEnergy x ≤
      energy (Finset.Icc 1 (greenPeriod x - 1)) (progressionWeight (greenPeriod x))
        (fun r => fittedMomentProbe x r - alpha * target (greenPeriod x) r - v r) := by
  have hP : 0 < greenPeriod x := lt_of_le_of_lt (Nat.zero_le x) (greenPeriod_gt x)
  calc
    probeHeadEnergy x ≤ energy (Finset.Icc 1 x) (progressionWeight (greenPeriod x))
        (fittedMomentProbe x) := by
      unfold probeHeadEnergy energy
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_right
        (positiveWeight_le_progressionWeight (greenPeriod x) r hP) (sq_nonneg _)
    _ = energy (Finset.Icc 1 x) (progressionWeight (greenPeriod x))
        (fun r => fittedMomentProbe x r - alpha * target (greenPeriod x) r - v r) := by
      apply Finset.sum_congr rfl
      intro r hr
      dsimp only
      rw [primorial_target_zero_on_head x r hr,
        upper_span_zero_on_head (greenPeriod x) x r (Finset.mem_Icc.mp hr).2 v hv]
      simp
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.Icc_subset_Icc_right (by have hp := greenPeriod_gt x; omega)
      · intro r hr hnot
        exact mul_nonneg (progressionWeight_nonneg _ _) (sq_nonneg _)

theorem probe_head_five_interval :
    ((6026 / 10000) : ℝ) ≤ probeHeadEnergy 5 ∧
      probeHeadEnergy 5 ≤ ((6027 / 10000) : ℝ) := by
  norm_num [probeHeadEnergy, energy, positiveWeight,
    ExactHeadAtomStageFiveMoment.probe_formula, sum_Icc_one, Finset.sum_range_succ]

theorem probe_head_three_energy : probeHeadEnergy 3 = (49 / 72 : ℝ) := by
  norm_num [probeHeadEnergy, energy, positiveWeight, fittedMomentProbe,
    affineMomentDual, mass, RiemannResearch.RH.MobiusAffineProfile.weight,
    RiemannResearch.RH.ExactHeadGreenProfile.grid,
    sum_Icc_one, Finset.sum_range_succ, ArithmeticFunction.moebius_apply_one,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three]

theorem probe_head_three_gt_two_thirds : (2 / 3 : ℝ) < probeHeadEnergy 3 := by
  rw [probe_head_three_energy]
  norm_num

/-- A uniform 2/3 proposal must exclude cutoff three, whatever alpha is chosen. -/
theorem centered_probe_three_gt_two_thirds (alpha : ℝ) (v : ℕ → ℝ)
    (hv : v ∈ upperSpan (greenPeriod 3) 3 (atom (greenPeriod 3))) :
    (2 / 3 : ℝ) <
      energy (Finset.Icc 1 (greenPeriod 3 - 1)) (progressionWeight (greenPeriod 3))
        (fun r => fittedMomentProbe 3 r - alpha * target (greenPeriod 3) r - v r) :=
  probe_head_three_gt_two_thirds.trans_le (probe_head_energy_le_centered 3 alpha v hv)

end RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer
