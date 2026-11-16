import RiemannResearch.RH.ExactHeadAtomOptimizer
import RiemannResearch.Analysis.ParetoProgressionCertificates
import Mathlib.Tactic

/-!
# A kernel-checkable complete Green stage at x=3
The actual period-six residual is supported only at residue five. Its profile
is exactly affine, yet its signed moment is twice its positive energy. This
keeps the dispersion and signed-moment obligations distinct.
The numerical energy interval includes the entire infinite progression.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadAtomSmallStage
open RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.RH.ExactHeadGreenProfile
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.Analysis.ParetoProgressionCertificates
open RiemannResearch.Analysis.LogRationalCertificates
open RiemannResearch.NumberTheory.DivisorIncidence
open ExactHeadAtomOptimizer

theorem residual_six_three (r : ℕ) (hr : r ∈ Finset.Icc 1 5) :
    atomResidual 6 3 r = if r = 5 then 1 else 0 := by
  have hD : upperDivisors 6 3 = {6} := by decide
  have hlt : r < 6 := by have hh := Finset.mem_Icc.mp hr; omega
  have he : atomResidual 6 3 r = target 6 r := by
    simp [atomResidual,hD,atom_zero_of_lt 6 6 r hlt]
  rw [he]
  have hcounts : ∀ n : Fin 6,
      ((Finset.Icc 1 n.val).filter (fun k => Nat.gcd k 6 = 1)).card =
        if n.val = 0 then 0 else if n.val = 5 then 2 else 1 := by decide
  have hc := hcounts ⟨r,hlt⟩
  change ((Finset.Icc 1 r).filter (fun k => Nat.gcd k 6 = 1)).card =
    (if r = 0 then 0 else if r = 5 then 2 else 1) at hc
  have hr0 : r ≠ 0 := by have hh := Finset.mem_Icc.mp hr; omega
  by_cases h5 : r = 5
  · subst r
    norm_num at hc
    norm_num [target,atom,hc]
  · simp [target,atom,hc,hr0,h5]

theorem energy_six_three : atomEnergy 6 3 = progressionWeight 6 5 := by
  unfold atomEnergy energy
  norm_num only [Nat.reduceSub]
  calc
    _ = ∑ r ∈ Finset.Icc 1 5, if r = 5 then progressionWeight 6 r else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [residual_six_three r hr]
      split_ifs <;> simp
    _ = _ := by simp

theorem profile_six_three (d : ℕ) :
    atomProfile 6 3 d = (d : ℝ) * progressionWeight 6 5 * (5 / d : ℕ) := by
  unfold atomProfile score pairing
  norm_num only [Nat.reduceSub]
  have hs : (∑ r ∈ Finset.Icc 1 5, progressionWeight 6 r * atomResidual 6 3 r * grid d r) =
      progressionWeight 6 5 * grid d 5 := by
    calc
      _ = ∑ r ∈ Finset.Icc 1 5, if r = 5 then progressionWeight 6 r * grid d r else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [residual_six_three r hr]
        split_ifs <;> simp
      _ = _ := by simp
  rw [hs]
  unfold grid
  ring

theorem profile_six_three_affine (d : ℕ) (hd : d ∈ Finset.Icc 1 3) :
    atomProfile 6 3 d = 6 * atomEnergy 6 3 -
      3 * atomEnergy 6 3 * ((d : ℝ) / 3) := by
  rw [profile_six_three,energy_six_three]
  obtain ⟨hd1,hd3⟩ := Finset.mem_Icc.mp hd
  interval_cases d <;> norm_num <;> ring

theorem affine_loss_six_three_zero :
    affineLoss (Finset.Icc 1 3) MobiusAffineProfile.weight (fun d => (d : ℝ) / 3)
      (atomProfile 6 3) (6 * atomEnergy 6 3) (-3 * atomEnergy 6 3) = 0 := by
  unfold affineLoss energy
  apply Finset.sum_eq_zero
  intro d hd
  dsimp only
  rw [profile_six_three_affine d hd]
  ring

theorem signed_moment_six_three :
    MobiusAffineProfile.signedSum 3 (atomProfile 6 3) = 2 * atomEnergy 6 3 := by
  rw [energy_six_three]
  norm_num [MobiusAffineProfile.signedSum, sum_Icc_one, Finset.sum_range_succ,
    profile_six_three, ArithmeticFunction.moebius_apply_one,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  ring

set_option maxHeartbeats 10000000 in
-- Exact rational endpoint evaluation expands finite sums of large fractions.
set_option maxRecDepth 100000 in
/-- Rational endpoints are checked by Lean; no external numerical premise. -/
theorem energy_six_three_interval :
    (0.05225229129512139667270 : ℝ) ≤ atomEnergy 6 3 ∧
      atomEnergy 6 3 ≤ (0.05225229129512139667271 : ℝ) := by
  have h := paretoProgressionInterval_contains (5 : ℚ) 6 16 (by norm_num)
    (by norm_num) (by norm_num)
  have he := paretoProgression_eq_progressionWeight 6 5
  norm_num only [Nat.cast_ofNat] at he
  norm_num only [Rat.cast_ofNat] at h
  rw [he] at h
  rw [energy_six_three]
  norm_num [RiemannResearch.RatInterval.Contains, paretoProgressionInterval,
    paretoRationalPart, correctionCoefficient, logOnePlusInvInterval,
    Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2]

theorem signed_moment_six_three_gt_energy :
    atomEnergy 6 3 < MobiusAffineProfile.signedSum 3 (atomProfile 6 3) := by
  rw [signed_moment_six_three]
  linarith [energy_six_three_interval.1]

end RiemannResearch.RH.Pareto.ExactHeadAtomSmallStage
