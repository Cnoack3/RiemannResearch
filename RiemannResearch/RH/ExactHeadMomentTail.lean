import RiemannResearch.RH.ExactHeadMomentHeadObstruction
import Mathlib.Tactic

/-!
# Tail-only certification of the affine Green signed moment

Source: user-provided "Exact-Head Green Profiles in the Nyman--Beurling Program",
27 July 2026, agenda R5, and the repository's 16 November continuation.
The exact-head residual annihilates every head-supported test function.
Consequently the full centered-probe energy can be replaced by its tail
energy. The complete head/tail equality and deficit bound are reused from
`ExactHeadAtomMoment`; this module retains the full tail Gram remainder. No uniform tail provider or RH conclusion is supplied here.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer
open RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.Analysis.FiniteProfileEnergy
open MobiusHeadGreen

private theorem primorial_atomResidual_zero_on_head (x r : ℕ)
    (hr : r ∈ Finset.Icc 1 x) : atomResidual (greenPeriod x) x r = 0 := by
  have hd := upper_span_zero_on_head (greenPeriod x) x r (Finset.mem_Icc.mp hr).2
    (atomResidual (greenPeriod x) x - target (greenPeriod x))
    (atomResidual_sub_target_mem (greenPeriod x) x)
  change atomResidual (greenPeriod x) x r - target (greenPeriod x) r = 0 at hd
  rw [primorial_target_zero_on_head x r hr, sub_zero] at hd
  exact hd

theorem primorial_pairing_eq_tail (x : ℕ) (g : ℕ → ℝ) :
    pairing (Finset.Icc 1 (greenPeriod x - 1)) (progressionWeight (greenPeriod x))
      (atomResidual (greenPeriod x) x) g =
    pairing (Finset.Icc (x + 1) (greenPeriod x - 1)) (progressionWeight (greenPeriod x))
      (atomResidual (greenPeriod x) x) g := by
  symm
  apply pairing_support
  · intro r hr
    obtain ⟨hrx, hrP⟩ := Finset.mem_Icc.mp hr
    exact Finset.mem_Icc.mpr ⟨by omega, hrP⟩
  · intro r hr hn
    apply primorial_atomResidual_zero_on_head
    simp only [Finset.mem_Icc] at *
    omega

theorem primorial_atomEnergy_eq_tail (x : ℕ) :
    atomEnergy (greenPeriod x) x =
      energy (Finset.Icc (x + 1) (greenPeriod x - 1)) (progressionWeight (greenPeriod x))
        (atomResidual (greenPeriod x) x) := by
  symm
  apply energy_support
  · intro r hr
    obtain ⟨hrx, hrP⟩ := Finset.mem_Icc.mp hr
    exact Finset.mem_Icc.mpr ⟨by omega, hrP⟩
  · intro r hr hn
    apply primorial_atomResidual_zero_on_head
    simp only [Finset.mem_Icc] at *
    omega

theorem primorial_tail_residues (x : ℕ) :
    Finset.Icc 1 (greenPeriod x - 1) \ Finset.Icc 1 x =
      Finset.Icc (x + 1) (greenPeriod x - 1) := by
  ext r
  simp only [Finset.mem_sdiff, Finset.mem_Icc]
  omega

def centeredMomentTailEnergy (x : ℕ) (alpha : ℝ) (v : ℕ → ℝ) : ℝ :=
  energy (Finset.Icc 1 (greenPeriod x - 1) \ Finset.Icc 1 x)
    (progressionWeight (greenPeriod x))
    (fun r => fittedMomentProbe x r - alpha * target (greenPeriod x) r - v r)

theorem centeredMomentTailEnergy_nonneg (x : ℕ) (alpha : ℝ) (v : ℕ → ℝ) :
    0 ≤ centeredMomentTailEnergy x alpha v :=
  energy_nonneg _ _ _ (fun r _ => progressionWeight_nonneg _ r)

theorem centered_tail_energy_le_full_sub_head (x : ℕ) (alpha : ℝ) (v : ℕ → ℝ)
    (hv : v ∈ upperSpan (greenPeriod x) x (atom (greenPeriod x))) :
    centeredMomentTailEnergy x alpha v ≤
      energy (Finset.Icc 1 (greenPeriod x - 1)) (progressionWeight (greenPeriod x))
        (fun r => fittedMomentProbe x r - alpha * target (greenPeriod x) r - v r) -
      probeHeadEnergy x := by
  rw [complete_centered_probe_energy_split x alpha v hv]
  change centeredMomentTailEnergy x alpha v ≤
    energy (Finset.Icc 1 x) (progressionWeight (greenPeriod x)) (fittedMomentProbe x) +
      centeredMomentTailEnergy x alpha v - probeHeadEnergy x
  have hh : probeHeadEnergy x ≤
      energy (Finset.Icc 1 x) (progressionWeight (greenPeriod x)) (fittedMomentProbe x) := by
    unfold probeHeadEnergy energy
    apply Finset.sum_le_sum
    intro r hr
    exact mul_le_mul_of_nonneg_right
      (positiveWeight_le_progressionWeight (greenPeriod x) r
        (lt_of_le_of_lt (Nat.zero_le x) (greenPeriod_gt x))) (sq_nonneg _)
  linarith

theorem fitted_moment_gap_eq_tail_pairing (x : ℕ) (alpha : ℝ) (v : ℕ → ℝ)
    (hv : v ∈ upperSpan (greenPeriod x) x (atom (greenPeriod x))) :
    atomFittedMoment (greenPeriod x) x - alpha * atomEnergy (greenPeriod x) x =
      pairing (Finset.Icc (x + 1) (greenPeriod x - 1)) (progressionWeight (greenPeriod x))
        (atomResidual (greenPeriod x) x)
        (fun r => fittedMomentProbe x r - alpha * target (greenPeriod x) r - v r) := by
  rw [fitted_moment_gap_eq_pairing _ _ _ _ hv, primorial_pairing_eq_tail]

theorem fitted_moment_tail_gram_identity (x : ℕ) (alpha : ℝ) (v : ℕ → ℝ)
    (hv : v ∈ upperSpan (greenPeriod x) x (atom (greenPeriod x))) :
    atomEnergy (greenPeriod x) x * centeredMomentTailEnergy x alpha v -
      (atomFittedMoment (greenPeriod x) x - alpha * atomEnergy (greenPeriod x) x) ^ 2 =
      (∑ r ∈ Finset.Icc (x + 1) (greenPeriod x - 1),
        ∑ s ∈ Finset.Icc (x + 1) (greenPeriod x - 1),
          progressionWeight (greenPeriod x) r * progressionWeight (greenPeriod x) s *
          (atomResidual (greenPeriod x) x r *
              (fittedMomentProbe x s - alpha * target (greenPeriod x) s - v s) -
            atomResidual (greenPeriod x) x s *
              (fittedMomentProbe x r - alpha * target (greenPeriod x) r - v r)) ^ 2) / 2 := by
  rw [fitted_moment_gap_eq_tail_pairing x alpha v hv]
  rw [primorial_atomEnergy_eq_tail]
  simp only [centeredMomentTailEnergy, primorial_tail_residues]
  exact gram_identity _ _ _ _

/-- Reuse both complete-weight certificates: deleting the head saves at least 0.6026. -/
theorem centered_tail_five_le :
    centeredMomentTailEnergy 5 (1 / 2) ExactHeadAtomStageFiveMoment.probeCorrection ≤
      (137 / 5000 : ℝ) := by
  have hP : greenPeriod 5 = 30 := by decide
  have hv : ExactHeadAtomStageFiveMoment.probeCorrection ∈
      upperSpan (greenPeriod 5) 5 (atom (greenPeriod 5)) := by
    simpa only [hP] using ExactHeadAtomStageFiveMoment.probeCorrection_mem
  have hh := centered_tail_energy_le_full_sub_head 5 (1 / 2)
    ExactHeadAtomStageFiveMoment.probeCorrection hv
  rw [hP] at hh
  change centeredMomentTailEnergy 5 (1 / 2) ExactHeadAtomStageFiveMoment.probeCorrection ≤
    energy (Finset.Icc 1 29) (progressionWeight 30)
      ExactHeadAtomStageFiveMoment.centeredProbe - probeHeadEnergy 5 at hh
  linarith [ExactHeadAtomStageFiveMoment.centered_probe_energy_interval.2,
    probe_head_five_interval.1]

/-- This finite tail provider is independent of any floating-point evaluation. -/
theorem fitted_moment_five_tail_deficit :
    atomFittedMoment (greenPeriod 5) 5 ≤
      (3 / 4) * atomEnergy (greenPeriod 5) 5 + 137 / 5000 := by
  have hP : greenPeriod 5 = 30 := by decide
  have hv : ExactHeadAtomStageFiveMoment.probeCorrection ∈
      upperSpan (greenPeriod 5) 5 (atom (greenPeriod 5)) := by
    simpa only [hP] using ExactHeadAtomStageFiveMoment.probeCorrection_mem
  have hh := fitted_moment_deficit_of_tail_probe_bound 5 (1 / 2) (137 / 5000) (1 / 4)
    (by norm_num) (by norm_num) ExactHeadAtomStageFiveMoment.probeCorrection hv
    centered_tail_five_le
  norm_num at hh ⊢
  exact hh

end RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer
