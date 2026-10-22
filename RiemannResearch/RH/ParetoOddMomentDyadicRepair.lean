/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoOddMomentDyadicObstruction
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.ParetoMellinDilation

/-!
# Full-energy obstruction to repeated dyadic Mellin repairs

Source: independently derived continuation of the user-provided
ParetoCapacityFormalization20260921_Continued_Dyadic (1)(1).md,
2026-09-21. No novelty claim is intended.

The three-scale repair is I - 2 T_2, where the actual Hilbert dilation
T_2 has norm sqrt(2) on every vector. Its exact signed energy and reverse
triangle bound exclude small energy for all normalized signed packet
mixtures, including arbitrarily many repeated repairs. This is an
obstruction to this restricted construction, not to the full odd Schur
problem, and it neither assumes nor proves RH.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

/-- The actual operator implementing the second dyadic Mellin repair. -/
def dyadicMellinRepair : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  ContinuousLinearMap.id ℝ ThresholdHilbert -
    (2 : ℝ) • hilbertDilationContinuous 2 (by norm_num)

theorem dyadicMellinRepair_apply (f : ThresholdHilbert) :
    dyadicMellinRepair f = f - (2 : ℝ) • hilbertDilation 2 (by norm_num) f := rfl

theorem dyadicMellinRepair_energy (f : ThresholdHilbert) :
    ‖dyadicMellinRepair f‖^2 = 9 * ‖f‖^2 -
      4 * inner ℝ f (hilbertDilation 2 (by norm_num) f) := by
  rw [dyadicMellinRepair_apply, norm_sub_sq_real, norm_smul,
    inner_smul_right, mul_pow, hilbertDilation_norm_sq]
  norm_num
  ring

theorem dyadicMellinRepair_norm_lower (f : ThresholdHilbert) :
    (2 * Real.sqrt 2 - 1) * ‖f‖ ≤ ‖dyadicMellinRepair f‖ := by
  have h := norm_sub_norm_le ((2 : ℝ) • hilbertDilation 2 (by norm_num) f) f
  rw [norm_smul, hilbertDilation_norm] at h
  norm_num at h
  rw [dyadicMellinRepair_apply, norm_sub_rev]
  nlinarith

theorem dyadicMellinRepair_factor_gt_one : 1 < 2 * Real.sqrt 2 - 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

theorem dyadicMellinRepair_energy_lower (f : ThresholdHilbert) :
    (2 * Real.sqrt 2 - 1)^2 * ‖f‖^2 ≤ ‖dyadicMellinRepair f‖^2 := by
  have h := dyadicMellinRepair_norm_lower f
  have hp : 0 ≤ (2 * Real.sqrt 2 - 1) * ‖f‖ :=
    mul_nonneg (le_of_lt (lt_trans zero_lt_one dyadicMellinRepair_factor_gt_one))
      (norm_nonneg _)
  have hh := (sq_le_sq₀ hp (norm_nonneg _)).mpr h
  simpa only [mul_pow] using hh

theorem dyadicMellinRepair_mellin_two (f : ThresholdHilbert) :
    paretoMellin (dyadicMellinRepair f) 2 = 0 := by
  rw [dyadicMellinRepair_apply]
  change paretoMellinContinuous 2 (by norm_num)
    (f - (2 : ℝ) • hilbertDilation 2 (by norm_num) f) = 0
  rw [map_sub, map_smul]
  change paretoMellin f 2 - (2 : ℂ) *
    paretoMellin (hilbertDilation 2 (by norm_num) f) 2 = 0
  rw [paretoMellin_dilation]
  norm_num [Complex.cpow_neg_one]
  ring

/-- Iterating the same repair preserves legality of finite residue packets. -/
def iteratedDyadicRepair : ℕ → ThresholdHilbert → ThresholdHilbert
  | 0, f => f
  | r + 1, f => dyadicMellinRepair (iteratedDyadicRepair r f)

theorem iteratedDyadicRepair_norm_lower (r : ℕ) (f : ThresholdHilbert) :
    (2 * Real.sqrt 2 - 1)^r * ‖f‖ ≤ ‖iteratedDyadicRepair r f‖ := by
  induction r with
  | zero => simp [iteratedDyadicRepair]
  | succ r ih =>
    have hp : 0 ≤ 2 * Real.sqrt 2 - 1 :=
      le_of_lt (lt_trans zero_lt_one dyadicMellinRepair_factor_gt_one)
    calc
      _ = (2 * Real.sqrt 2 - 1) * ((2 * Real.sqrt 2 - 1)^r * ‖f‖) := by
        rw [pow_succ]; ring
      _ ≤ (2 * Real.sqrt 2 - 1) * ‖iteratedDyadicRepair r f‖ :=
        mul_le_mul_of_nonneg_left ih hp
      _ ≤ _ := dyadicMellinRepair_norm_lower _

theorem iteratedDyadicRepair_energy_lower (r : ℕ) (f : ThresholdHilbert) :
    (2 * Real.sqrt 2 - 1)^(2*r) * ‖f‖^2 ≤ ‖iteratedDyadicRepair r f‖^2 := by
  have hp : 0 ≤ (2 * Real.sqrt 2 - 1)^r * ‖f‖ := by
    apply mul_nonneg _ (norm_nonneg _)
    exact pow_nonneg (le_of_lt (lt_trans zero_lt_one dyadicMellinRepair_factor_gt_one)) _
  have h := (sq_le_sq₀ hp (norm_nonneg _)).mpr (iteratedDyadicRepair_norm_lower r f)
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm r 2] using h

namespace CoefficientStabilization.TailCapacity

theorem dyadicTailPacket_dilation_two (k : ℕ) :
    hilbertDilation 2 (by norm_num) (dyadicTailPacket k) =
      (2 : ℝ) • dyadicTailPacket (2*k+2) := by
  rw [dyadicTailPacket_eq_residues]
  change hilbertDilationContinuous 2 (by norm_num)
    (residueAtom k - (2 : ℝ) • residueAtom (2*k+2)) = _
  rw [map_sub, map_smul]
  simp only [hilbertDilationContinuous_apply, hilbertDilation_residueAtom]
  rw [dyadicTailPacket_eq_residues]
  have hi₁ : 2 * (k+2) = 2*k+2+2 := by omega
  have hi₂ : 2 * (2*k+2+2) = (2*(2*k+2)+2)+2 := by omega
  simp only [hi₁, hi₂, Nat.cast_ofNat]
  have hc : (2 : ℝ) / (k+2 : ℕ) =
      2 * (2 / ((2*k+2+2 : ℕ) : ℝ)) := by
    push_cast
    field_simp
    <;> ring
  rw [hc]
  simp only [residueAtom]
  module

theorem mellinRepairedPacket_eq_repair (k : ℕ) :
    mellinRepairedPacket k = dyadicMellinRepair (dyadicTailPacket k) := by
  rw [dyadicMellinRepair_apply, dyadicTailPacket_dilation_two]
  unfold mellinRepairedPacket
  module

theorem mellinRepairedCombination_eq_repair (n : ℕ) (b : OddTailIndex n → ℝ) :
    (∑ j, b j • mellinRepairedPacket j.val.val) =
      dyadicMellinRepair (dyadicPacketCombination n b) := by
  unfold dyadicPacketCombination
  simp only [map_sum, map_smul, mellinRepairedPacket_eq_repair]

theorem mellinRepairedCombination_energy (n : ℕ) (b : OddTailIndex n → ℝ) :
    ‖∑ j, b j • mellinRepairedPacket j.val.val‖^2 =
      9 * ‖dyadicPacketCombination n b‖^2 -
        4 * inner ℝ (dyadicPacketCombination n b)
          (hilbertDilation 2 (by norm_num) (dyadicPacketCombination n b)) := by
  rw [mellinRepairedCombination_eq_repair, dyadicMellinRepair_energy]

theorem mellinRepairedCombination_energy_lower (n : ℕ) (b : OddTailIndex n → ℝ)
    (hm : (∑ j, b j / ((j.val.val+2 : ℕ) : ℝ)^2) = 1) :
    (2 * Real.sqrt 2 - 1)^2 * (81 * ‖riemannZeta 2‖^2 / 16) ≤
      ‖∑ j, b j • mellinRepairedPacket j.val.val‖^2 := by
  rw [mellinRepairedCombination_eq_repair]
  exact (mul_le_mul_of_nonneg_left (dyadicPacketCombination_energy_lower n b hm)
    (sq_nonneg _)).trans (dyadicMellinRepair_energy_lower _)

theorem iteratedDyadicPacket_energy_lower (r n : ℕ) (b : OddTailIndex n → ℝ)
    (hm : (∑ j, b j / ((j.val.val+2 : ℕ) : ℝ)^2) = 1) :
    (2 * Real.sqrt 2 - 1)^(2*r) * (81 * ‖riemannZeta 2‖^2 / 16) ≤
      ‖iteratedDyadicRepair r (dyadicPacketCombination n b)‖^2 := by
  have hp : 0 ≤ (2 * Real.sqrt 2 - 1)^(2*r) :=
    pow_nonneg (le_of_lt (lt_trans zero_lt_one dyadicMellinRepair_factor_gt_one)) _
  exact (mul_le_mul_of_nonneg_left (dyadicPacketCombination_energy_lower n b hm) hp).trans
    (iteratedDyadicRepair_energy_lower _ _)

theorem iteratedDyadicPacket_uniform_floor (r n : ℕ) (b : OddTailIndex n → ℝ)
    (hm : (∑ j, b j / ((j.val.val+2 : ℕ) : ℝ)^2) = 1) :
    81 * ‖riemannZeta 2‖^2 / 16 ≤
      ‖iteratedDyadicRepair r (dyadicPacketCombination n b)‖^2 := by
  have hp : 1 ≤ (2 * Real.sqrt 2 - 1)^(2*r) :=
    one_le_pow₀ (le_of_lt dyadicMellinRepair_factor_gt_one)
  have hh := mul_le_mul_of_nonneg_right hp (le_of_lt dyadicPacket_energy_floor_pos)
  simp only [one_mul] at hh
  exact hh.trans (iteratedDyadicPacket_energy_lower r n b hm)

end CoefficientStabilization.TailCapacity
end RiemannResearch.RH.Pareto
