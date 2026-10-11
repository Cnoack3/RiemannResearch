/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.MellinNormalizedResidue
import RiemannResearch.RH.ParetoOddMomentParity
import RiemannResearch.RH.ParetoExactHeadResidual

/-!
# Matched dyadic corrections: Mellin obstruction and explicit repair

Source: independently derived continuation of the user-provided
ParetoCapacityFormalization20260921_Continued_Parity(1).md, 2026-09-21.
No novelty claim is intended. The existing normalized residue Mellin
identity and exact-head tail Cauchy inequality supply the proof.

All signed mixtures of g_d - 2 g_(2d) with odd reciprocal-square moment
one have a strictly positive full-energy floor. Escaping modulus support
strengthens this to a cubic bound. The three-scale correction
g_d - 6 g_(2d) + 8 g_(4d) cancels the s=2 obstruction exactly.
No decay of its full energy, or unconditional RH, is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.RH.ArithmeticCumulative

/-- The matched correction at modulus 2d, with d=k+2. -/
def dyadicTailPacket (k : ℕ) : ThresholdHilbert :=
  tailAtom k - (2 : ℝ) • tailAtom (2*k+2)

theorem dyadicTailPacket_eq_residues (k : ℕ) :
    dyadicTailPacket k = residueAtom k - (2 : ℝ) • residueAtom (2*k+2) := by
  have hcoef : 1 / ((k+2 : ℕ) : ℝ) -
      2 * (1 / ((2*k+2+2 : ℕ) : ℝ)) = 0 := by
    push_cast
    field_simp
    <;> ring
  unfold dyadicTailPacket tailAtom
  rw [← map_smul, ← map_sub]
  change residueAtom k - (2 : ℝ) • residueAtom (2*k+2) -
    (anchoredEvaluationCLM 1 (residueAtom k - (2 : ℝ) • residueAtom (2*k+2))) •
      paretoPointHilbert 0 = _
  rw [map_sub, map_smul, residueAtom_evaluation, residueAtom_evaluation]
  simp only [smul_eq_mul, hcoef, zero_smul, sub_zero]

theorem dyadicTailPacket_zero_head (k j : ℕ) (hj : j < k+2) :
    hilbertSequence (dyadicTailPacket k) j = 0 := by
  rw [dyadicTailPacket_eq_residues]
  change hilbertSequenceLinear (residueAtom k - (2 : ℝ) • residueAtom (2*k+2)) j = 0
  rw [map_sub, map_smul]
  change hilbertSequence (residueAtom k) j -
    2 * hilbertSequence (residueAtom (2*k+2)) j = 0
  simp only [residueAtom, normalizedResidueHilbert_sequence, residueFraction,
    Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt (by omega : j < 2*k+2+2)]
  push_cast
  field_simp
  <;> ring

private theorem normalizedResidue_mellin_two (d : ℕ) (hd : 0 < d) :
    paretoMellin (normalizedResidueHilbert d hd) 2 =
      riemannZeta 2 / 2 * (1 / (d : ℂ) - 1 / (d : ℂ)^2) := by
  have h := normalizedResidue_mellin_zeta d hd 2 (by norm_num) (by norm_num)
  have hp : (d : ℂ) ^ (-(2 : ℂ)) = 1 / (d : ℂ)^2 := by
    rw [Complex.cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num,
      Complex.cpow_natCast]
    simp only [one_div]
  rw [hp] at h
  linear_combination h / 2

theorem dyadicTailPacket_mellin_two (k : ℕ) :
    paretoMellin (dyadicTailPacket k) 2 =
      -(riemannZeta 2 / 4) / ((k+2 : ℕ) : ℂ)^2 := by
  rw [dyadicTailPacket_eq_residues]
  change paretoMellinContinuous 2 (by norm_num)
    (residueAtom k - (2 : ℝ) • residueAtom (2*k+2)) = _
  rw [map_sub, map_smul]
  change paretoMellin (normalizedResidueHilbert (k+2) _) 2 -
    (2 : ℂ) * paretoMellin (normalizedResidueHilbert (2*k+2+2) _) 2 = _
  rw [normalizedResidue_mellin_two, normalizedResidue_mellin_two]
  have hk : (k : ℂ) + 2 ≠ 0 := by
    exact_mod_cast (show k+2 ≠ 0 by omega)
  push_cast
  rw [show (2 : ℂ) * k + 2 + 2 = 2 * ((k : ℂ) + 2) by ring]
  field_simp [hk]
  <;> ring

/-- Arbitrary signed mixtures of matched packets. -/
def dyadicPacketCombination (n : ℕ) (b : OddTailIndex n → ℝ) : ThresholdHilbert :=
  ∑ j, b j • dyadicTailPacket j.val.val

theorem dyadicPacketCombination_zero_head (n : ℕ) (b : OddTailIndex n → ℝ)
    (j : ℕ) (hj : j ≤ 2) :
    hilbertSequence (dyadicPacketCombination n b) j = 0 := by
  change hilbertSequenceLinear (∑ i, b i • dyadicTailPacket i.val.val) j = 0
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  have hi := i.property
  change b i * hilbertSequence (dyadicTailPacket i.val.val) j = 0
  rw [dyadicTailPacket_zero_head i.val.val j (by omega), mul_zero]

theorem dyadicPacketCombination_mellin_two (n : ℕ) (b : OddTailIndex n → ℝ) :
    paretoMellin (dyadicPacketCombination n b) 2 =
      -(riemannZeta 2 / 4) *
        ((∑ j, b j / ((j.val.val+2 : ℕ) : ℝ)^2 : ℝ) : ℂ) := by
  change paretoMellinContinuous 2 (by norm_num) (∑ j, b j • dyadicTailPacket j.val.val) = _
  rw [map_sum]
  simp only [map_smul]
  change (∑ j, (b j : ℂ) * paretoMellin (dyadicTailPacket j.val.val) 2) = _
  simp only [dyadicTailPacket_mellin_two]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem dyadicPacketCombination_energy_lower (n : ℕ) (b : OddTailIndex n → ℝ)
    (hm : (∑ j, b j / ((j.val.val+2 : ℕ) : ℝ)^2) = 1) :
    81 * ‖riemannZeta 2‖^2 / 16 ≤ ‖dyadicPacketCombination n b‖^2 := by
  have h := paretoMellin_zero_head_norm_sq_le
    (N := 2) (f := dyadicPacketCombination n b)
    (fun j _ hj => dyadicPacketCombination_zero_head n b j hj)
    2 (by norm_num)
  rw [dyadicPacketCombination_mellin_two, hm] at h
  norm_num [norm_div, norm_neg, Real.rpow_neg, Real.rpow_natCast] at h
  nlinarith

theorem dyadicPacket_energy_floor_pos : 0 < 81 * ‖riemannZeta 2‖^2 / 16 := by
  have hz : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  positivity

/-- The independent correction must cancel the fixed Mellin value. -/
theorem dyadicPacket_correction_mellin (n : ℕ) (b : OddTailIndex n → ℝ)
    (hm : (∑ j, b j / ((j.val.val+2 : ℕ) : ℝ)^2) = 1)
    (v : ThresholdHilbert) :
    paretoMellin (dyadicPacketCombination n b + v) 2 =
      paretoMellin v 2 - riemannZeta 2 / 4 := by
  rw [paretoMellin_add _ _ _ (by norm_num), dyadicPacketCombination_mellin_two, hm]
  simp
  ring

theorem dyadicPacket_correction_energy_lower (n : ℕ) (b : OddTailIndex n → ℝ)
    (hm : (∑ j, b j / ((j.val.val+2 : ℕ) : ℝ)^2) = 1)
    (v : ThresholdHilbert) :
    3 * ‖paretoMellin v 2 - riemannZeta 2 / 4‖^2 ≤
      ‖dyadicPacketCombination n b + v‖^2 := by
  have h := paretoMellin_norm_sq_le (dyadicPacketCombination n b + v) 2 (by norm_num)
  rw [dyadicPacket_correction_mellin n b hm v] at h
  norm_num at h
  linarith

def dyadicPacketCoefficients (n : ℕ) (b : OddTailIndex n → ℝ) : Fin (2*n+2) → ℝ :=
  ∑ j, ((b j) • Pi.single (⟨j.val.val, by have := j.val.isLt; omega⟩ : Fin (2*n+2)) (1 : ℝ) -
    (2*b j) • Pi.single (⟨2*j.val.val+2, by have := j.val.isLt; omega⟩ : Fin (2*n+2)) (1 : ℝ))

theorem dyadicPacketCoefficients_synthesis (n : ℕ) (b : OddTailIndex n → ℝ) :
    Fintype.linearCombination ℝ (fun i : Fin (2*n+2) => tailAtom i.val)
      (dyadicPacketCoefficients n b) = dyadicPacketCombination n b := by
  unfold dyadicPacketCoefficients dyadicPacketCombination
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_sub, map_smul]
  simp [Fintype.linearCombination_apply, dyadicTailPacket, smul_sub, smul_smul, mul_comm]

theorem dyadicPacketCoefficients_moment (n : ℕ) (b : OddTailIndex n → ℝ) :
    (∑ i : Fin (2*n+2), if 2 ∣ i.val+2 then 0 else
      dyadicPacketCoefficients n b i / ((i.val+2 : ℕ) : ℝ)^2) =
      ∑ j, b j / ((j.val.val+2 : ℕ) : ℝ)^2 := by
  classical
  unfold dyadicPacketCoefficients
  simp only [Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.sum_div]
  have hsplit (p : Prop) [Decidable p] (f : OddTailIndex n → ℝ) :
      (if p then 0 else ∑ j, f j) = ∑ j, if p then 0 else f j := by
    split_ifs <;> simp
  simp_rw [hsplit]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have he : 2 ∣ (2*j.val.val+2)+2 := by omega
  have ho := j.property
  simp only [sub_div, mul_div_assoc]
  have hsub (p : Prop) [Decidable p] (x y : ℝ) :
      (if p then 0 else x-y) = (if p then 0 else x) - (if p then 0 else y) := by
    split_ifs <;> simp
  simp_rw [hsub]
  rw [Finset.sum_sub_distrib]
  have hsingle (a : Fin (2*n+2)) (r : ℝ) :
      (∑ i : Fin (2*n+2), if 2 ∣ i.val+2 then (0 : ℝ) else
        r * ((Pi.single a (1 : ℝ) : Fin (2*n+2) → ℝ) i / ((i.val+2 : ℕ) : ℝ)^2)) =
      if 2 ∣ a.val+2 then 0 else r / ((a.val+2 : ℕ) : ℝ)^2 := by
    rw [Finset.sum_eq_single a]
    · simp [div_eq_mul_inv]
    · intro i _ hia
      simp [Pi.single_apply, hia]
    · simp
  rw [hsingle, hsingle, if_neg ho, if_pos he, sub_zero]

theorem dyadicPacketCombination_zero_head_of_support (n N : ℕ)
    (b : OddTailIndex n → ℝ)
    (hsupp : ∀ i, b i ≠ 0 → N < i.val.val+2) (j : ℕ) (hj : j ≤ N) :
    hilbertSequence (dyadicPacketCombination n b) j = 0 := by
  change hilbertSequenceLinear (∑ i, b i • dyadicTailPacket i.val.val) j = 0
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : b i = 0
  · simp [hi]
  · change b i * hilbertSequence (dyadicTailPacket i.val.val) j = 0
    rw [dyadicTailPacket_zero_head i.val.val j (lt_of_le_of_lt hj (hsupp i hi)), mul_zero]

theorem dyadicPacketCombination_head_energy_lower (n N : ℕ)
    (b : OddTailIndex n → ℝ)
    (hm : (∑ j, b j / ((j.val.val+2 : ℕ) : ℝ)^2) = 1)
    (hsupp : ∀ i, b i ≠ 0 → N < i.val.val+2) :
    3 * ((N : ℝ)+1)^3 * ‖riemannZeta 2‖^2 / 16 ≤
      ‖dyadicPacketCombination n b‖^2 := by
  have h := paretoMellin_zero_head_norm_sq_le
    (N := N) (f := dyadicPacketCombination n b)
    (fun j _ hj => dyadicPacketCombination_zero_head_of_support n N b hsupp j hj)
    2 (by norm_num)
  rw [dyadicPacketCombination_mellin_two, hm] at h
  norm_num [norm_div, norm_neg, Real.rpow_neg, Real.rpow_natCast] at h
  have hp : 0 < ((N : ℝ)+1)^3 := by positivity
  have hh := mul_le_mul_of_nonneg_right h hp.le
  field_simp at hh
  nlinarith

/-- A second even correction cancels the fixed s=2 Mellin obstruction. -/
def mellinRepairedPacket (k : ℕ) : ThresholdHilbert :=
  dyadicTailPacket k - (4 : ℝ) • dyadicTailPacket (2*k+2)

theorem mellinRepairedPacket_residues (k : ℕ) :
    mellinRepairedPacket k = residueAtom k -
      (6 : ℝ) • residueAtom (2*k+2) +
      (8 : ℝ) • residueAtom (4*k+6) := by
  unfold mellinRepairedPacket
  rw [dyadicTailPacket_eq_residues, dyadicTailPacket_eq_residues]
  rw [show 2*(2*k+2)+2 = 4*k+6 by omega]
  module

theorem mellinRepairedPacket_zero_head (k j : ℕ) (hj : j < k+2) :
    hilbertSequence (mellinRepairedPacket k) j = 0 := by
  change hilbertSequenceLinear
    (dyadicTailPacket k - (4 : ℝ) • dyadicTailPacket (2*k+2)) j = 0
  rw [map_sub, map_smul]
  change hilbertSequence (dyadicTailPacket k) j -
    4 * hilbertSequence (dyadicTailPacket (2*k+2)) j = 0
  rw [dyadicTailPacket_zero_head k j hj,
    dyadicTailPacket_zero_head (2*k+2) j (by omega)]
  ring

theorem mellinRepairedPacket_mellin_two (k : ℕ) :
    paretoMellin (mellinRepairedPacket k) 2 = 0 := by
  change paretoMellinContinuous 2 (by norm_num)
    (dyadicTailPacket k - (4 : ℝ) • dyadicTailPacket (2*k+2)) = 0
  rw [map_sub, map_smul]
  change paretoMellin (dyadicTailPacket k) 2 -
    (4 : ℂ) * paretoMellin (dyadicTailPacket (2*k+2)) 2 = 0
  rw [dyadicTailPacket_mellin_two, dyadicTailPacket_mellin_two]
  push_cast
  rw [show (2 : ℂ) * k + 2 + 2 = 2 * ((k : ℂ)+2) by ring]
  field_simp
  <;> ring

theorem mellinRepairedPacket_combination_mellin_two (n : ℕ)
    (b : OddTailIndex n → ℝ) :
    paretoMellin (∑ j, b j • mellinRepairedPacket j.val.val) 2 = 0 := by
  change paretoMellinContinuous 2 (by norm_num)
    (∑ j, b j • mellinRepairedPacket j.val.val) = 0
  simp only [map_sum, map_smul]
  change (∑ j, (b j : ℂ) * paretoMellin (mellinRepairedPacket j.val.val) 2) = 0
  simp only [mellinRepairedPacket_mellin_two, mul_zero, Finset.sum_const_zero]

theorem mellinRepairedPacket_odd_moment (k : ℕ) (hk : ¬ 2 ∣ k+2) :
    (if 2 ∣ k+2 then (0 : ℝ) else 1 / ((k+2 : ℕ) : ℝ)^2) +
    (if 2 ∣ 2*k+2+2 then (0 : ℝ) else -6 / ((2*k+2+2 : ℕ) : ℝ)^2) +
    (if 2 ∣ 4*k+6+2 then (0 : ℝ) else 8 / ((4*k+6+2 : ℕ) : ℝ)^2) =
      1 / ((k+2 : ℕ) : ℝ)^2 := by
  have h₂ : 2 ∣ 2*k+2+2 := by omega
  have h₄ : 2 ∣ 4*k+6+2 := by omega
  simp only [if_neg hk, if_pos h₂, if_pos h₄, add_zero]

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
