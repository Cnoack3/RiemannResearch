/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QLegalMixedConductorMoments
import RiemannResearch.RH.QConductorDecay
import RiemannResearch.RH.QFiniteEnergyBounds
import Lean.Elab.Tactic.Omega

/-!
# Actual Gram and target-moment asymptotics of the mixed-conductor family

Source: LegalSubspaceProjectionObstruction.md. The argument improves the
paper's norm upper estimate using the previously verified bound 2/(zetaTwo*d).
Every eventual inequality follows from full Q arithmetic conductor estimates;
none is an assumed projection-stability provider.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QLegalMixedConductor
open ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal

def fixedParityCoefficient : ℝ := inner ℝ (qResidue 3) parityAtom / ‖parityAtom‖ ^ 2
def fixedOrthogonalVector : QHilbert := qResidue 3 - fixedParityCoefficient • parityAtom

theorem highPart_eq (d : ℕ) : highPart d = (10 : ℝ) • normalizedConductor d := by
  simp only [highPart, normalizedConductor, smul_smul]

theorem highPart_norm_sq_le (d : ℕ) (hd : 2 ≤ d) : ‖highPart d‖ ^ 2 ≤ 200 := by
  have hz : 1 < zetaTwo := by linarith [QFiniteEnergyBounds.zetaTwo_rational_bounds.1]
  have h := normalizedConductor_norm_sq_le d hd
  have hz' : 2 / zetaTwo ≤ 2 := (div_le_iff₀ zetaTwo_pos).mpr (by linarith)
  rw [highPart_eq, norm_smul, Real.norm_eq_abs, mul_pow]
  norm_num
  nlinarith

theorem highPart_norm_sq_ge (d : ℕ) (hd : 2 ≤ d) : 30 ≤ ‖highPart d‖ ^ 2 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have h := mul_le_mul_of_nonneg_left
    (qResidue_norm_sq_ge_half_div d hd) (show 0 ≤ (100 : ℝ) * d by positivity)
  have he : 100 * (d : ℝ) * (1 / (2 * zetaTwo * d)) = 50 / zetaTwo := by
    field_simp [hd'.ne', zetaTwo_pos.ne']; ring
  rw [he] at h
  have hz : 30 ≤ 50 / zetaTwo := (le_div_iff₀ zetaTwo_pos).mpr (by
    linarith [QFiniteEnergyBounds.zetaTwo_rational_bounds.2])
  rw [highPart, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  norm_num
  exact hz.trans h

theorem qResidue_three_norm_le : ‖qResidue 3‖ ≤ 2 / 3 := by
  have h := qResidue_norm_sq_le_two_div 3 (by norm_num)
  have hz : 2 / (zetaTwo * 3) ≤ (2 / 3 : ℝ) ^ 2 :=
    (div_le_iff₀ (mul_pos zetaTwo_pos (by norm_num))).mpr (by
      linarith [QFiniteEnergyBounds.zetaTwo_rational_bounds.1])
  norm_num at h
  nlinarith [norm_nonneg (qResidue 3)]

theorem fixedOrthogonalVector_norm_sq :
    ‖fixedOrthogonalVector‖ ^ 2 = ‖qResidue 3‖ ^ 2 -
      fixedParityCoefficient ^ 2 * ‖parityAtom‖ ^ 2 := by
  have hc : fixedParityCoefficient * ‖parityAtom‖ ^ 2 =
      inner ℝ (qResidue 3) parityAtom := by
    unfold fixedParityCoefficient
    rw [div_mul_cancel₀ _ (by rw [parityAtom_norm_sq]; norm_num)]
  rw [fixedOrthogonalVector, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_smul_right]
  rw [← hc]
  ring

theorem fixedOrthogonalVector_norm_sq_le : ‖fixedOrthogonalVector‖ ^ 2 ≤ 4 / 9 := by
  rw [fixedOrthogonalVector_norm_sq]
  have h := qResidue_three_norm_le
  have hn : 0 ≤ fixedParityCoefficient ^ 2 * ‖parityAtom‖ ^ 2 := by positivity
  nlinarith [norm_nonneg (qResidue 3)]

theorem highPart_inner_tendsto_zero (f : QHilbert) (C : ℝ)
    (hf : ∀ n, |qSequence f n| ≤ C) :
    Tendsto (fun d => inner ℝ f (highPart d)) atTop (𝓝 0) := by
  simpa only [highPart_eq, real_inner_smul_right, mul_zero] using
    (normalizedConductor_inner_tendsto_zero f C hf).const_mul 10

theorem parityCoefficient_tendsto :
    Tendsto parityCoefficient atTop (𝓝 fixedParityCoefficient) := by
  have h := (highPart_inner_tendsto_zero parityAtom 1
    (qResidue_physical_abs_le_one 2)).add_const (inner ℝ (qResidue 3) parityAtom)
  have h' := h.div_const (‖parityAtom‖ ^ 2)
  convert h' using 1
  · funext d
    simp only [parityCoefficient, mixedVector, inner_add_left]
    rw [real_inner_comm (highPart d) parityAtom]
    ring
  · simp [fixedParityCoefficient]

theorem gram_sub_highPart_norm_sq (d : ℕ) :
    gram d - ‖highPart d‖ ^ 2 = ‖qResidue 3‖ ^ 2 +
      2 * inner ℝ (qResidue 3) (highPart d) -
      parityCoefficient d ^ 2 * ‖parityAtom‖ ^ 2 := by
  have hc : parityCoefficient d * ‖parityAtom‖ ^ 2 =
      inner ℝ (mixedVector d) parityAtom := by
    unfold parityCoefficient
    rw [div_mul_cancel₀ _ (by rw [parityAtom_norm_sq]; norm_num)]
  unfold gram orthogonalVector
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_smul_right]
  rw [← hc]
  rw [mixedVector, norm_add_sq_real]
  ring

theorem gram_sub_highPart_norm_sq_tendsto :
    Tendsto (fun d => gram d - ‖highPart d‖ ^ 2) atTop
      (𝓝 (‖fixedOrthogonalVector‖ ^ 2)) := by
  have hg := highPart_inner_tendsto_zero (qResidue 3) 1
    (qResidue_physical_abs_le_one 3)
  have h := ((hg.const_mul 2).const_add (‖qResidue 3‖ ^ 2)).sub
    ((parityCoefficient_tendsto.pow 2).mul_const (‖parityAtom‖ ^ 2))
  simpa only [gram_sub_highPart_norm_sq, mul_zero, add_zero,
    fixedOrthogonalVector_norm_sq] using h

theorem gram_bounds_eventually : ∀ᶠ d in atTop, 25 ≤ gram d ∧ gram d ≤ 303 := by
  have hlo := gram_sub_highPart_norm_sq_tendsto.eventually
    (lt_mem_nhds (show (-1 : ℝ) < ‖fixedOrthogonalVector‖ ^ 2 by
      linarith [sq_nonneg ‖fixedOrthogonalVector‖]))
  have hhi := gram_sub_highPart_norm_sq_tendsto.eventually
    (gt_mem_nhds (show ‖fixedOrthogonalVector‖ ^ 2 < 1 by
      linarith [fixedOrthogonalVector_norm_sq_le]))
  filter_upwards [eventually_ge_atTop (2 : ℕ), hlo, hhi] with d hd hlo hhi
  have hl := highPart_norm_sq_ge d hd
  have hu := highPart_norm_sq_le d hd
  constructor <;> linarith

theorem targetMoment_tendsto :
    Tendsto targetMoment atTop (𝓝 (inner ℝ evenTarget (qResidue 3))) := by
  have h := highPart_inner_tendsto_zero evenTarget 1 (by
    intro n
    rw [QDivisibilityDensity.qSequence_qDivisor]
    exact QDivisibilityDensity.positiveDivisor_abs_le_one 2 n)
  have he (d : ℕ) : targetMoment d = inner ℝ evenTarget (qResidue 3) +
      inner ℝ evenTarget (highPart d) := by
    rw [targetMoment_eq, highPart, real_inner_smul_right]
  change Tendsto (fun d => targetMoment d) atTop (𝓝 (inner ℝ evenTarget (qResidue 3)))
  simpa only [he, add_zero] using h.const_add (inner ℝ evenTarget (qResidue 3))

theorem targetMoment_upper_eventually : ∀ᶠ d in atTop, targetMoment d ≤ 1 / 2 := by
  have hj : ‖evenTarget‖ ≤ 1 / 2 := by
    nlinarith [evenTarget_norm_sq, norm_nonneg evenTarget]
  have hi := real_inner_le_norm evenTarget (qResidue 3)
  have hbound : inner ℝ evenTarget (qResidue 3) < 1 / 2 := by
    have hm := mul_le_mul hj qResidue_three_norm_le (norm_nonneg (qResidue 3))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  exact (targetMoment_tendsto.eventually (gt_mem_nhds hbound)).mono (fun _ h => h.le)

end RiemannResearch.RH.QLegalMixedConductor
