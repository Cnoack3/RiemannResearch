/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QConductorLimits
import RiemannResearch.RH.QConductorEscape
import RiemannResearch.RH.QDivisibilityHilbertMoments
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QDivisorLegality
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Reflected-vector obstruction for escaping conductor packets

Source: the user-requested finite-stage reflected-vector investigation,
17 October 2026. The two-site completed-square argument is developed here.
The full Q norm, rather than a truncated substitute, appears in the bound.
No RH assumption and no bound on coefficient sizes or support cardinality
is used.
-/

noncomputable section
namespace RiemannResearch.RH.QReflectedFiniteStage
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity ArithmeticCumulative

/-- The exact physical reflected head before the first wrap. -/
theorem qReflected_short_head (d n : ℕ) (hn : 0 < n) (hnd : n < d) :
    qSequence (qReflected d) n = 1 - (n : ℝ) / (d : ℝ) := by
  rw [qReflected_sequence]
  simp [qOneSequence, residueFraction, positiveDivisor,
    Nat.ne_of_gt hn, Nat.mod_eq_of_lt hnd,
    Nat.not_dvd_of_pos_of_lt hn hnd]

/-- The first two physical sites are bounded by the complete infinite norm. -/
theorem twoSite_energy_le (f : QHilbert) :
    positiveQWeight 1 * (qSequence f 1) ^ 2 +
      positiveQWeight 2 * (qSequence f 2) ^ 2 ≤ ‖f‖ ^ 2 := by
  rw [qNorm_weighted_sq]
  have h := (qSequence_square_summable f).sum_le_tsum ({1, 2} : Finset ℕ)
    (fun k _ => mul_nonneg (positiveQWeight_nonneg k) (sq_nonneg _))
  simpa using h

/-- Exact two-site error with the old conductor-two coefficient retained.
The separate comparison theorem below retains the complete infinite norm. -/
theorem reflected_twoSite_energy_exact (d : ℕ) (hd : 3 ≤ d)
    (F : QHilbert) (c : ℝ)
    (hhead : qSequence F 2 = 2 * qSequence F 1 - c) :
    positiveQWeight 1 * (qSequence (qReflected d - F) 1) ^ 2 +
      positiveQWeight 2 * (qSequence (qReflected d - F) 2) ^ 2 =
    (c - 1) ^ 2 / (8 * zetaTwo) +
      (2 / zetaTwo) *
        (1 - 1 / (d : ℝ) - qSequence F 1 + (c - 1) / 4) ^ 2 := by
  have hsub (k : ℕ) :
      qSequence (qReflected d - F) k =
        qSequence (qReflected d) k - qSequence F k :=
    congrFun (qSequenceLinear.map_sub (qReflected d) F) k
  rw [hsub 1, hsub 2,
    qReflected_short_head d 1 (by decide) (by omega),
    qReflected_short_head d 2 (by decide) (by omega), hhead]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  norm_num only [positiveQWeight, Nat.cast_ofNat, Nat.cast_one, one_pow, mul_one]
  field_simp [ne_of_gt zetaTwo_pos, hdR]
  ring

/-- A quantitative necessary conductor-two coefficient condition. -/
theorem reflected_error_sq_ge_coefficient (d : ℕ) (hd : 3 ≤ d)
    (F : QHilbert) (c : ℝ)
    (hhead : qSequence F 2 = 2 * qSequence F 1 - c) :
    (c - 1) ^ 2 / (8 * zetaTwo) ≤ ‖qReflected d - F‖ ^ 2 := by
  have h := twoSite_energy_le (qReflected d - F)
  rw [reflected_twoSite_energy_exact d hd F c hhead] at h
  have hp : 0 ≤ (2 / zetaTwo) *
      (1 - 1 / (d : ℝ) - qSequence F 1 + (c - 1) / 4) ^ 2 :=
    mul_nonneg (div_nonneg (by norm_num) zetaTwo_pos.le) (sq_nonneg _)
  linarith

/-- Every packet using only conductors at least three has a fixed positive
complete Q-error against every reflected target of conductor at least three.
Coefficient signs, coefficient sizes, and support size are unrestricted. -/
theorem reflected_error_sq_ge_of_tailSpan (d : ℕ) (hd : 3 ≤ d)
    (F : QHilbert) (hF : F ∈ qConductorTailSpan 2) :
    1 / (8 * zetaTwo) ≤ ‖qReflected d - F‖ ^ 2 := by
  have hhead : qSequence F 2 = 2 * qSequence F 1 - (0 : ℝ) := by
    simpa using qConductorTailSpan_head 2 (by decide) F hF 2 (by decide)
  simpa using reflected_error_sq_ge_coefficient d hd F 0 hhead

/-- Every vector in the divisor stage vanishes on the d progression. -/
theorem divisorStage_inner_qDivisor_zero (d : ℕ) (hd : 0 < d)
    (F : QHilbert) (hF : F ∈ QSquarefreeLatticePackets.divisorStage d) :
    inner ℝ F (qDivisor d) = 0 := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
      obtain ⟨a, ha, rfl⟩ := hF
      exact qResidue_inner_qDivisor_eq_zero a d hd ha
  | zero => simp
  | add F G hF hG ihF ihG => rw [inner_add_left, ihF, ihG, add_zero]
  | smul c F hF ih => rw [real_inner_smul_left, ih, mul_zero]

/-- Exact complete reflected trial energy. No signed term or tail is omitted. -/
theorem reflected_shift_energy_exact (d : ℕ) (F : QHilbert) :
    ‖qReflected d - (F - qResidue d)‖ ^ 2 =
      ‖qOne - F‖ ^ 2 + ‖qDivisor d‖ ^ 2 -
        2 * inner ℝ (qOne - F) (qDivisor d) := by
  have hv : qReflected d - (F - qResidue d) = qOne - F - qDivisor d := by
    unfold qReflected
    abel
  rw [hv, norm_sub_sq_real]
  ring

/-- On a conductor's own divisor stage, reflection improves the full error
by exactly d^(-2), without any unproved asymptotic energy premise. -/
theorem reflected_divisorStage_energy_exact (d : ℕ) (hd : 0 < d)
    (F : QHilbert) (hF : F ∈ QSquarefreeLatticePackets.divisorStage d) :
    ‖qReflected d - (F - qResidue d)‖ ^ 2 =
      ‖qOne - F‖ ^ 2 - 1 / (d : ℝ) ^ 2 := by
  rw [reflected_shift_energy_exact, qDivisor_norm_sq d hd, inner_sub_left,
    qOne_inner_qDivisor d hd, divisorStage_inner_qDivisor_zero d hd F hF]
  ring

/-- The shifted vector remains in the original finite divisor stage. -/
theorem reflected_divisorStage_trial_mem (d : ℕ) (F : QHilbert)
    (hF : F ∈ QSquarefreeLatticePackets.divisorStage d) :
    F - qResidue d ∈ QSquarefreeLatticePackets.divisorStage d :=
  (QSquarefreeLatticePackets.divisorStage d).sub_mem hF
    (Submodule.subset_span ⟨d, dvd_refl d, rfl⟩)

def binaryTrial (d : ℕ) : QHilbert := (2 : ℝ) • qResidue 2 - qResidue d

/-- A completely explicit legal reflected trial for every squarefree d >= 2. -/
theorem binaryTrial_mem (d : ℕ) (hd : 2 ≤ d) (hsf : Squarefree d) :
    binaryTrial d ∈ qSquarefreeCRTSpan := by
  exact qSquarefreeCRTSpan.sub_mem
    (qSquarefreeCRTSpan.smul_mem 2
      (Submodule.subset_span ⟨⟨2, by decide, Nat.prime_two.squarefree⟩, rfl⟩))
    (Submodule.subset_span ⟨⟨d, hd, hsf⟩, rfl⟩)

/-- An explicit upper-bound certificate with the exact overlap/carry term. -/
theorem binaryTrial_energy_exact (d : ℕ) (hd : 0 < d) :
    ‖qReflected d - binaryTrial d‖ ^ 2 =
      1 / 4 + 1 / (d : ℝ) ^ 2 - 2 / (Nat.lcm 2 d : ℝ) ^ 2 := by
  have hv : qReflected d - binaryTrial d = qDivisor 2 - qDivisor d := by
    rw [QDivisorLegality.qDivisor_two_eq]
    unfold qReflected binaryTrial
    abel
  rw [hv, norm_sub_sq_real, qDivisor_norm_sq 2 (by decide),
    qDivisor_norm_sq d hd, qDivisor_inner_qDivisor 2 d (by decide) hd]
  norm_num
  ring

end RiemannResearch.RH.QReflectedFiniteStage
