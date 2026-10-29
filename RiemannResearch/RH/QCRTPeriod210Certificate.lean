/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.NumberTheory.Primorial
import RiemannResearch.RH.QCRTMinimumEnergy
import RiemannResearch.RH.QFiniteEnergyBounds
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QSquarefreeLatticePackets
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Data.Rat.Cast.Order
import Lean.Elab.Tactic.Omega

/-!
# A signed exact-head certificate at period 210

Source: the user-provided minimum-energy exact-head research agenda,
28 October 2026, priorities 1 and 3. Finite-stage coefficient exploration
suggested the explicit signed vector below. Its complete energy bound
uses an exact rational head sum and a bound for the entire infinite tail.
This is a finite benchmark, not a cofinal energy bound or RH conclusion.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTPeriod210Certificate
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open QSquarefreeLatticePackets QCRTMinimumEnergy QFiniteEnergyBounds

def certificate : QHilbert :=
  qResidue 2 + qResidue 3 + qResidue 5 - qResidue 6 + (2 : ℝ) • qResidue 7 -
    qResidue 14 - qResidue 21 - qResidue 30

def rationalValue (n : ℕ) : ℚ :=
  ((n % 2 : ℕ) : ℚ) / 2 + ((n % 3 : ℕ) : ℚ) / 3 +
    ((n % 5 : ℕ) : ℚ) / 5 - ((n % 6 : ℕ) : ℚ) / 6 +
    2 * (((n % 7 : ℕ) : ℚ) / 7) - ((n % 14 : ℕ) : ℚ) / 14 -
    ((n % 21 : ℕ) : ℚ) / 21 - ((n % 30 : ℕ) : ℚ) / 30

theorem certificate_sequence (n : ℕ) :
    qSequence certificate n = (rationalValue n : ℝ) := by
  change qSequenceLinear
    (qResidue 2 + qResidue 3 + qResidue 5 - qResidue 6 + (2 : ℝ) • qResidue 7 -
      qResidue 14 - qResidue 21 - qResidue 30) n = _
  simp only [map_sub, map_add, map_smul, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  change qSequence (qResidue 2) n + qSequence (qResidue 3) n +
    qSequence (qResidue 5) n - qSequence (qResidue 6) n +
    2 * qSequence (qResidue 7) n - qSequence (qResidue 14) n -
    qSequence (qResidue 21) n - qSequence (qResidue 30) n = _
  simp [qSequence_qResidue, residueFraction, rationalValue]

theorem rationalValue_period (n : ℕ) : rationalValue (n % 210) = rationalValue n := by
  have h2 : (n % 210) % 2 = n % 2 := by omega
  have h3 : (n % 210) % 3 = n % 3 := by omega
  have h5 : (n % 210) % 5 = n % 5 := by omega
  have h6 : (n % 210) % 6 = n % 6 := by omega
  have h7 : (n % 210) % 7 = n % 7 := by omega
  have h14 : (n % 210) % 14 = n % 14 := by omega
  have h21 : (n % 210) % 21 = n % 21 := by omega
  have h30 : (n % 210) % 30 = n % 30 := by omega
  simp only [rationalValue, h2, h3, h5, h6, h7, h14, h21, h30]

set_option maxRecDepth 100000 in
theorem rationalValue_ternary_finite : ∀ n : Fin 210,
    rationalValue n = -1 ∨ rationalValue n = 0 ∨ rationalValue n = 1 := by
  decide +kernel

theorem certificate_ternary (n : ℕ) :
    qSequence certificate n = -1 ∨ qSequence certificate n = 0 ∨
      qSequence certificate n = 1 := by
  have h := rationalValue_ternary_finite ⟨n % 210, Nat.mod_lt _ (by norm_num)⟩
  change rationalValue (n % 210) = -1 ∨ rationalValue (n % 210) = 0 ∨
    rationalValue (n % 210) = 1 at h
  simp only [rationalValue_period] at h
  simp only [certificate_sequence]
  rcases h with h | h | h
  · left; exact_mod_cast h
  · right; left; exact_mod_cast h
  · right; right; exact_mod_cast h

theorem certificate_abs_le_one (n : ℕ) : |qSequence certificate n| ≤ 1 := by
  rcases certificate_ternary n with h | h | h <;> norm_num [h]

theorem certificate_energy_le_one : ‖certificate‖^2 ≤ 1 := by
  rw [qNorm_weighted_sq, ← positiveQWeight_tsum]
  apply (qSequence_square_summable certificate).tsum_le_tsum _ positiveQWeight_summable
  intro n
  rcases certificate_ternary n with h | h | h
  · simp [h]
  · simpa only [h, zero_pow (by norm_num : 2 ≠ 0), mul_zero] using
      positiveQWeight_nonneg n
  · simp [h]

theorem certificate_exact_head (n : ℕ) (hn : 0 < n) (hH : n ≤ 6) :
    qSequence certificate n = 1 := by
  rw [certificate_sequence]
  interval_cases n <;> norm_num [rationalValue]

theorem certificate_at_half_period : qSequence certificate 105 = -1 := by
  rw [certificate_sequence]
  norm_num [rationalValue]

theorem certificate_at_half_period_add_four : qSequence certificate 109 = 1 := by
  rw [certificate_sequence]
  norm_num [rationalValue]

theorem certificate_mem_stage : certificate ∈ divisorStage 210 := by
  have hm (d : ℕ) (hd : d ∣ 210) : qResidue d ∈ divisorStage 210 :=
    Submodule.subset_span ⟨d, hd, rfl⟩
  exact (divisorStage 210).sub_mem
    ((divisorStage 210).sub_mem
      ((divisorStage 210).sub_mem
        ((divisorStage 210).add_mem
          ((divisorStage 210).sub_mem
            ((divisorStage 210).add_mem
              ((divisorStage 210).add_mem (hm 2 (by norm_num)) (hm 3 (by norm_num)))
              (hm 5 (by norm_num)))
            (hm 6 (by norm_num)))
          ((divisorStage 210).smul_mem _ (hm 7 (by norm_num))))
        (hm 14 (by norm_num)))
      (hm 21 (by norm_num)))
    (hm 30 (by norm_num))

theorem certificate_legal : certificate ∈ qSquarefreeCRTSpan := by
  have hp : primorial 7 = 210 := by decide +kernel
  have hsf : Squarefree 210 := by
    rw [← hp]
    exact squarefree_primorial 7
  exact divisorStage_le_squarefreeSpan 210 (by norm_num) hsf certificate_mem_stage

/-- Exact rational prefix plus the complete tail majorant B²/K. -/
def rationalBudget : ℚ :=
  (∑ n ∈ Finset.range 210, (rationalValue (n + 1)) ^ 2 / (n + 1 : ℚ) ^ 2) + 1 / 210

set_option maxRecDepth 100000 in
theorem rationalBudget_bound : (76 : ℚ) / 125 * rationalBudget < 47 / 50 := by
  decide +kernel

theorem rationalBudget_cast : (rationalBudget : ℝ) =
    (∑ n ∈ Finset.range 210, (qSequence certificate (n + 1)) ^ 2 / (n + 1 : ℝ) ^ 2) +
      (1 : ℝ) / 210 := by
  unfold rationalBudget
  push_cast
  simp only [certificate_sequence]

theorem certificate_energy_lt : ‖certificate‖^2 < (47 : ℝ) / 50 := by
  have hbudget : 0 ≤ (rationalBudget : ℝ) := by
    rw [rationalBudget_cast]
    positivity
  have ht := norm_sq_le_head_tail certificate 210 (by norm_num) 1
    (by norm_num) certificate_abs_le_one
  norm_num only [Nat.cast_ofNat] at ht
  rw [← rationalBudget_cast] at ht
  have hratio := mul_le_mul_of_nonneg_right inverse_zetaTwo_rational_bounds.2.le hbudget
  have hnum : (76 : ℝ) / 125 * (rationalBudget : ℝ) < 47 / 50 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr rationalBudget_bound
    push_cast at h
    exact h
  exact (ht.trans hratio).trans_lt hnum

theorem minimumEnergyApproximant_five_lt :
    ‖minimumEnergyApproximant 5‖^2 < (47 : ℝ) / 50 := by
  have hp : primorial (5 + 2) = 210 := by decide +kernel
  have hmem : certificate ∈ divisorStage (primorial (5 + 2)) := by
    simpa only [hp] using certificate_mem_stage
  have h := (minimumEnergyApproximant_isLeast 5).2
    ⟨certificate, hmem, certificate_exact_head, rfl⟩
  exact h.trans_lt certificate_energy_lt

end RiemannResearch.RH.QCRTPeriod210Certificate
