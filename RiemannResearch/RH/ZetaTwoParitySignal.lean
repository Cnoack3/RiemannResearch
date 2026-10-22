import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual inverse-square parity signal

Source: user-provided `Final_Limit_Unit_Signal_Residues_2026-10-11 (1).md`,
Sections 1--2, for the parity signal and inverse-square law.

The definitions below use the existing
`QHilbert`, `qOne`, `qResidue`, and their complete inverse-square weighted
coordinate formulas. The multiples calculation reindexes the complete real
series; no finite truncation or covariance approximation is used.

The results identify the parity target and its norm and show that conductor 3
detects it nontrivially. They do not prove convergence of the optimized residue
approximants or any new implication discharging an RH-strength hypothesis.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.ZetaTwoParitySignal

open RiemannResearch.RH.ZetaTwoProbability
open RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.RH.ArithmeticCumulative

/-- Scaling the physical inverse-square weights, including the zero coordinate. -/
theorem positiveQWeight_mul (m k : ℕ) :
    positiveQWeight (m * k) = (1 / (m : ℝ) ^ 2) * positiveQWeight k := by
  simp only [positiveQWeight, Nat.cast_mul, mul_pow, one_div, mul_inv_rev]
  ring

/-- The real Hilbert weight of the multiples of a positive integer is 1/m². -/
theorem positiveQWeight_dvd_tsum (m : ℕ) (hm : 0 < m) :
    (∑' k : ℕ, if m ∣ k then positiveQWeight k else 0) = 1 / (m : ℝ) ^ 2 := by
  classical
  have hreindex :
      (∑' k : ℕ, if m ∣ k then positiveQWeight k else 0) =
        ∑' k : ℕ, positiveQWeight (m * k) := by
    apply tsum_eq_tsum_of_ne_zero_bij
      (fun k : Function.support (fun j : ℕ => positiveQWeight (m * j)) => m * k.val)
    · intro a b hab
      apply Subtype.ext
      exact Nat.eq_of_mul_eq_mul_left hm hab
    · intro k hk
      change (if m ∣ k then positiveQWeight k else 0) ≠ 0 at hk
      have hd : m ∣ k := by
        by_contra hnot
        apply hk
        exact if_neg hnot
      obtain ⟨a, ha⟩ := hd
      refine ⟨⟨a, ?_⟩, ha.symm⟩
      change positiveQWeight (m * a) ≠ 0
      rw [← ha]
      simpa only [if_pos (show m ∣ k from ⟨a, ha⟩)] using hk
    · intro k
      exact if_pos (dvd_mul_right m k.val)
  rw [hreindex]
  simp_rw [positiveQWeight_mul]
  rw [tsum_mul_left, positiveQWeight_tsum, mul_one]

/-- The legal odd-integer indicator, including the required zero extension. -/
def qOdd : QHilbert := (2 : ℝ) • qResidue 2

/-- The positive-even-integer indicator in the actual inverse-square Hilbert space. -/
def qEven : QHilbert := qOne - qOdd

theorem qSequence_qOdd_mod :
    qSequence qOdd = fun k : ℕ => ((k % 2 : ℕ) : ℝ) := by
  change qSequenceLinear ((2 : ℝ) • qResidue 2) = _
  rw [map_smul]
  funext k
  change (2 : ℝ) * qSequence (qResidue 2) k = _
  rw [qSequence_qResidue]
  change (2 : ℝ) * (((k % 2 : ℕ) : ℝ) / 2) = _
  ring

theorem qSequence_qOdd (k : ℕ) :
    qSequence qOdd k = if 2 ∣ k then 0 else 1 := by
  rw [qSequence_qOdd_mod]
  by_cases hd : 2 ∣ k
  · simp [hd, Nat.mod_eq_zero_of_dvd hd]
  · have hmod : k % 2 = 1 :=
      (Nat.mod_two_eq_zero_or_one k).resolve_left
        (fun hz => hd (Nat.dvd_of_mod_eq_zero hz))
    simp [hd, hmod]

theorem qSequence_qEven (k : ℕ) :
    qSequence qEven k = if k = 0 then 0 else if 2 ∣ k then 1 else 0 := by
  change qSequenceLinear (qOne - qOdd) k = _
  rw [map_sub]
  change qSequence qOne k - qSequence qOdd k = _
  rw [qSequence_qOne, qSequence_qOdd]
  by_cases hk : k = 0
  · subst k
    norm_num [qOneSequence]
  · by_cases hd : 2 ∣ k <;> simp [qOneSequence, hk, hd]

@[simp] theorem qEven_at_one : qSequence qEven 1 = 0 := by
  rw [qSequence_qEven]
  norm_num

@[simp] theorem qEven_at_two : qSequence qEven 2 = 1 := by
  rw [qSequence_qEven]
  norm_num

/-- The exact unconditional target mass is 1/4 for the inverse-square law. -/
theorem qEven_norm_sq : ‖qEven‖ ^ 2 = (1 / 4 : ℝ) := by
  rw [qNorm_weighted_sq]
  have he :
      (fun k => positiveQWeight k * (qSequence qEven k) ^ 2) =
        fun k => if 2 ∣ k then positiveQWeight k else 0 := by
    funext k
    rw [qSequence_qEven]
    by_cases hk : k = 0
    · subst k
      simp [positiveQWeight]
    · by_cases hd : 2 ∣ k <;> simp [hk, hd]
  rw [he, positiveQWeight_dvd_tsum 2 (by norm_num)]
  norm_num

theorem qEven_inner_self : inner ℝ qEven qEven = (1 / 4 : ℝ) := by
  rw [real_inner_self_eq_norm_sq, qEven_norm_sq]

/-- The actual even and odd indicators are orthogonal, with the full tail included. -/
theorem qEven_inner_qOdd : inner ℝ qEven qOdd = 0 := by
  rw [qInner_weighted]
  calc
    (∑' k : ℕ, positiveQWeight k * qSequence qEven k * qSequence qOdd k) =
        ∑' _k : ℕ, (0 : ℝ) := by
      apply tsum_congr
      intro k
      rw [qSequence_qEven, qSequence_qOdd]
      by_cases hd : 2 ∣ k <;> simp [hd]
    _ = 0 := by simp

theorem qOdd_inner_qEven : inner ℝ qOdd qEven = 0 := by
  rw [real_inner_comm, qEven_inner_qOdd]

theorem qEven_add_qOdd : qEven + qOdd = qOne := by
  exact sub_add_cancel qOne qOdd

theorem qEven_inner_qOne : inner ℝ qEven qOne = (1 / 4 : ℝ) := by
  rw [← qEven_add_qOdd, inner_add_right, qEven_inner_self, qEven_inner_qOdd, add_zero]

theorem qOdd_norm_sq : ‖qOdd‖ ^ 2 = (3 / 4 : ℝ) := by
  have hsum : inner ℝ (qEven + qOdd) (qEven + qOdd) = 1 := by
    rw [qEven_add_qOdd, real_inner_self_eq_norm_sq, qOne_norm_sq]
  simp only [inner_add_left, inner_add_right, qEven_inner_qOdd,
    qOdd_inner_qEven, zero_add, add_zero, real_inner_self_eq_norm_sq] at hsum
  linarith [qEven_norm_sq]

/-- Conductor 3 detects the actual target because the full nonnegative pairing
has a strictly positive contribution at physical coordinate 2. -/
theorem qEven_inner_qResidue_three_pos : 0 < inner ℝ qEven (qResidue 3) := by
  rw [qInner_weighted]
  refine (qSequence_product_summable qEven (qResidue 3)).tsum_pos ?_ 2 ?_
  · intro k
    rw [qSequence_qEven, qSequence_qResidue]
    have hw := positiveQWeight_nonneg k
    unfold residueFraction
    split_ifs <;> positivity
  · rw [qEven_at_two, qSequence_qResidue]
    have hw : 0 < positiveQWeight 2 := by
      have hZ := zetaTwo_pos
      unfold positiveQWeight
      positivity
    have hr : 0 < residueFraction 3 2 := by
      norm_num [residueFraction]
    exact mul_pos (mul_pos hw zero_lt_one) hr

/-- Any legal subspace containing conductor 2 contains the constant exactly when
it contains the even target. No closure or RH theorem is assumed here. -/
theorem qOne_mem_iff_qEven_mem (S : Submodule ℝ QHilbert)
    (h2 : qResidue 2 ∈ S) : qOne ∈ S ↔ qEven ∈ S := by
  constructor
  · intro hOne
    exact S.sub_mem hOne (S.smul_mem (2 : ℝ) h2)
  · intro hEven
    rw [← qEven_add_qOdd]
    exact S.add_mem hEven (S.smul_mem (2 : ℝ) h2)

end RiemannResearch.RH.ZetaTwoParitySignal
