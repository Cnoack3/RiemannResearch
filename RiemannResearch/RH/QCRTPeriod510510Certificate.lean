/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFiniteEnergyBounds
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Cast.Order
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# A complete-energy certificate after inserting conductor 17

Source: the user-provided delayed-period CRT research task, 28 October 2026.
The rational candidate was found by signed full-Gram minimization and then
simplified. The proof below checks its actual exact head, bounds all physical
coordinates, rounds a finite prefix upwards, and includes the entire infinite
tail. It does not assert a bound for any cofinal family.
-/

noncomputable section
set_option maxRecDepth 100000
open scoped BigOperators
namespace RiemannResearch.RH.QCRTPeriod510510Certificate
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open QSquarefreeLatticePackets QFiniteEnergyBounds QCRTPeriodHeadBalance

def blockA (n : ℕ) : ℚ :=
  ((n % 2 : ℕ) : ℚ) / 2 + ((n % 3 : ℕ) : ℚ) / 3 + ((n % 5 : ℕ) : ℚ) / 5 -
    ((n % 6 : ℕ) : ℚ) / 6 - ((n % 10 : ℕ) : ℚ) / 10 - ((n % 15 : ℕ) : ℚ) / 15 +
    ((n % 30 : ℕ) : ℚ) / 30

def blockB (n : ℕ) : ℚ := ((n % 7 : ℕ) : ℚ) / 7 - ((n % 14 : ℕ) : ℚ) / 14

def blockC (n : ℕ) : ℚ := ((n % 11 : ℕ) : ℚ) / 11 + ((n % 13 : ℕ) : ℚ) / 13

def blockD (n : ℕ) : ℚ :=
  (29518 / 15015 : ℚ) * (((n % 17 : ℕ) : ℚ) / 17) -
    2 * (((n % 34 : ℕ) : ℚ) / 34) - (3 / 2 : ℚ) * (((n % 51 : ℕ) : ℚ) / 51)

def rationalValue (n : ℕ) : ℚ := blockA n + blockB n + blockC n + blockD n

def certificate : QHilbert :=
  (qResidue 2 + qResidue 3 + qResidue 5 - qResidue 6 - qResidue 10 -
    qResidue 15 + qResidue 30) + (qResidue 7 - qResidue 14) +
    (qResidue 11 + qResidue 13) +
    ((29518 / 15015 : ℝ) • qResidue 17 - (2 : ℝ) • qResidue 34 -
      (3 / 2 : ℝ) • qResidue 51)

theorem certificate_sequence (n : ℕ) :
    qSequence certificate n = (rationalValue n : ℝ) := by
  change qSequenceLinear
    ((qResidue 2 + qResidue 3 + qResidue 5 - qResidue 6 - qResidue 10 -
      qResidue 15 + qResidue 30) + (qResidue 7 - qResidue 14) +
      (qResidue 11 + qResidue 13) +
      ((29518 / 15015 : ℝ) • qResidue 17 - (2 : ℝ) • qResidue 34 -
        (3 / 2 : ℝ) • qResidue 51)) n = _
  simp only [map_sub, map_add, map_smul, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  change (qSequence (qResidue 2) n + qSequence (qResidue 3) n +
    qSequence (qResidue 5) n - qSequence (qResidue 6) n -
    qSequence (qResidue 10) n - qSequence (qResidue 15) n +
    qSequence (qResidue 30) n) +
    (qSequence (qResidue 7) n - qSequence (qResidue 14) n) +
    (qSequence (qResidue 11) n + qSequence (qResidue 13) n) +
    ((29518 / 15015 : ℝ) * qSequence (qResidue 17) n -
      2 * qSequence (qResidue 34) n -
      (3 / 2 : ℝ) * qSequence (qResidue 51) n) = _
  simp [qSequence_qResidue, residueFraction, rationalValue, blockA, blockB, blockC, blockD]

private theorem blockA_period (n : ℕ) : blockA (n % 30) = blockA n := by
  have h2 : n % 30 % 2 = n % 2 := by omega
  have h3 : n % 30 % 3 = n % 3 := by omega
  have h5 : n % 30 % 5 = n % 5 := by omega
  have h6 : n % 30 % 6 = n % 6 := by omega
  have h10 : n % 30 % 10 = n % 10 := by omega
  have h15 : n % 30 % 15 = n % 15 := by omega
  simp only [blockA, h2, h3, h5, h6, h10, h15, Nat.mod_mod]

private theorem blockB_period (n : ℕ) : blockB (n % 14) = blockB n := by
  have h7 : n % 14 % 7 = n % 7 := by omega
  simp only [blockB, h7, Nat.mod_mod]

private theorem blockD_period (n : ℕ) : blockD (n % 102) = blockD n := by
  have h17 : n % 102 % 17 = n % 17 := by omega
  have h34 : n % 102 % 34 = n % 34 := by omega
  have h51 : n % 102 % 51 = n % 51 := by omega
  simp only [blockD, h17, h34, h51]

set_option maxRecDepth 100000 in
private theorem blockA_finite : ∀ n : Fin 30,
    -(2 : ℚ) / 3 ≤ blockA n ∧ blockA n ≤ 14 / 15 := by decide +kernel

set_option maxRecDepth 100000 in
private theorem blockB_finite : ∀ n : Fin 14,
    -(1 : ℚ) / 2 ≤ blockB n ∧ blockB n ≤ 3 / 7 := by decide +kernel

set_option maxRecDepth 100000 in
private theorem blockD_finite : ∀ n : Fin 102,
    -(2 : ℚ) ≤ blockD n ∧ blockD n ≤ 6584 / 15015 := by decide +kernel

theorem rationalValue_abs_le_four (n : ℕ) : |rationalValue n| ≤ 4 := by
  have hA := blockA_finite ⟨n % 30, Nat.mod_lt _ (by norm_num)⟩
  have hB := blockB_finite ⟨n % 14, Nat.mod_lt _ (by norm_num)⟩
  have hD := blockD_finite ⟨n % 102, Nat.mod_lt _ (by norm_num)⟩
  change -(2 : ℚ) / 3 ≤ blockA (n % 30) ∧ blockA (n % 30) ≤ 14 / 15 at hA
  change -(1 : ℚ) / 2 ≤ blockB (n % 14) ∧ blockB (n % 14) ≤ 3 / 7 at hB
  change -(2 : ℚ) ≤ blockD (n % 102) ∧ blockD (n % 102) ≤ 6584 / 15015 at hD
  rw [blockA_period] at hA
  rw [blockB_period] at hB
  rw [blockD_period] at hD
  have h11n : 0 ≤ ((n % 11 : ℕ) : ℚ) := by positivity
  have h13n : 0 ≤ ((n % 13 : ℕ) : ℚ) := by positivity
  have h11 : ((n % 11 : ℕ) : ℚ) ≤ 10 := by
    exact_mod_cast (show n % 11 ≤ 10 by omega)
  have h13 : ((n % 13 : ℕ) : ℚ) ≤ 12 := by
    exact_mod_cast (show n % 13 ≤ 12 by omega)
  have hC : 0 ≤ blockC n ∧ blockC n ≤ 10 / 11 + 12 / 13 := by
    dsimp [blockC]
    constructor <;> linarith
  rw [abs_le]
  dsimp [rationalValue]
  constructor <;> linarith [hA.1, hA.2, hB.1, hB.2, hC.1, hC.2, hD.1, hD.2]

theorem certificate_abs_le_four (n : ℕ) : |qSequence certificate n| ≤ 4 := by
  rw [certificate_sequence]
  exact_mod_cast rationalValue_abs_le_four n

theorem certificate_exact_head (n : ℕ) (hn : 0 < n) (hH : n ≤ 16) :
    qSequence certificate n = 1 := by
  rw [certificate_sequence]
  interval_cases n <;> norm_num [rationalValue, blockA, blockB, blockC, blockD]

theorem certificate_mem_stage : certificate ∈ divisorStage 510510 := by
  have hm (d : ℕ) (hd : d ∣ 510510) : qResidue d ∈ divisorStage 510510 :=
    Submodule.subset_span ⟨d, hd, rfl⟩
  unfold certificate
  repeat first
    | apply (divisorStage 510510).add_mem
    | apply (divisorStage 510510).sub_mem
    | apply (divisorStage 510510).smul_mem
    | exact hm _ (by norm_num)

theorem certificate_legal : certificate ∈ qSquarefreeCRTSpan := by
  have hp : primorial 17 = 510510 := by decide +kernel
  have hsf : Squarefree 510510 := by
    rw [← hp]
    exact squarefree_primorial 17
  exact divisorStage_le_squarefreeSpan 510510 (by norm_num) hsf certificate_mem_stage

/-- Common-denominator numerator: no floating arithmetic enters the certificate. -/
def integerValue (n : ℕ) : ℤ :=
  255255 * ((n % 2 : ℕ) : ℤ) + 170170 * ((n % 3 : ℕ) : ℤ) + 102102 * ((n % 5 : ℕ) : ℤ) -
  85085 * ((n % 6 : ℕ) : ℤ) + 72930 * ((n % 7 : ℕ) : ℤ) - 51051 * ((n % 10 : ℕ) : ℤ) +
  46410 * ((n % 11 : ℕ) : ℤ) + 39270 * ((n % 13 : ℕ) : ℤ) - 36465 * ((n % 14 : ℕ) : ℤ) -
  34034 * ((n % 15 : ℕ) : ℤ) + 59036 * ((n % 17 : ℕ) : ℤ) + 17017 * ((n % 30 : ℕ) : ℤ) -
  30030 * ((n % 34 : ℕ) : ℤ) - 15015 * ((n % 51 : ℕ) : ℤ)

theorem rationalValue_eq_integer (n : ℕ) :
    rationalValue n = (integerValue n : ℚ) / 510510 := by
  unfold rationalValue blockA blockB blockC blockD integerValue
  simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  ring

def scaledTerm (n : ℕ) : ℚ :=
  100000000 * (integerValue (n + 1) : ℚ) ^ 2 /
    (510510 ^ 2 * (n + 1 : ℚ) ^ 2)

def roundedTerm (n : ℕ) : ℤ := ⌈scaledTerm n⌉

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation of 1024 exact integer ceilings needs a larger tactic budget.
/-- Upward rounding is done separately at every site, retaining signed cancellation
inside the square. The sum is entirely integer arithmetic. -/
theorem rounded_prefix_exact :
    (∑ n ∈ Finset.range 1024, roundedTerm n) = 162048069 := by decide +kernel

theorem roundedTerm_upper (n : ℕ) :
    (qSequence certificate (n + 1)) ^ 2 / (n + 1 : ℝ) ^ 2 ≤
      (roundedTerm n : ℝ) / 100000000 := by
  have hq : scaledTerm n ≤ (roundedTerm n : ℚ) := Int.le_ceil _
  have hr : (scaledTerm n : ℝ) ≤ (roundedTerm n : ℝ) := by exact_mod_cast hq
  have he : (scaledTerm n : ℝ) =
      100000000 * (qSequence certificate (n + 1)) ^ 2 / (n + 1 : ℝ) ^ 2 := by
    rw [certificate_sequence, rationalValue_eq_integer]
    unfold scaledTerm
    push_cast
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hn]
  rw [he] at hr
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 100000000)).mpr
  calc
    (qSequence certificate (n + 1)) ^ 2 / (n + 1 : ℝ) ^ 2 * 100000000 =
        100000000 * (qSequence certificate (n + 1)) ^ 2 / (n + 1 : ℝ) ^ 2 := by ring
    _ ≤ (roundedTerm n : ℝ) := hr

theorem prefix_upper :
    (∑ n ∈ Finset.range 1024,
      (qSequence certificate (n + 1)) ^ 2 / (n + 1 : ℝ) ^ 2) ≤
        (162048069 : ℝ) / 100000000 := by
  calc
    _ ≤ ∑ n ∈ Finset.range 1024, (roundedTerm n : ℝ) / 100000000 :=
      Finset.sum_le_sum (fun n _ => roundedTerm_upper n)
    _ = _ := by
      rw [← Finset.sum_div]
      have hcast : (∑ n ∈ Finset.range 1024, (roundedTerm n : ℝ)) = 162048069 := by
        exact_mod_cast rounded_prefix_exact
      rw [hcast]

/-- A strict bound on the complete infinite Q energy of the actual legal vector. -/
theorem certificate_energy_bound :
    ‖certificate‖ ^ 2 ≤ (3108600811 : ℝ) / 3125000000 := by
  have ht := norm_sq_le_head_tail certificate 1024 (by norm_num) 4
    (by norm_num) certificate_abs_le_four
  have hsum := prefix_upper
  have hz := inverse_zetaTwo_rational_bounds.2.le
  have hstep : ‖certificate‖ ^ 2 ≤ (1 / zetaTwo) *
      ((162048069 : ℝ) / 100000000 + 4 ^ 2 / 1024) :=
    ht.trans (mul_le_mul_of_nonneg_left (add_le_add hsum (le_refl _))
      (one_div_pos.mpr zetaTwo_pos).le)
  calc
    _ ≤ (1 / zetaTwo) * ((162048069 : ℝ) / 100000000 + 4 ^ 2 / 1024) := hstep
    _ ≤ (76 / 125 : ℝ) * ((162048069 : ℝ) / 100000000 + 4 ^ 2 / 1024) :=
      mul_le_mul_of_nonneg_right hz (by norm_num)
    _ = _ := by norm_num

theorem certificate_energy_lt_one : ‖certificate‖ ^ 2 < 1 :=
  certificate_energy_bound.trans_lt (by norm_num)

/-- The certified upper bound applies to the actual complete minimum at the
requested period and head, not merely to the displayed candidate. -/
theorem minimumAt_fifteen_head15_bound :
    ‖minimumAt 15 15‖ ^ 2 ≤ (3108600811 : ℝ) / 3125000000 := by
  have hp : primorial (15 + 2) = 510510 := by decide +kernel
  have hm : certificate ∈ divisorStage (primorial (15 + 2)) := by
    simpa only [hp] using certificate_mem_stage
  have h := minimumAt_completion 15 15 (by norm_num) certificate hm
    (fun n hn hH => certificate_exact_head n hn (by omega))
  nlinarith [certificate_energy_bound, sq_nonneg ‖certificate - minimumAt 15 15‖]

theorem minimumAt_fifteen_head15_lt_one : ‖minimumAt 15 15‖ ^ 2 < 1 :=
  minimumAt_fifteen_head15_bound.trans_lt (by norm_num)

end RiemannResearch.RH.QCRTPeriod510510Certificate
