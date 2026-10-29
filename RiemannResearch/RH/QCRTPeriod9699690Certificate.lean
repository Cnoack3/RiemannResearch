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
# A complete-energy certificate after inserting conductor 19

Source: the user-provided delayed-period CRT research task, 28 October 2026.
The rational vector was found by signed full-Gram exploration. This module
checks exact head 20, a uniform physical-coordinate bound, an upward-rounded
finite prefix, and the entire infinite Q-tail. Its conclusion concerns a
single finite stage, and supplies no uniform bound for a cofinal family.
-/

noncomputable section
set_option maxRecDepth 100000
open scoped BigOperators
namespace RiemannResearch.RH.QCRTPeriod9699690Certificate
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open QSquarefreeLatticePackets QFiniteEnergyBounds QCRTPeriodHeadBalance

def rationalValue (n : ℕ) : ℚ :=
  ((n % 2 : ℕ) : ℚ) / 2 +
  ((n % 3 : ℕ) : ℚ) / 3 +
  ((n % 5 : ℕ) : ℚ) / 5 -
  ((n % 6 : ℕ) : ℚ) / 6 +
  ((n % 7 : ℕ) : ℚ) / 7 -
  ((n % 10 : ℕ) : ℚ) / 10 +
  ((n % 11 : ℕ) : ℚ) / 11 +
  ((n % 13 : ℕ) : ℚ) / 13 -
  ((n % 14 : ℕ) : ℚ) / 14 -
  ((n % 15 : ℕ) : ℚ) / 15 +
  ((n % 17 : ℕ) : ℚ) / 17 +
  ((n % 19 : ℕ) : ℚ) / 19 +
  (249384135 / 255255000 : ℚ) * (((n % 30 : ℕ) : ℚ) / 30) -
  (260870610 / 255255000 : ℚ) * (((n % 34 : ℕ) : ℚ) / 34) -
  (217614037 / 255255000 : ℚ) * (((n % 38 : ℕ) : ℚ) / 38) -
  (218753535 / 255255000 : ℚ) * (((n % 51 : ℕ) : ℚ) / 51) -
  (232026795 / 255255000 : ℚ) * (((n % 65 : ℕ) : ℚ) / 65)

def certificate : QHilbert :=
  qResidue 2 +
  qResidue 3 +
  qResidue 5 -
  qResidue 6 +
  qResidue 7 -
  qResidue 10 +
  qResidue 11 +
  qResidue 13 -
  qResidue 14 -
  qResidue 15 +
  qResidue 17 +
  qResidue 19 +
  (249384135 / 255255000 : ℝ) • qResidue 30 -
  (260870610 / 255255000 : ℝ) • qResidue 34 -
  (217614037 / 255255000 : ℝ) • qResidue 38 -
  (218753535 / 255255000 : ℝ) • qResidue 51 -
  (232026795 / 255255000 : ℝ) • qResidue 65

theorem certificate_sequence (n : ℕ) :
    qSequence certificate n = (rationalValue n : ℝ) := by
  change qSequenceLinear (qResidue 2 +
  qResidue 3 +
  qResidue 5 -
  qResidue 6 +
  qResidue 7 -
  qResidue 10 +
  qResidue 11 +
  qResidue 13 -
  qResidue 14 -
  qResidue 15 +
  qResidue 17 +
  qResidue 19 +
  (249384135 / 255255000 : ℝ) • qResidue 30 -
  (260870610 / 255255000 : ℝ) • qResidue 34 -
  (217614037 / 255255000 : ℝ) • qResidue 38 -
  (218753535 / 255255000 : ℝ) • qResidue 51 -
  (232026795 / 255255000 : ℝ) • qResidue 65) n = _
  simp only [map_sub, map_add, map_smul, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  change qSequence (qResidue 2) n +
  qSequence (qResidue 3) n +
  qSequence (qResidue 5) n -
  qSequence (qResidue 6) n +
  qSequence (qResidue 7) n -
  qSequence (qResidue 10) n +
  qSequence (qResidue 11) n +
  qSequence (qResidue 13) n -
  qSequence (qResidue 14) n -
  qSequence (qResidue 15) n +
  qSequence (qResidue 17) n +
  qSequence (qResidue 19) n +
  (249384135 / 255255000 : ℝ) * qSequence (qResidue 30) n -
  (260870610 / 255255000 : ℝ) * qSequence (qResidue 34) n -
  (217614037 / 255255000 : ℝ) * qSequence (qResidue 38) n -
  (218753535 / 255255000 : ℝ) * qSequence (qResidue 51) n -
  (232026795 / 255255000 : ℝ) * qSequence (qResidue 65) n = _
  simp [qSequence_qResidue, residueFraction, rationalValue]

/-- An integer numerator for the physical vector. -/
def integerValue (n : ℕ) : ℤ :=
  4849845000 * ((n % 2 : ℕ) : ℤ) +
  3233230000 * ((n % 3 : ℕ) : ℤ) +
  1939938000 * ((n % 5 : ℕ) : ℤ) -
  1616615000 * ((n % 6 : ℕ) : ℤ) +
  1385670000 * ((n % 7 : ℕ) : ℤ) -
  969969000 * ((n % 10 : ℕ) : ℤ) +
  881790000 * ((n % 11 : ℕ) : ℤ) +
  746130000 * ((n % 13 : ℕ) : ℤ) -
  692835000 * ((n % 14 : ℕ) : ℤ) -
  646646000 * ((n % 15 : ℕ) : ℤ) +
  570570000 * ((n % 17 : ℕ) : ℤ) +
  510510000 * ((n % 19 : ℕ) : ℤ) +
  315886571 * ((n % 30 : ℕ) : ℤ) -
  291561270 * ((n % 34 : ℕ) : ℤ) -
  217614037 * ((n % 38 : ℕ) : ℤ) -
  162992830 * ((n % 51 : ℕ) : ℤ) -
  135646434 * ((n % 65 : ℕ) : ℤ)

theorem rationalValue_eq_integer (n : ℕ) :
    rationalValue n = (integerValue n : ℚ) / 9699690000 := by
  unfold rationalValue integerValue
  simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  ring

theorem integerValue_bounds (n : ℕ) :
    -(8 * 9699690000 : ℤ) ≤ integerValue n ∧
      integerValue n ≤ (8 * 9699690000 : ℤ) := by
  have hl2 : (0 : ℤ) ≤ ((n % 2 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.zero_le (n % 2))
  have hu2 : ((n % 2 : ℕ) : ℤ) ≤ 1 := by
    exact_mod_cast (Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num : 0 < 2)))
  have hl3 : (0 : ℤ) ≤ ((n % 3 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.zero_le (n % 3))
  have hu3 : ((n % 3 : ℕ) : ℤ) ≤ 2 := by
    exact_mod_cast (Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num : 0 < 3)))
  have hl5 : (0 : ℤ) ≤ ((n % 5 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.zero_le (n % 5))
  have hu5 : ((n % 5 : ℕ) : ℤ) ≤ 4 := by
    exact_mod_cast (Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num : 0 < 5)))
  have hl6 : (0 : ℤ) ≤ ((n % 6 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.zero_le (n % 6))
  have hu6 : ((n % 6 : ℕ) : ℤ) ≤ 5 := by
    exact_mod_cast (Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num : 0 < 6)))
  have hl7 : (0 : ℤ) ≤ ((n % 7 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.zero_le (n % 7))
  have hu7 : ((n % 7 : ℕ) : ℤ) ≤ 6 := by
    exact_mod_cast (Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num : 0 < 7)))
  have hl10 : (0 : ℤ) ≤ ((n % 10 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.zero_le (n % 10))
  have hu10 : ((n % 10 : ℕ) : ℤ) ≤ 9 := by
    exact_mod_cast (Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num : 0 < 10)))
  have hl11 : (0 : ℤ) ≤ ((n % 11 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.zero_le (n % 11))
  have hu11 : ((n % 11 : ℕ) : ℤ) ≤ 10 := by
    exact_mod_cast (Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num : 0 < 11)))
  have hl13 : (0 : ℤ) ≤ ((n % 13 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.zero_le (n % 13))
  have hu13 : ((n % 13 : ℕ) : ℤ) ≤ 12 := by
    exact_mod_cast (Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num : 0 < 13)))
  have hl14 : (0 : ℤ) ≤ ((n % 14 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.zero_le (n % 14))
  have hu14 : ((n % 14 : ℕ) : ℤ) ≤ 13 := by
    exact_mod_cast (Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num : 0 < 14)))
  have hl15 : (0 : ℤ) ≤ ((n % 15 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.zero_le (n % 15))
  have hu15 : ((n % 15 : ℕ) : ℤ) ≤ 14 := by
    exact_mod_cast (Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num : 0 < 15)))
  have hl17 : (0 : ℤ) ≤ ((n % 17 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.zero_le (n % 17))
  have hu17 : ((n % 17 : ℕ) : ℤ) ≤ 16 := by
    exact_mod_cast (Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num : 0 < 17)))
  have hl19 : (0 : ℤ) ≤ ((n % 19 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.zero_le (n % 19))
  have hu19 : ((n % 19 : ℕ) : ℤ) ≤ 18 := by
    exact_mod_cast (Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num : 0 < 19)))
  have hl30 : (0 : ℤ) ≤ ((n % 30 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.zero_le (n % 30))
  have hu30 : ((n % 30 : ℕ) : ℤ) ≤ 29 := by
    exact_mod_cast (Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num : 0 < 30)))
  have hl34 : (0 : ℤ) ≤ ((n % 34 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.zero_le (n % 34))
  have hu34 : ((n % 34 : ℕ) : ℤ) ≤ 33 := by
    exact_mod_cast (Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num : 0 < 34)))
  have hl38 : (0 : ℤ) ≤ ((n % 38 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.zero_le (n % 38))
  have hu38 : ((n % 38 : ℕ) : ℤ) ≤ 37 := by
    exact_mod_cast (Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num : 0 < 38)))
  have hl51 : (0 : ℤ) ≤ ((n % 51 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.zero_le (n % 51))
  have hu51 : ((n % 51 : ℕ) : ℤ) ≤ 50 := by
    exact_mod_cast (Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num : 0 < 51)))
  have hl65 : (0 : ℤ) ≤ ((n % 65 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.zero_le (n % 65))
  have hu65 : ((n % 65 : ℕ) : ℤ) ≤ 64 := by
    exact_mod_cast (Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num : 0 < 65)))
  unfold integerValue
  constructor <;> linarith only [hl2, hu2, hl3, hu3, hl5, hu5, hl6, hu6, hl7, hu7,
    hl10, hu10, hl11, hu11, hl13, hu13, hl14, hu14, hl15, hu15, hl17, hu17,
    hl19, hu19, hl30, hu30, hl34, hu34, hl38, hu38, hl51, hu51, hl65, hu65]

theorem rationalValue_abs_le_eight (n : ℕ) : |rationalValue n| ≤ 8 := by
  have hi := integerValue_bounds n
  have hq : -(8 * 9699690000 : ℚ) ≤ (integerValue n : ℚ) ∧
      (integerValue n : ℚ) ≤ (8 * 9699690000 : ℚ) := by exact_mod_cast hi
  have habs : |(integerValue n : ℚ)| ≤ 8 * 9699690000 := abs_le.mpr hq
  rw [rationalValue_eq_integer, abs_div]
  norm_num only [abs_of_pos (by norm_num : (0 : ℚ) < 9699690000)]
  exact (div_le_iff₀ (by norm_num : (0 : ℚ) < 9699690000)).mpr habs

theorem certificate_abs_le_eight (n : ℕ) : |qSequence certificate n| ≤ 8 := by
  rw [certificate_sequence]
  exact_mod_cast rationalValue_abs_le_eight n

theorem certificate_exact_head (n : ℕ) (hn : 0 < n) (hH : n ≤ 20) :
    qSequence certificate n = 1 := by
  rw [certificate_sequence]
  interval_cases n <;> norm_num [rationalValue]

theorem certificate_mem_stage : certificate ∈ divisorStage 9699690 := by
  have hm (d : ℕ) (hd : d ∣ 9699690) : qResidue d ∈ divisorStage 9699690 :=
    Submodule.subset_span ⟨d, hd, rfl⟩
  unfold certificate
  repeat first
    | apply (divisorStage 9699690).add_mem
    | apply (divisorStage 9699690).sub_mem
    | apply (divisorStage 9699690).smul_mem
    | exact hm _ (by norm_num)

theorem certificate_legal : certificate ∈ qSquarefreeCRTSpan := by
  have hp : primorial 19 = 9699690 := by decide +kernel
  have hsf : Squarefree 9699690 := by
    rw [← hp]
    exact squarefree_primorial 19
  exact divisorStage_le_squarefreeSpan 9699690 (by norm_num) hsf certificate_mem_stage

def scaledTerm (n : ℕ) : ℚ :=
  10000000000 * (integerValue (n + 1) : ℚ) ^ 2 /
    (9699690000 ^ 2 * (n + 1 : ℚ) ^ 2)

def roundedTerm (n : ℕ) : ℤ := ⌈scaledTerm n⌉

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel evaluation of 4096 exact integer ceilings needs a larger tactic budget.
/-- Upward rounding at each coordinate retains every signed term inside the square. -/
theorem rounded_prefix_exact :
    (∑ n ∈ Finset.range 4096, roundedTerm n) = 16225558099 := by decide +kernel

theorem roundedTerm_upper (n : ℕ) :
    (qSequence certificate (n + 1)) ^ 2 / (n + 1 : ℝ) ^ 2 ≤
      (roundedTerm n : ℝ) / 10000000000 := by
  have hq : scaledTerm n ≤ (roundedTerm n : ℚ) := Int.le_ceil _
  have hr : (scaledTerm n : ℝ) ≤ (roundedTerm n : ℝ) := by exact_mod_cast hq
  have he : (scaledTerm n : ℝ) =
      10000000000 * (qSequence certificate (n + 1)) ^ 2 / (n + 1 : ℝ) ^ 2 := by
    rw [certificate_sequence, rationalValue_eq_integer]
    unfold scaledTerm
    push_cast
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hn]
  rw [he] at hr
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 10000000000)).mpr
  calc
    (qSequence certificate (n + 1)) ^ 2 / (n + 1 : ℝ) ^ 2 * 10000000000 =
        10000000000 * (qSequence certificate (n + 1)) ^ 2 / (n + 1 : ℝ) ^ 2 := by ring
    _ ≤ (roundedTerm n : ℝ) := hr

theorem prefix_upper :
    (∑ n ∈ Finset.range 4096,
      (qSequence certificate (n + 1)) ^ 2 / (n + 1 : ℝ) ^ 2) ≤
        (16225558099 : ℝ) / 10000000000 := by
  calc
    _ ≤ ∑ n ∈ Finset.range 4096, (roundedTerm n : ℝ) / 10000000000 :=
      Finset.sum_le_sum (fun n _ => roundedTerm_upper n)
    _ = _ := by
      rw [← Finset.sum_div]
      have hcast : (∑ n ∈ Finset.range 4096, (roundedTerm n : ℝ)) = 16225558099 := by
        exact_mod_cast rounded_prefix_exact
      rw [hcast]

/-- A rational upper bound for the complete infinite Q-energy. -/
theorem certificate_energy_bound :
    ‖certificate‖ ^ 2 ≤ (311254353881 : ℝ) / 312500000000 := by
  have ht := norm_sq_le_head_tail certificate 4096 (by norm_num) 8
    (by norm_num) certificate_abs_le_eight
  have hsum := prefix_upper
  have hz := inverse_zetaTwo_rational_bounds.2.le
  have hstep : ‖certificate‖ ^ 2 ≤ (1 / zetaTwo) *
      ((16225558099 : ℝ) / 10000000000 + 8 ^ 2 / 4096) :=
    ht.trans (mul_le_mul_of_nonneg_left (add_le_add hsum (le_refl _))
      (one_div_pos.mpr zetaTwo_pos).le)
  calc
    _ ≤ (1 / zetaTwo) * ((16225558099 : ℝ) / 10000000000 + 8 ^ 2 / 4096) := hstep
    _ ≤ (76 / 125 : ℝ) * ((16225558099 : ℝ) / 10000000000 + 8 ^ 2 / 4096) :=
      mul_le_mul_of_nonneg_right hz (by norm_num)
    _ = _ := by norm_num

theorem certificate_energy_lt_one : ‖certificate‖ ^ 2 < 1 :=
  certificate_energy_bound.trans_lt (by norm_num)

/-- The actual constrained minimum for period 9699690 and head 19 is below one. -/
theorem minimumAt_eighteen_head19_bound :
    ‖minimumAt 18 19‖ ^ 2 ≤ (311254353881 : ℝ) / 312500000000 := by
  have hp : primorial (18 + 2) = 9699690 := by decide +kernel
  have hm : certificate ∈ divisorStage (primorial (18 + 2)) := by
    simpa only [hp] using certificate_mem_stage
  have h := minimumAt_completion 18 19 (by norm_num) certificate hm
    (fun n hn hH => certificate_exact_head n hn (by omega))
  nlinarith [certificate_energy_bound, sq_nonneg ‖certificate - minimumAt 18 19‖]

theorem minimumAt_eighteen_head19_lt_one : ‖minimumAt 18 19‖ ^ 2 < 1 :=
  minimumAt_eighteen_head19_bound.trans_lt (by norm_num)

end RiemannResearch.RH.QCRTPeriod9699690Certificate
