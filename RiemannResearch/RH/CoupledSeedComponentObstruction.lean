import RiemannResearch.RH.PositiveSeedCone
import RiemannResearch.LinearAlgebra.WeightedDualCertificate
import Mathlib.Tactic.FinCases

/-!
# Coupled component obstruction with seed exponents bounded by 4 and 2

The condition is `32 ∤ M` and `27 ∤ M`; powers of every other prime remain
unrestricted. Coupling the root component with the component at 5 gives a finite
actual-generator annihilator with exact signed full-error lower bound `272/15927`.
This retains the mixed component contribution and improves the root-only bound
`1/59`. The arithmetic certificate was independently derived in the research
notes; no historical priority claim is intended.
-/

namespace RiemannResearch.RH.CoupledSeedComponentObstruction

open scoped BigOperators
open PositiveSeedCone TwoSeedThreshold
open RiemannResearch.LinearAlgebra

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private def chargeCoordinate : Fin 51 → ℕ :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 23, 24, 29, 30, 35, 36, 39, 40, 44, 45, 47, 48, 59, 60, 71, 72, 79, 80, 89, 90, 119, 120, 143, 144, 179, 180, 239, 240, 359, 360, 719, 720]

private def chargeNumerator : Fin 51 → ℤ :=
  ![16320, 5440, 2720, 7632, -4912, 5440, -4080, -1360, 5176, 264, -2720, 2720, -176, -3904, 4080, -2720, 2720, -132, 132, -1360, 1360, -88, 88, -1360, 1360, -66, 66, -88, 88, -1360, 1360, -44, 44, -680, 680, -66, 66, -44, 44, -22, 22, -680, 680, -22, 22, -22, 22, -11, 11, -11, 11]

/-- The integer charge of the root component plus `11/680` times the component at 5.
The normalization is `97920` times the corresponding divergence functional. -/
def coupledSeedCharge (F : ℕ → ℝ) : ℝ :=
  ∑ r : Fin 51, (chargeNumerator r : ℝ) * F (chargeCoordinate r)

private def chargeWeight (r : Fin 51) : ℝ :=
  Pareto.positiveWeight (chargeCoordinate r)

private def chargeDual (r : Fin 51) : ℝ := (chargeNumerator r : ℝ) / 1911240

private theorem chargeWeight_pos (r : Fin 51) : 0 < chargeWeight r := by
  fin_cases r <;> norm_num [chargeWeight, chargeCoordinate, Pareto.positiveWeight]

private theorem generator_integer_charge_eq_zero_block0 (a m : ℕ)
    (ha : a = 2 ∨ a = 3) (hl : 1 ≤ m) (hu : m ≤ 72)
    (h32 : ¬ 32 ∣ a * m) (h27 : ¬ 27 ∣ a * m) :
    (∑ r : Fin 51, chargeNumerator r *
      (((chargeCoordinate r % (a*m) : ℕ) : ℤ) -
        ((chargeCoordinate r % m : ℕ) : ℤ))) = 0 := by
  rcases ha with rfl | rfl
  all_goals interval_cases m <;> norm_num at *
  all_goals decide

private theorem generator_integer_charge_eq_zero_block1 (a m : ℕ)
    (ha : a = 2 ∨ a = 3) (hl : 73 ≤ m) (hu : m ≤ 144)
    (h32 : ¬ 32 ∣ a * m) (h27 : ¬ 27 ∣ a * m) :
    (∑ r : Fin 51, chargeNumerator r *
      (((chargeCoordinate r % (a*m) : ℕ) : ℤ) -
        ((chargeCoordinate r % m : ℕ) : ℤ))) = 0 := by
  rcases ha with rfl | rfl
  all_goals interval_cases m <;> norm_num at *
  all_goals decide

private theorem generator_integer_charge_eq_zero_block2 (a m : ℕ)
    (ha : a = 2 ∨ a = 3) (hl : 145 ≤ m) (hu : m ≤ 216)
    (h32 : ¬ 32 ∣ a * m) (h27 : ¬ 27 ∣ a * m) :
    (∑ r : Fin 51, chargeNumerator r *
      (((chargeCoordinate r % (a*m) : ℕ) : ℤ) -
        ((chargeCoordinate r % m : ℕ) : ℤ))) = 0 := by
  rcases ha with rfl | rfl
  all_goals interval_cases m <;> norm_num at *
  all_goals decide

private theorem generator_integer_charge_eq_zero_block3 (a m : ℕ)
    (ha : a = 2 ∨ a = 3) (hl : 217 ≤ m) (hu : m ≤ 288)
    (h32 : ¬ 32 ∣ a * m) (h27 : ¬ 27 ∣ a * m) :
    (∑ r : Fin 51, chargeNumerator r *
      (((chargeCoordinate r % (a*m) : ℕ) : ℤ) -
        ((chargeCoordinate r % m : ℕ) : ℤ))) = 0 := by
  rcases ha with rfl | rfl
  all_goals interval_cases m <;> norm_num at *
  all_goals decide

private theorem generator_integer_charge_eq_zero_block4 (a m : ℕ)
    (ha : a = 2 ∨ a = 3) (hl : 289 ≤ m) (hu : m ≤ 360)
    (h32 : ¬ 32 ∣ a * m) (h27 : ¬ 27 ∣ a * m) :
    (∑ r : Fin 51, chargeNumerator r *
      (((chargeCoordinate r % (a*m) : ℕ) : ℤ) -
        ((chargeCoordinate r % m : ℕ) : ℤ))) = 0 := by
  rcases ha with rfl | rfl
  all_goals interval_cases m <;> norm_num at *
  all_goals decide

private theorem generator_integer_charge_eq_zero_block5 (a m : ℕ)
    (ha : a = 2 ∨ a = 3) (hl : 361 ≤ m) (hu : m ≤ 432)
    (h32 : ¬ 32 ∣ a * m) (h27 : ¬ 27 ∣ a * m) :
    (∑ r : Fin 51, chargeNumerator r *
      (((chargeCoordinate r % (a*m) : ℕ) : ℤ) -
        ((chargeCoordinate r % m : ℕ) : ℤ))) = 0 := by
  rcases ha with rfl | rfl
  all_goals interval_cases m <;> norm_num at *
  all_goals decide

private theorem generator_integer_charge_eq_zero_block6 (a m : ℕ)
    (ha : a = 2 ∨ a = 3) (hl : 433 ≤ m) (hu : m ≤ 504)
    (h32 : ¬ 32 ∣ a * m) (h27 : ¬ 27 ∣ a * m) :
    (∑ r : Fin 51, chargeNumerator r *
      (((chargeCoordinate r % (a*m) : ℕ) : ℤ) -
        ((chargeCoordinate r % m : ℕ) : ℤ))) = 0 := by
  rcases ha with rfl | rfl
  all_goals interval_cases m <;> norm_num at *
  all_goals decide

private theorem generator_integer_charge_eq_zero_block7 (a m : ℕ)
    (ha : a = 2 ∨ a = 3) (hl : 505 ≤ m) (hu : m ≤ 576)
    (h32 : ¬ 32 ∣ a * m) (h27 : ¬ 27 ∣ a * m) :
    (∑ r : Fin 51, chargeNumerator r *
      (((chargeCoordinate r % (a*m) : ℕ) : ℤ) -
        ((chargeCoordinate r % m : ℕ) : ℤ))) = 0 := by
  rcases ha with rfl | rfl
  all_goals interval_cases m <;> norm_num at *
  all_goals decide

private theorem generator_integer_charge_eq_zero_block8 (a m : ℕ)
    (ha : a = 2 ∨ a = 3) (hl : 577 ≤ m) (hu : m ≤ 648)
    (h32 : ¬ 32 ∣ a * m) (h27 : ¬ 27 ∣ a * m) :
    (∑ r : Fin 51, chargeNumerator r *
      (((chargeCoordinate r % (a*m) : ℕ) : ℤ) -
        ((chargeCoordinate r % m : ℕ) : ℤ))) = 0 := by
  rcases ha with rfl | rfl
  all_goals interval_cases m <;> norm_num at *
  all_goals decide

private theorem generator_integer_charge_eq_zero_block9 (a m : ℕ)
    (ha : a = 2 ∨ a = 3) (hl : 649 ≤ m) (hu : m ≤ 720)
    (h32 : ¬ 32 ∣ a * m) (h27 : ¬ 27 ∣ a * m) :
    (∑ r : Fin 51, chargeNumerator r *
      (((chargeCoordinate r % (a*m) : ℕ) : ℤ) -
        ((chargeCoordinate r % m : ℕ) : ℤ))) = 0 := by
  rcases ha with rfl | rfl
  all_goals interval_cases m <;> norm_num at *
  all_goals decide

private theorem generator_integer_charge_eq_zero (a m : ℕ)
    (ha : a = 2 ∨ a = 3) (hm : 0 < m)
    (h32 : ¬ 32 ∣ a * m) (h27 : ¬ 27 ∣ a * m) :
    (∑ r : Fin 51, chargeNumerator r *
      (((chargeCoordinate r % (a*m) : ℕ) : ℤ) -
        ((chargeCoordinate r % m : ℕ) : ℤ))) = 0 := by
  by_cases hm720 : m ≤ 720
  · by_cases h72 : m ≤ 72
    · exact generator_integer_charge_eq_zero_block0 a m ha (by omega) h72 h32 h27
    by_cases h144 : m ≤ 144
    · exact generator_integer_charge_eq_zero_block1 a m ha (by omega) h144 h32 h27
    by_cases h216 : m ≤ 216
    · exact generator_integer_charge_eq_zero_block2 a m ha (by omega) h216 h32 h27
    by_cases h288 : m ≤ 288
    · exact generator_integer_charge_eq_zero_block3 a m ha (by omega) h288 h32 h27
    by_cases h360 : m ≤ 360
    · exact generator_integer_charge_eq_zero_block4 a m ha (by omega) h360 h32 h27
    by_cases h432 : m ≤ 432
    · exact generator_integer_charge_eq_zero_block5 a m ha (by omega) h432 h32 h27
    by_cases h504 : m ≤ 504
    · exact generator_integer_charge_eq_zero_block6 a m ha (by omega) h504 h32 h27
    by_cases h576 : m ≤ 576
    · exact generator_integer_charge_eq_zero_block7 a m ha (by omega) h576 h32 h27
    by_cases h648 : m ≤ 648
    · exact generator_integer_charge_eq_zero_block8 a m ha (by omega) h648 h32 h27
    exact generator_integer_charge_eq_zero_block9 a m ha (by omega) hm720 h32 h27
  · have hmlarge : 720 < m := by omega
    have ha1 : 1 ≤ a := by rcases ha with rfl | rfl <;> omega
    apply Finset.sum_eq_zero
    intro r _
    have hr : chargeCoordinate r ≤ 720 := by
      fin_cases r <;> norm_num [chargeCoordinate]
    have hkm : chargeCoordinate r < m := by omega
    have hkam : chargeCoordinate r < a * m := by nlinarith
    rw [Nat.mod_eq_of_lt hkm, Nat.mod_eq_of_lt hkam]
    ring

/-- Exact arithmetic annihilation, uniform over every positive legal dilation. -/
theorem generator_coupledSeedCharge_eq_zero (a m : ℕ)
    (ha : a = 2 ∨ a = 3) (hm : 0 < m)
    (h32 : ¬ 32 ∣ a * m) (h27 : ¬ 27 ∣ a * m) :
    coupledSeedCharge (certificateGenerator a m) = 0 := by
  have hi := generator_integer_charge_eq_zero a m ha hm h32 h27
  unfold coupledSeedCharge
  simp only [certificateGenerator]
  exact_mod_cast hi

/-- Exact weighted dual value; every signed coordinate contributes. -/
private theorem chargeDual_value :
    (∑ r : Fin 51, (2 * chargeDual r - (chargeDual r)^2 / chargeWeight r)) =
      (272 : ℝ) / 15927 := by
  norm_num [Fin.sum_univ_succ, chargeDual, chargeNumerator,
    chargeWeight, chargeCoordinate, Pareto.positiveWeight]

theorem coupledSeedCharge_seedCombination {ι : Type*} (s : Finset ι)
    (a m : ι → ℕ) (c : ι → ℝ) :
    coupledSeedCharge (seedCombination s a m c) =
      ∑ i ∈ s, c i * coupledSeedCharge (certificateGenerator (a i) (m i)) := by
  unfold coupledSeedCharge seedCombination
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem seedCombination_coupledSeedCharge_eq_zero {ι : Type*}
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ) (M : ℕ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i)
    (hperiod : ∀ i ∈ s, a i * m i ∣ M)
    (h32 : ¬ 32 ∣ M) (h27 : ¬ 27 ∣ M) :
    coupledSeedCharge (seedCombination s a m c) = 0 := by
  rw [coupledSeedCharge_seedCombination]
  apply Finset.sum_eq_zero
  intro i hi
  have h32i : ¬ 32 ∣ a i * m i := fun h => h32 (dvd_trans h (hperiod i hi))
  have h27i : ¬ 27 ∣ a i * m i := fun h => h27 (dvd_trans h (hperiod i hi))
  rw [generator_coupledSeedCharge_eq_zero (a i) (m i) (ha i hi) (hm i hi)
    h32i h27i, mul_zero]

/-- The finite weighted error retained by the dual certificate. -/
def coupledSeedFiniteError (F : ℕ → ℝ) : ℝ :=
  ∑ r : Fin 51, chargeWeight r * (1 - F (chargeCoordinate r)) ^ 2

private theorem chargeDual_annihilates (F : ℕ → ℝ)
    (hF : coupledSeedCharge F = 0) :
    (∑ r : Fin 51, chargeDual r * F (chargeCoordinate r)) = 0 := by
  calc
    _ = coupledSeedCharge F / 1911240 := by
      simp only [chargeDual, coupledSeedCharge, div_mul_eq_mul_div, Finset.sum_div]
    _ = 0 := by rw [hF]; norm_num

/-- The exact square remainder in the finite weighted dual identity. -/
theorem coupledSeedFiniteError_exact (F : ℕ → ℝ)
    (hF : coupledSeedCharge F = 0) :
    coupledSeedFiniteError F = (272 : ℝ) / 15927 +
      ∑ r : Fin 51, chargeWeight r *
        (1 - F (chargeCoordinate r) - chargeDual r / chargeWeight r) ^ 2 := by
  unfold coupledSeedFiniteError
  rw [weighted_error_dual_exact chargeWeight chargeDual
    (fun r => F (chargeCoordinate r)) chargeWeight_pos (chargeDual_annihilates F hF)]
  rw [chargeDual_value]

private theorem coupledSeedFiniteError_lower (F : ℕ → ℝ)
    (hF : coupledSeedCharge F = 0) :
    (272 : ℝ) / 15927 ≤ coupledSeedFiniteError F := by
  have hl := weighted_error_lower_of_dual chargeWeight chargeDual
    (fun r => F (chargeCoordinate r)) chargeWeight_pos (chargeDual_annihilates F hF)
  rw [chargeDual_value] at hl
  exact hl

private theorem coupledSeedFiniteError_eq_sum (F : ℕ → ℝ) :
    coupledSeedFiniteError F =
      ∑ k ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 22, 23, 28, 29, 34, 35, 38, 39, 43, 44, 46, 47, 58, 59, 70, 71, 78, 79, 88, 89, 118, 119, 142, 143, 178, 179, 238, 239, 358, 359, 718, 719} : Finset ℕ),
        weightedError F k := by
  norm_num [coupledSeedFiniteError, Fin.sum_univ_succ, chargeWeight,
    chargeCoordinate, weightedError, Pareto.positiveWeight] <;> ring

/-- Complete infinite error bound from the actual finite arithmetic annihilator. -/
theorem fullError_coupledSeedCharge_lower (F : ℕ → ℝ)
    (hF : coupledSeedCharge F = 0) (hsum : Summable (weightedError F)) :
    (272 : ℝ) / 15927 ≤ ∑' k : ℕ, weightedError F k := by
  calc
    (272 : ℝ) / 15927 ≤ coupledSeedFiniteError F := coupledSeedFiniteError_lower F hF
    _ = ∑ k ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 22, 23, 28, 29, 34, 35, 38, 39, 43, 44, 46, 47, 58, 59, 70, 71, 78, 79, 88, 89, 118, 119, 142, 143, 178, 179, 238, 239, 358, 359, 718, 719} : Finset ℕ),
          weightedError F k := coupledSeedFiniteError_eq_sum F
    _ ≤ ∑' k : ℕ, weightedError F k :=
      hsum.sum_le_tsum _ (fun k _ => weightedError_nonneg F k)

/-- Arbitrary primes and their powers cannot remove this fixed seed-grid obstruction. -/
theorem conductor_seedCaps_four_two_coupled_fullError_lower {ι : Type*}
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ) (M : ℕ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i)
    (hperiod : ∀ i ∈ s, a i * m i ∣ M)
    (h32 : ¬ 32 ∣ M) (h27 : ¬ 27 ∣ M) :
    (272 : ℝ) / 15927 ≤ ∑' k : ℕ, weightedError (seedCombination s a m c) k := by
  have ha0 : ∀ i ∈ s, 0 < a i := by
    intro i hi
    rcases ha i hi with h | h <;> omega
  exact fullError_coupledSeedCharge_lower _
    (seedCombination_coupledSeedCharge_eq_zero s a m c M ha hm hperiod h32 h27)
    (seedCombination_weightedError_summable s a m c ha0 hm)

/-- Exact completion of the component Gram quadratic, including its mixed term. -/
theorem coupled_component_gram_completion (t : ℝ) :
    (59 : ℝ) / 9 + 2 * (-55 / 18) * t + (1700 / 9) * t ^ 2 =
      (5309 : ℝ) / 816 + (1700 / 9) * (t - 11 / 680) ^ 2 := by
  ring

/-- Exact improvement in the error floor obtained from the coupled functional. -/
theorem coupled_component_bound_gain_exact :
    (272 : ℝ) / 15927 - 1 / 59 = 121 / 939693 := by norm_num

/-- The coupled bound strictly improves the single root-component lower bound. -/
theorem coupled_component_bound_gt_root_bound :
    (1 : ℝ) / 59 < (272 : ℝ) / 15927 := by norm_num

end

end RiemannResearch.RH.CoupledSeedComponentObstruction
