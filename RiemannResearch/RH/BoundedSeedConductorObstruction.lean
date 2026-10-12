import Mathlib.Algebra.BigOperators.Field
import RiemannResearch.RH.PositiveSeedCone
import RiemannResearch.LinearAlgebra.WeightedDualCertificate
import Mathlib.Tactic.FinCases

/-!
# A fixed error floor when the seed exponents are bounded by 3 and 2

The condition is `16 ∤ M` and `27 ∤ M`; powers of every other prime remain
unrestricted. A finite actual-generator annihilator and its exact weighted
dual value prove the complete signed error bound `2/95`.
-/

namespace RiemannResearch.RH.BoundedSeedConductorObstruction

open scoped BigOperators
open PositiveSeedCone TwoSeedThreshold
open RiemannResearch.LinearAlgebra

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

private def chargeCoordinate : Fin 19 → ℕ :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 17, 18, 23, 24, 35, 36, 71, 72]

private def chargeNumerator : Fin 19 → ℤ :=
  ![12, 4, 2, 6, -4, 4, -6, 2, 4, -2, 2, -2, 2, -2, 2, -1, 1, -1, 1]

/-- Seventy-two times the finite root-component divergence functional. -/
def boundedSeedCharge (F : ℕ → ℝ) : ℝ :=
  ∑ r : Fin 19, (chargeNumerator r : ℝ) * F (chargeCoordinate r)

private def chargeWeight (r : Fin 19) : ℝ :=
  Pareto.positiveWeight (chargeCoordinate r)

private def chargeDual (r : Fin 19) : ℝ := (chargeNumerator r : ℝ) / 1140

private theorem chargeWeight_pos (r : Fin 19) : 0 < chargeWeight r := by
  fin_cases r <;> norm_num [chargeWeight, chargeCoordinate, Pareto.positiveWeight]

private theorem generator_integer_charge_eq_zero (a m : ℕ)
    (ha : a = 2 ∨ a = 3) (hm : 0 < m)
    (h16 : ¬ 16 ∣ a * m) (h27 : ¬ 27 ∣ a * m) :
    (∑ r : Fin 19, chargeNumerator r *
      (((chargeCoordinate r % (a*m) : ℕ) : ℤ) -
        ((chargeCoordinate r % m : ℕ) : ℤ))) = 0 := by
  by_cases hm72 : m ≤ 72
  · rcases ha with rfl | rfl
    all_goals interval_cases m <;> norm_num at *
    all_goals decide
  · have hmlarge : 72 < m := by omega
    have ha1 : 1 ≤ a := by rcases ha with rfl | rfl <;> omega
    apply Finset.sum_eq_zero
    intro r _
    have hr : chargeCoordinate r ≤ 72 := by
      fin_cases r <;> norm_num [chargeCoordinate]
    have hkm : chargeCoordinate r < m := by omega
    have hkam : chargeCoordinate r < a * m := by nlinarith
    rw [Nat.mod_eq_of_lt hkm, Nat.mod_eq_of_lt hkam]
    ring

/-- Exact arithmetic annihilation, uniform over every positive legal dilation. -/
theorem generator_boundedSeedCharge_eq_zero (a m : ℕ)
    (ha : a = 2 ∨ a = 3) (hm : 0 < m)
    (h16 : ¬ 16 ∣ a * m) (h27 : ¬ 27 ∣ a * m) :
    boundedSeedCharge (certificateGenerator a m) = 0 := by
  have hi := generator_integer_charge_eq_zero a m ha hm h16 h27
  unfold boundedSeedCharge
  simp only [certificateGenerator]
  exact_mod_cast hi

/-- Exact weighted dual value; every signed coordinate contributes. -/
private theorem chargeDual_value :
    (∑ r : Fin 19, (2 * chargeDual r - (chargeDual r)^2 / chargeWeight r)) =
      (2 : ℝ) / 95 := by
  norm_num [Fin.sum_univ_succ, chargeDual, chargeNumerator,
    chargeWeight, chargeCoordinate, Pareto.positiveWeight]

theorem boundedSeedCharge_seedCombination {ι : Type*} (s : Finset ι)
    (a m : ι → ℕ) (c : ι → ℝ) :
    boundedSeedCharge (seedCombination s a m c) =
      ∑ i ∈ s, c i * boundedSeedCharge (certificateGenerator (a i) (m i)) := by
  unfold boundedSeedCharge seedCombination
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem seedCombination_boundedSeedCharge_eq_zero {ι : Type*}
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ) (M : ℕ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i)
    (hperiod : ∀ i ∈ s, a i * m i ∣ M)
    (h16 : ¬ 16 ∣ M) (h27 : ¬ 27 ∣ M) :
    boundedSeedCharge (seedCombination s a m c) = 0 := by
  rw [boundedSeedCharge_seedCombination]
  apply Finset.sum_eq_zero
  intro i hi
  have h16i : ¬ 16 ∣ a i * m i := fun h => h16 (dvd_trans h (hperiod i hi))
  have h27i : ¬ 27 ∣ a i * m i := fun h => h27 (dvd_trans h (hperiod i hi))
  rw [generator_boundedSeedCharge_eq_zero (a i) (m i) (ha i hi) (hm i hi)
    h16i h27i, mul_zero]

/-- The finite weighted error retained by the dual certificate. -/
def boundedSeedFiniteError (F : ℕ → ℝ) : ℝ :=
  ∑ r : Fin 19, chargeWeight r * (1 - F (chargeCoordinate r)) ^ 2

private theorem chargeDual_annihilates (F : ℕ → ℝ)
    (hF : boundedSeedCharge F = 0) :
    (∑ r : Fin 19, chargeDual r * F (chargeCoordinate r)) = 0 := by
  calc
    _ = boundedSeedCharge F / 1140 := by
      simp only [chargeDual, boundedSeedCharge, div_mul_eq_mul_div, Finset.sum_div]
    _ = 0 := by rw [hF]; norm_num

/-- The exact square remainder in the finite weighted dual identity. -/
theorem boundedSeedFiniteError_exact (F : ℕ → ℝ)
    (hF : boundedSeedCharge F = 0) :
    boundedSeedFiniteError F = (2 : ℝ) / 95 +
      ∑ r : Fin 19, chargeWeight r *
        (1 - F (chargeCoordinate r) - chargeDual r / chargeWeight r) ^ 2 := by
  unfold boundedSeedFiniteError
  rw [weighted_error_dual_exact chargeWeight chargeDual
    (fun r => F (chargeCoordinate r)) chargeWeight_pos (chargeDual_annihilates F hF)]
  rw [chargeDual_value]

private theorem boundedSeedFiniteError_lower (F : ℕ → ℝ)
    (hF : boundedSeedCharge F = 0) :
    (2 : ℝ) / 95 ≤ boundedSeedFiniteError F := by
  have hl := weighted_error_lower_of_dual chargeWeight chargeDual
    (fun r => F (chargeCoordinate r)) chargeWeight_pos (chargeDual_annihilates F hF)
  rw [chargeDual_value] at hl
  exact hl

private theorem boundedSeedFiniteError_eq_sum (F : ℕ → ℝ) :
    boundedSeedFiniteError F =
      ∑ k ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 16, 17, 22, 23, 34, 35, 70, 71} : Finset ℕ),
        weightedError F k := by
  norm_num [boundedSeedFiniteError, Fin.sum_univ_succ, chargeWeight,
    chargeCoordinate, weightedError, Pareto.positiveWeight] <;> ring

/-- Complete infinite error bound from the actual finite arithmetic annihilator. -/
theorem fullError_boundedSeedCharge_lower (F : ℕ → ℝ)
    (hF : boundedSeedCharge F = 0) (hsum : Summable (weightedError F)) :
    (2 : ℝ) / 95 ≤ ∑' k : ℕ, weightedError F k := by
  calc
    (2 : ℝ) / 95 ≤ boundedSeedFiniteError F := boundedSeedFiniteError_lower F hF
    _ = ∑ k ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 16, 17, 22, 23, 34, 35, 70, 71} : Finset ℕ),
          weightedError F k := boundedSeedFiniteError_eq_sum F
    _ ≤ ∑' k : ℕ, weightedError F k :=
      hsum.sum_le_tsum _ (fun k _ => weightedError_nonneg F k)

/-- Arbitrary primes and their powers cannot remove this fixed seed-grid obstruction. -/
theorem conductor_seedCaps_three_two_fullError_lower {ι : Type*}
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ) (M : ℕ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i)
    (hperiod : ∀ i ∈ s, a i * m i ∣ M)
    (h16 : ¬ 16 ∣ M) (h27 : ¬ 27 ∣ M) :
    (2 : ℝ) / 95 ≤ ∑' k : ℕ, weightedError (seedCombination s a m c) k := by
  have ha0 : ∀ i ∈ s, 0 < a i := by
    intro i hi
    rcases ha i hi with h | h <;> omega
  exact fullError_boundedSeedCharge_lower _
    (seedCombination_boundedSeedCharge_eq_zero s a m c M ha hm hperiod h16 h27)
    (seedCombination_weightedError_summable s a m c ha0 hm)

end

end RiemannResearch.RH.BoundedSeedConductorObstruction
