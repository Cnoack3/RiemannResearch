import RiemannResearch.RH.PositiveSeedCone
import RiemannResearch.RH.ThresholdPrimeFiveInfinite360

/-!
# A signed obstruction when both seed valuations are at most one

If a conductor is divisible by neither 4 nor 9, all legal two-seed
generators satisfy the same four-coordinate identity. This includes every
squarefree conductor, however many other primes it contains. The obstruction
holds for arbitrary signed coefficients and the full infinite Pareto error.
-/

namespace RiemannResearch.RH.SquarefreeConductorObstruction

open scoped BigOperators
open PositiveSeedCone TwoSeedThreshold

noncomputable section

/-- The finite component-charge functional for the seed orbit `{1,2,3,6}`. -/
def seedCharge (F : ℕ → ℝ) : ℝ := F 2 + F 3 - F 5 + F 6

/-- All four coordinates with their actual Pareto weights. -/
def seedChargeError (F : ℕ → ℝ) : ℝ :=
  (1 - F 2) ^ 2 / 6 + (1 - F 3) ^ 2 / 12 +
  (1 - F 5) ^ 2 / 30 + (1 - F 6) ^ 2 / 42

def seedChargeCenteredError (F : ℕ → ℝ) : ℝ :=
  let u := 2 - seedCharge F
  (1 - F 2 - u / 15) ^ 2 / 6 +
  (1 - F 3 - 2 * u / 15) ^ 2 / 12 +
  (1 - F 5 + u / 3) ^ 2 / 30 +
  (1 - F 6 - 7 * u / 15) ^ 2 / 42

/-- Exact extraction before any nonnegative term is discarded. -/
theorem seedChargeError_completion (F : ℕ → ℝ) :
    seedChargeError F = (2 - seedCharge F) ^ 2 / 90 +
      seedChargeCenteredError F := by
  unfold seedChargeError seedChargeCenteredError seedCharge
  ring

theorem seedChargeCenteredError_nonneg (F : ℕ → ℝ) :
    0 ≤ seedChargeCenteredError F := by
  unfold seedChargeCenteredError
  positivity

theorem seedChargeError_eq_sum (F : ℕ → ℝ) :
    seedChargeError F =
      ∑ k ∈ ({1, 2, 4, 5} : Finset ℕ), weightedError F k := by
  norm_num [seedChargeError, weightedError, Pareto.positiveWeight] <;> ring

theorem fullError_seedCharge_lower (F : ℕ → ℝ)
    (hsum : Summable (weightedError F)) :
    (2 - seedCharge F) ^ 2 / 90 ≤ ∑' k : ℕ, weightedError F k := by
  have hfinite : (2 - seedCharge F) ^ 2 / 90 ≤ seedChargeError F := by
    rw [seedChargeError_completion]
    exact le_add_of_nonneg_right (seedChargeCenteredError_nonneg F)
  calc
    (2 - seedCharge F) ^ 2 / 90 ≤ seedChargeError F := hfinite
    _ = ∑ k ∈ ({1, 2, 4, 5} : Finset ℕ), weightedError F k := seedChargeError_eq_sum F
    _ ≤ ∑' k : ℕ, weightedError F k :=
      hsum.sum_le_tsum _ (fun k _ => weightedError_nonneg F k)

/-- Actual arithmetic identity for every positive legal dilation with these endpoint constraints. -/
theorem generator_seedCharge_eq_zero (a m : ℕ)
    (ha : a = 2 ∨ a = 3) (hm : 0 < m)
    (h4 : ¬ 4 ∣ a * m) (h9 : ¬ 9 ∣ a * m) :
    seedCharge (certificateGenerator a m) = 0 := by
  by_cases hm6 : m ≤ 6
  · rcases ha with rfl | rfl
    all_goals
      interval_cases m <;>
        norm_num [seedCharge, certificateGenerator] at *
  · have hmlarge : 6 < m := by omega
    have ha1 : 1 ≤ a := by rcases ha with rfl | rfl <;> omega
    have hg (k : ℕ) (hk : k ≤ 6) : certificateGenerator a m k = 0 := by
      have hkm : k < m := by omega
      have hkam : k < a * m := by nlinarith
      simp only [certificateGenerator, Nat.mod_eq_of_lt hkm,
        Nat.mod_eq_of_lt hkam, sub_self]
    simp only [seedCharge, hg 2 (by omega), hg 3 (by omega),
      hg 5 (by omega), hg 6 (by omega)]
    ring

theorem seedCharge_seedCombination {ι : Type*} (s : Finset ι)
    (a m : ι → ℕ) (c : ι → ℝ) :
    seedCharge (seedCombination s a m c) =
      ∑ i ∈ s, c i * seedCharge (certificateGenerator (a i) (m i)) := by
  simp only [seedCharge, seedCombination, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Adding any number of other primes cannot change this component identity. -/
theorem seedCombination_seedCharge_eq_zero {ι : Type*}
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ) (M : ℕ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i)
    (hperiod : ∀ i ∈ s, a i * m i ∣ M)
    (h4 : ¬ 4 ∣ M) (h9 : ¬ 9 ∣ M) :
    seedCharge (seedCombination s a m c) = 0 := by
  rw [seedCharge_seedCombination]
  apply Finset.sum_eq_zero
  intro i hi
  have h4i : ¬ 4 ∣ a i * m i := fun h => h4 (dvd_trans h (hperiod i hi))
  have h9i : ¬ 9 ∣ a i * m i := fun h => h9 (dvd_trans h (hperiod i hi))
  rw [generator_seedCharge_eq_zero (a i) (m i) (ha i hi) (hm i hi) h4i h9i,
    mul_zero]

/-- Uniform full error obstruction; no coefficient sign or conductor size restriction. -/
theorem conductor_seedValuations_fullError_lower {ι : Type*}
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ) (M : ℕ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i)
    (hperiod : ∀ i ∈ s, a i * m i ∣ M)
    (h4 : ¬ 4 ∣ M) (h9 : ¬ 9 ∣ M) :
    (2 : ℝ) / 45 ≤ ∑' k : ℕ, weightedError (seedCombination s a m c) k := by
  have ha0 : ∀ i ∈ s, 0 < a i := by
    intro i hi
    rcases ha i hi with h | h <;> omega
  have hs := seedCombination_weightedError_summable s a m c ha0 hm
  have hl := fullError_seedCharge_lower (seedCombination s a m c) hs
  rw [seedCombination_seedCharge_eq_zero s a m c M ha hm hperiod h4 h9] at hl
  norm_num at hl
  exact hl

/-- The already certified period-360 witness beats this entire infinite family. -/
theorem legalWitness360_beats_conductors_with_small_seedValuations {ι : Type*}
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ) (M : ℕ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i)
    (hperiod : ∀ i ∈ s, a i * m i ∣ M)
    (h4 : ¬ 4 ∣ M) (h9 : ¬ 9 ∣ M) :
    (∑' k : ℕ, weightedError legalWitness360 k) + 1 / 2250 <
      ∑' k : ℕ, weightedError (seedCombination s a m c) k := by
  have hu : (∑' k : ℕ, weightedError legalWitness360 k) < (11 : ℝ) / 250 :=
    legalWitness360_full_error_lt
  have hl := conductor_seedValuations_fullError_lower s a m c M ha hm hperiod h4 h9
  linarith

end

end RiemannResearch.RH.SquarefreeConductorObstruction
