import RiemannResearch.RH.PositiveSeedCone

/-!
# Coupled signed prime defects and omitted-prime obstructions

The common error coordinate at 1 couples the defects at 5 and 7.  The exact
completion below retains that coupling, the five original Pareto weights,
and every square remainder.  No coefficient positivity is assumed.
-/

namespace RiemannResearch.RH.PrimeDefectEnergy

open scoped BigOperators
open PositiveSeedCone

noncomputable section

/-- Inverse-Gram energy of the two actual prime defects. -/
def jointDefectEnergy (u v : ℝ) : ℝ :=
  (25 * u ^ 2 - u * v + 13 * v ^ 2) / 1299

/-- The five-coordinate residual after the two defect constraints are removed. -/
def jointCenteredError (F : ℕ → ℝ) : ℝ :=
  let u := 1 + defectFive F
  let v := 1 + defectSeven F
  (1 - F 1 - (49 * u + 25 * v) / 1299) ^ 2 / 2 +
  (1 - F 4 - (500 * u - 10 * v) / 1299) ^ 2 / 20 +
  (1 - F 5 + (750 * u - 15 * v) / 1299) ^ 2 / 30 +
  (1 - F 6 - (-21 * u + 546 * v) / 1299) ^ 2 / 42 +
  (1 - F 7 + (-28 * u + 728 * v) / 1299) ^ 2 / 56

/-- Exact joint extraction; in particular the signed mixed term is preserved. -/
theorem finiteError_joint_completion (F : ℕ → ℝ) :
    finiteError F =
      jointDefectEnergy (1 + defectFive F) (1 + defectSeven F) +
        jointCenteredError F := by
  unfold finiteError jointDefectEnergy jointCenteredError defectFive defectSeven
  ring

theorem jointCenteredError_nonneg (F : ℕ → ℝ) :
    0 ≤ jointCenteredError F := by
  unfold jointCenteredError
  positivity

/-- The exact conditional prime-seven decomposition of the coupled energy. -/
theorem jointDefectEnergy_pivot_seven (u v : ℝ) :
    jointDefectEnergy u v = v ^ 2 / 100 +
      (25 / 1299) * (u - v / 50) ^ 2 := by
  unfold jointDefectEnergy
  ring

/-- The corresponding conditional prime-five decomposition. -/
theorem jointDefectEnergy_pivot_five (u v : ℝ) :
    jointDefectEnergy u v = u ^ 2 / 52 +
      (13 / 1299) * (v - u / 26) ^ 2 := by
  unfold jointDefectEnergy
  ring

theorem fullError_joint_forcedMass (F : ℕ → ℝ)
    (hsum : Summable (weightedError F)) :
    jointDefectEnergy (1 + defectFive F) (1 + defectSeven F) ≤
      ∑' k : ℕ, weightedError F k := by
  have hfinite : jointDefectEnergy (1 + defectFive F) (1 + defectSeven F) ≤
      finiteError F := by
    rw [finiteError_joint_completion]
    exact le_add_of_nonneg_right (jointCenteredError_nonneg F)
  calc
    jointDefectEnergy (1 + defectFive F) (1 + defectSeven F) ≤ finiteError F := hfinite
    _ = ∑ k ∈ ({0, 3, 4, 5, 6} : Finset ℕ), weightedError F k := finiteError_eq_sum F
    _ ≤ ∑' k : ℕ, weightedError F k :=
      hsum.sum_le_tsum _ (fun k _ => weightedError_nonneg F k)

/-- Both arithmetic coefficient masses enter one bound with their exact coupling. -/
theorem signed_seed_joint_forcedMass {ι : Type*} (s : Finset ι)
    (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i) :
    jointDefectEnergy
      (1 + ∑ i ∈ s, c i * (if m i = 5 then 5 else 0))
      (1 + ∑ i ∈ s, c i * (if m i = 7 then 7 else 0)) ≤
      ∑' k : ℕ, weightedError (seedCombination s a m c) k := by
  have ha0 : ∀ i ∈ s, 0 < a i := by
    intro i hi
    rcases ha i hi with h | h <;> omega
  have hs := seedCombination_weightedError_summable s a m c ha0 hm
  have hl := fullError_joint_forcedMass (seedCombination s a m c) hs
  obtain ⟨h5, h7⟩ := seedCombination_defects_exact s a m c ha hm
  rw [h5, h7] at hl
  exact hl

theorem fullError_primeSeven_forcedMass (F : ℕ → ℝ)
    (hsum : Summable (weightedError F)) :
    (1 + defectSeven F) ^ 2 / 100 ≤ ∑' k : ℕ, weightedError F k := by
  have hl := fullError_joint_forcedMass F hsum
  rw [jointDefectEnergy_pivot_seven] at hl
  have hn : 0 ≤ (25 : ℝ) / 1299 *
      ((1 + defectFive F) - (1 + defectSeven F) / 50) ^ 2 := by positivity
  linarith

theorem signed_seed_primeSeven_forcedMass {ι : Type*} (s : Finset ι)
    (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i) :
    (1 + ∑ i ∈ s, c i * (if m i = 7 then 7 else 0)) ^ 2 / 100 ≤
      ∑' k : ℕ, weightedError (seedCombination s a m c) k := by
  have ha0 : ∀ i ∈ s, 0 < a i := by
    intro i hi
    rcases ha i hi with h | h <;> omega
  have hs := seedCombination_weightedError_summable s a m c ha0 hm
  have hl := fullError_primeSeven_forcedMass (seedCombination s a m c) hs
  rw [(seedCombination_defects_exact s a m c ha hm).2] at hl
  exact hl

/-- If 7 is absent from the conductor, the actual signed defect is exactly zero. -/
theorem seedCombination_defectSeven_eq_zero_of_not_dvd {ι : Type*}
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ) (M : ℕ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i)
    (hperiod : ∀ i ∈ s, a i * m i ∣ M) (h7 : ¬ 7 ∣ M) :
    defectSeven (seedCombination s a m c) = 0 := by
  rw [(seedCombination_defects_exact s a m c ha hm).2]
  apply Finset.sum_eq_zero
  intro i hi
  have hmi : m i ≠ 7 := by
    intro hm7
    apply h7
    apply dvd_trans _ (hperiod i hi)
    exact ⟨a i, by rw [hm7]; omega⟩
  simp [hmi]

/-- A whole signed conductor space omitting 7 remains at distance at least 1/100. -/
theorem conductor_omitting_seven_fullError_lower {ι : Type*}
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ) (M : ℕ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i)
    (hperiod : ∀ i ∈ s, a i * m i ∣ M) (h7 : ¬ 7 ∣ M) :
    (1 : ℝ) / 100 ≤ ∑' k : ℕ, weightedError (seedCombination s a m c) k := by
  have ha0 : ∀ i ∈ s, 0 < a i := by
    intro i hi
    rcases ha i hi with h | h <;> omega
  have hs := seedCombination_weightedError_summable s a m c ha0 hm
  have hl := fullError_primeSeven_forcedMass (seedCombination s a m c) hs
  rw [seedCombination_defectSeven_eq_zero_of_not_dvd s a m c M ha hm hperiod h7] at hl
  simpa using hl

/-- Low full error forces negative aggregate coefficient mass at dilation 7. -/
theorem signed_seed_primeSeven_mass_negative {ι : Type*} (s : Finset ι)
    (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i)
    (herr : (∑' k : ℕ, weightedError (seedCombination s a m c) k) < 1 / 100) :
    (∑ i ∈ s, c i * (if m i = 7 then 7 else 0)) < 0 := by
  have hl := signed_seed_primeSeven_forcedMass s a m c ha hm
  nlinarith [sq_nonneg (∑ i ∈ s, c i * (if m i = 7 then 7 else 0))]

end

end RiemannResearch.RH.PrimeDefectEnergy
