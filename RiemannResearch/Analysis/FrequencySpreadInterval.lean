import RiemannResearch.Analysis.FrequencySensitiveGramBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Sharp interval bounds for the existing weighted Fourier frequency spread

Source: user-supplied Zeta_Zero_Harmonic_Analysis_20261011 (1)(1).md,
Section 9.3. This extends the repository's exact frequency-spread identities
with the sharp half-diameter bound and its retained negative square.
The actual zeta entrywise estimate remains an explicit hypothesis.

Recovery status, 2026-10-11: preserved proof terms prepared for the combined
integration; final server-checkpoint verification remains pending.
-/

open scoped BigOperators

namespace RiemannResearch.Fourier

variable {ι : Type*}

/-- Midpoint second moment without dividing by total mass. -/
theorem frequency_midpointSecondMoment_le
    (s : Finset ι) (w u : ι → ℝ) (A B : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hA : ∀ i ∈ s, A ≤ u i) (hB : ∀ i ∈ s, u i ≤ B) :
    (∑ i ∈ s, w i * (u i - (A + B) / 2) ^ 2) ≤
      (∑ i ∈ s, w i) * ((B - A) ^ 2 / 4) := by
  calc
    (∑ i ∈ s, w i * (u i - (A + B) / 2) ^ 2) ≤
        ∑ i ∈ s, w i * ((B - A) ^ 2 / 4) := by
      apply Finset.sum_le_sum
      intro i hi
      have hprod : 0 ≤ (u i - A) * (B - u i) :=
        mul_nonneg (sub_nonneg.mpr (hA i hi)) (sub_nonneg.mpr (hB i hi))
      have hpoint : (u i - (A + B) / 2) ^ 2 ≤ (B - A) ^ 2 / 4 := by
        nlinarith
      exact mul_le_mul_of_nonneg_left hpoint (hw i hi)
    _ = (∑ i ∈ s, w i) * ((B - A) ^ 2 / 4) := by
      rw [Finset.sum_mul]

/-- Sharp interval estimate retaining the centered first-moment square. -/
theorem weightedFrequencySpread_le_interval_centered
    (s : Finset ι) (w u : ι → ℝ) (A B : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hA : ∀ i ∈ s, A ≤ u i) (hB : ∀ i ∈ s, u i ≤ B) :
    weightedFrequencySpread s w u ≤
      (B - A) ^ 2 * (∑ i ∈ s, w i) ^ 2 / 2 -
        2 * (∑ i ∈ s, w i * (u i - (A + B) / 2)) ^ 2 := by
  have hm : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg hw
  rw [weightedFrequencySpread_eq_centered s w u ((A + B) / 2)]
  calc
    2 * (∑ i ∈ s, w i) * (∑ i ∈ s, w i * (u i - (A + B) / 2) ^ 2) -
        2 * (∑ i ∈ s, w i * (u i - (A + B) / 2)) ^ 2 ≤
      2 * (∑ i ∈ s, w i) * ((∑ i ∈ s, w i) * ((B - A) ^ 2 / 4)) -
        2 * (∑ i ∈ s, w i * (u i - (A + B) / 2)) ^ 2 := by
      exact sub_le_sub_right
        (mul_le_mul_of_nonneg_left
          (frequency_midpointSecondMoment_le s w u A B hw hA hB) (by positivity)) _
    _ = _ := by ring

theorem weightedFrequencySpread_le_half_diameter_sq
    (s : Finset ι) (w u : ι → ℝ) (A B : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hA : ∀ i ∈ s, A ≤ u i) (hB : ∀ i ∈ s, u i ≤ B) :
    weightedFrequencySpread s w u ≤
      (B - A) ^ 2 * (∑ i ∈ s, w i) ^ 2 / 2 := by
  have h := weightedFrequencySpread_le_interval_centered s w u A B hw hA hB
  nlinarith [sq_nonneg (∑ i ∈ s, w i * (u i - (A + B) / 2))]

/-- The full complex Gram remainder inherits the sharp interval improvement.
Its actual arithmetic entrywise estimate is an explicit external hypothesis. -/
theorem finiteGramErrorPairing_norm_le_interval
    (s : Finset ι) (a : ι → ℂ) (R : ι → ι → ℂ) (u : ι → ℝ)
    (η κ A B : ℝ) (hκ : 0 ≤ κ)
    (hA : ∀ i ∈ s, A ≤ u i) (hB : ∀ i ∈ s, u i ≤ B)
    (hR : ∀ i ∈ s, ∀ j ∈ s, ‖R i j‖ ≤ η + κ * (u i - u j) ^ 2) :
    ‖finiteGramErrorPairing s a R‖ ≤
      η * (∑ i ∈ s, ‖a i‖) ^ 2 +
        κ * ((B - A) ^ 2 * (∑ i ∈ s, ‖a i‖) ^ 2 / 2 -
          2 * (∑ i ∈ s, ‖a i‖ * (u i - (A + B) / 2)) ^ 2) := by
  exact (finiteGramErrorPairing_norm_le_frequencySpread s a R u η κ hR).trans
    (add_le_add (le_refl (η * (∑ i ∈ s, ‖a i‖) ^ 2))
      (mul_le_mul_of_nonneg_left
        (weightedFrequencySpread_le_interval_centered s (fun i => ‖a i‖) u A B
          (fun i _ => norm_nonneg _) hA hB) hκ))

end RiemannResearch.Fourier
