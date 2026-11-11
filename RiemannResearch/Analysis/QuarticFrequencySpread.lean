import RiemannResearch.Analysis.FrequencySensitiveGramBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
Exact fourth-order frequency dispersion, extending the existing second-order
identity. For prime support with weights |a_p|² this is the FRZ identity
J₄ = 2 E M₄ + 6 V². No sign or positivity premise is needed for the algebra.
-/

open scoped BigOperators
namespace RiemannResearch.Fourier

def weightedFourthFrequencySpread {ι : Type*} (s : Finset ι) (w u : ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, w i * w j * (u i - u j) ^ 4

theorem weightedFourthFrequencySpread_eq {ι : Type*}
    (s : Finset ι) (w u : ι → ℝ) :
    weightedFourthFrequencySpread s w u =
      2 * (∑ i ∈ s, w i) * (∑ i ∈ s, w i * u i ^ 4) -
      8 * (∑ i ∈ s, w i * u i) * (∑ i ∈ s, w i * u i ^ 3) +
      6 * (∑ i ∈ s, w i * u i ^ 2) ^ 2 := by
  unfold weightedFourthFrequencySpread
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s,
        ((w i * u i ^ 4) * w j -
         (4 * (w i * u i ^ 3)) * (w j * u j) +
         (6 * (w i * u i ^ 2)) * (w j * u j ^ 2) -
         (4 * (w i * u i)) * (w j * u j ^ 3) +
         w i * (w j * u j ^ 4)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul]
      ring

theorem weightedFourthFrequencySpread_shift {ι : Type*}
    (s : Finset ι) (w u : ι → ℝ) (c : ℝ) :
    weightedFourthFrequencySpread s w (fun i => u i - c) =
      weightedFourthFrequencySpread s w u := by
  unfold weightedFourthFrequencySpread
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem weightedFourthFrequencySpread_eq_centered {ι : Type*}
    (s : Finset ι) (w u : ι → ℝ) (c : ℝ)
    (hc : (∑ i ∈ s, w i * (u i - c)) = 0) :
    weightedFourthFrequencySpread s w u =
      2 * (∑ i ∈ s, w i) * (∑ i ∈ s, w i * (u i - c) ^ 4) +
      6 * (∑ i ∈ s, w i * (u i - c) ^ 2) ^ 2 := by
  rw [← weightedFourthFrequencySpread_shift s w u c,
    weightedFourthFrequencySpread_eq, hc]
  ring

theorem weighted_center_sum_zero {ι : Type*}
    (s : Finset ι) (w u : ι → ℝ) (hE : (∑ i ∈ s, w i) ≠ 0) :
    ∑ i ∈ s, w i * (u i - (∑ j ∈ s, w j * u j) / (∑ j ∈ s, w j)) = 0 := by
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  field_simp
  ring

/-- Fourth spread is at most the squared diameter times the second spread. -/
theorem weightedFourthFrequencySpread_le_second {ι : Type*}
    (s : Finset ι) (w u : ι → ℝ) (D : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hD : ∀ i ∈ s, ∀ j ∈ s, (u i - u j) ^ 2 ≤ D ^ 2) :
    weightedFourthFrequencySpread s w u ≤ D ^ 2 * weightedFrequencySpread s w u := by
  unfold weightedFourthFrequencySpread weightedFrequencySpread
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have h := mul_le_mul_of_nonneg_right (hD i hi j hj) (sq_nonneg (u i - u j))
  have h' := mul_le_mul_of_nonneg_left h (mul_nonneg (hw i hi) (hw j hj))
  nlinarith only [h']

/-- Sharp universal fourth-dispersion bound on an interval. The constant 1/2
improves the diameter-only bound in FRZ (13); equal endpoint masses attain it. -/
theorem weightedFourthFrequencySpread_le_half_diameter {ι : Type*}
    (s : Finset ι) (w u : ι → ℝ) (L U : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hu : ∀ i ∈ s, L ≤ u i ∧ u i ≤ U) :
    weightedFourthFrequencySpread s w u ≤
      (U - L) ^ 4 * (∑ i ∈ s, w i) ^ 2 / 2 := by
  have hE : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg hw
  have hpair : ∀ i ∈ s, ∀ j ∈ s, (u i - u j) ^ 2 ≤ (U - L) ^ 2 := by
    intro i hi j hj
    have h := mul_nonneg
      (show 0 ≤ (U - L) - (u i - u j) by linarith [(hu i hi).2, (hu j hj).1])
      (show 0 ≤ (U - L) + (u i - u j) by linarith [(hu i hi).1, (hu j hj).2])
    nlinarith only [h]
  have hmid : ∀ i ∈ s, (u i - (L + U) / 2) ^ 2 ≤ (U - L) ^ 2 / 4 := by
    intro i hi
    have h := mul_nonneg (sub_nonneg.mpr (hu i hi).1) (sub_nonneg.mpr (hu i hi).2)
    nlinarith only [h]
  have hmoment : (∑ i ∈ s, w i * (u i - (L + U) / 2) ^ 2) ≤
      (U - L) ^ 2 / 4 * (∑ i ∈ s, w i) := by
    calc
      _ ≤ ∑ i ∈ s, w i * ((U - L) ^ 2 / 4) :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hmid i hi) (hw i hi)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hquad : weightedFrequencySpread s w u ≤
      (U - L) ^ 2 * (∑ i ∈ s, w i) ^ 2 / 2 := by
    have h := weightedFrequencySpread_le_centered s w u ((L + U) / 2)
    have hm := mul_le_mul_of_nonneg_left hmoment (show 0 ≤ 2 * (∑ i ∈ s, w i) by positivity)
    nlinarith only [h, hm]
  have hfour := weightedFourthFrequencySpread_le_second s w u (U - L) hw hpair
  have h := mul_le_mul_of_nonneg_left hquad (sq_nonneg (U - L))
  nlinarith only [hfour, h]

/-- Equal weights on two endpoints attain the preceding constant. -/
theorem weightedFourthFrequencySpread_two_points (L U : ℝ) :
    weightedFourthFrequencySpread (Finset.univ : Finset Bool)
      (fun _ => 1) (fun b => if b then U else L) = 2 * (U - L) ^ 4 := by
  simp [weightedFourthFrequencySpread]
  ring

end RiemannResearch.Fourier
