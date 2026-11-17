import RiemannResearch.NumberTheory.DivisorReturnCoordinates
import RiemannResearch.Analysis.FiniteWeightedVariance
import RiemannResearch.Analysis.FinitePeriodicCancellation

/-!
# Return sampling centered on the units, with its exact bias retained

Source: correction of Hypothesis 14.9 and Remark 14.10 in Christian Noack,
`sdf_modified.pdf`, 21 July 2026. Uniform coprime residues, not the whole
residue group, are the reference distribution. The periodic boundary
estimate below is unconditional; it gives no modulus-uniform power saving
on short shells. Real observables cover the real and imaginary parts of
additive characters separately.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.NumberTheory.UnitCenteredReturnSampling
open DivisorReturnCoordinates
open RiemannResearch.Analysis.FinitePeriodicCancellation
open RiemannResearch.Analysis.FiniteWeightedVariance

def unitResidues (Q : ℕ) : Finset ℕ :=
  (Finset.range Q).filter (fun n => Nat.Coprime n Q)

def average (s : Finset ℕ) (f : ℕ → ℝ) : ℝ := (∑ n ∈ s, f n) / s.card

def unitMean (Q : ℕ) (f : ℕ → ℝ) : ℝ := average (unitResidues Q) f

def unitVariance (Q : ℕ) (f : ℕ → ℝ) : ℝ :=
  unitMean Q (fun n => (f n - unitMean Q f) ^ 2)

theorem unitResidues_nonempty (Q : ℕ) (hQ : 0 < Q) : (unitResidues Q).Nonempty := by
  by_cases h : Q = 1
  · subst Q
    exact ⟨0, by simp [unitResidues]⟩
  · exact ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by simp⟩⟩

theorem unit_card_ne_zero (Q : ℕ) (hQ : 0 < Q) :
    ((unitResidues Q).card : ℝ) ≠ 0 := by
  exact_mod_cast (Finset.card_ne_zero.mpr (unitResidues_nonempty Q hQ))

theorem unit_centered_sum (Q : ℕ) (hQ : 0 < Q) (f : ℕ → ℝ) :
    (∑ n ∈ unitResidues Q, (f n - unitMean Q f)) = 0 := by
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  simp [unitMean, average, mul_div_cancel₀ _ (unit_card_ne_zero Q hQ)]

/-- Exact unit variance plus the deterministic shift from any proposed center. -/
theorem unit_second_moment (Q : ℕ) (hQ : 0 < Q) (f : ℕ → ℝ) (a : ℝ) :
    unitMean Q (fun n => (f n - a) ^ 2) =
      unitVariance Q f + (unitMean Q f - a) ^ 2 := by
  have h := translation_energy (unitResidues Q) (fun _ => 1) f (-a)
    (by simpa [mass] using unit_card_ne_zero Q hQ)
  have hm : mean (unitResidues Q) (fun _ => 1) f = unitMean Q f := by
    simp [mean, mass, unitMean, average]
  simp only [one_mul, hm] at h
  have he : (∑ n ∈ unitResidues Q, (f n - a) ^ 2) =
      (∑ n ∈ unitResidues Q, (f n - unitMean Q f) ^ 2) +
        (unitResidues Q).card * (unitMean Q f - a) ^ 2 := by
    simpa [variance, hm, mass, sub_eq_add_neg] using h
  unfold unitVariance unitMean average
  rw [he, add_div, mul_div_cancel_left₀ _ (unit_card_ne_zero Q hQ)]
  rfl

/-- Exact transfer, including the signed sampling correction and unit/Haar bias. -/
theorem sample_second_moment_exact (Q : ℕ) (hQ : 0 < Q)
    (s : Finset ℕ) (f : ℕ → ℝ) (a : ℝ) :
    average s (fun n => (f n - a) ^ 2) =
      unitVariance Q f + (unitMean Q f - a) ^ 2 +
        (average s (fun n => (f n - a) ^ 2) -
          unitMean Q (fun n => (f n - a) ^ 2)) := by
  rw [unit_second_moment Q hQ]
  ring

/-- A valid replacement for the informal mean-square transfer in Remark 14.10. -/
theorem sample_second_moment_le (Q : ℕ) (hQ : 0 < Q)
    (s : Finset ℕ) (f : ℕ → ℝ) (a δ : ℝ)
    (hδ : |average s (fun n => (f n - a) ^ 2) -
      unitMean Q (fun n => (f n - a) ^ 2)| ≤ δ) :
    average s (fun n => (f n - a) ^ 2) ≤
      unitVariance Q f + (unitMean Q f - a) ^ 2 + δ := by
  rw [sample_second_moment_exact Q hQ s f a]
  exact add_le_add le_rfl (le_trans (le_abs_self _) hδ)

/-- Restriction of a nonnegative Haar moment to units costs Q divided by the unit count. -/
theorem unit_second_moment_le_haar (Q : ℕ) (hQ : 0 < Q) (f : ℕ → ℝ) :
    unitMean Q (fun n => f n ^ 2) ≤
      ((Q : ℝ) / (unitResidues Q).card) *
        average (Finset.range Q) (fun n => f n ^ 2) := by
  have hs : (∑ n ∈ unitResidues Q, f n ^ 2) ≤ ∑ n ∈ Finset.range Q, f n ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
      (fun n _ _ => sq_nonneg _)
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hc : (0 : ℝ) ≤ (unitResidues Q).card := by positivity
  calc
    _ ≤ (∑ n ∈ Finset.range Q, f n ^ 2) / (unitResidues Q).card :=
      div_le_div_of_nonneg_right hs hc
    _ = _ := by
      simp only [average, Finset.card_range]
      field_simp

/-- The parity bias is absorbed by the correct reference mean, exactly. -/
theorem unitMean_parity (Q : ℕ) (hQ : 0 < Q) (heven : 2 ∣ Q) :
    unitMean Q parityCharacter = -1 := by
  unfold unitMean average
  rw [parity_return_sum Q (unitResidues Q) heven
    (fun n hn => (Finset.mem_filter.mp hn).2)]
  simp [unit_card_ne_zero Q hQ]

theorem parity_centered_return_sum (Q : ℕ) (hQ : 0 < Q) (heven : 2 ∣ Q)
    (s : Finset ℕ) (hs : ∀ n ∈ s, Nat.Coprime n Q) :
    (∑ n ∈ s, (parityCharacter n - unitMean Q parityCharacter)) = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  rw [parityCharacter_coprime_even Q n heven (hs n hn), unitMean_parity Q hQ heven]
  ring

/-- The actual coprime-residue observable, with the unit reference subtracted. -/
def centeredUnitSignal (Q : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  if Nat.Coprime (n % Q) Q then f (n % Q) - unitMean Q f else 0

theorem centeredUnitSignal_periodic (Q : ℕ) (f : ℕ → ℝ) (n : ℕ) :
    centeredUnitSignal Q f (n + Q) = centeredUnitSignal Q f n := by
  simp [centeredUnitSignal]

theorem centeredUnitSignal_period_sum (Q : ℕ) (hQ : 0 < Q) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range Q, centeredUnitSignal Q f i) = 0 := by
  have he : (∑ i ∈ Finset.range Q, centeredUnitSignal Q f i) =
      ∑ i ∈ unitResidues Q, (f i - unitMean Q f) := by
    rw [unitResidues, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    simp [centeredUnitSignal, Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]
  rw [he, unit_centered_sum Q hQ]

/-- Unconditional cancellation of the corrected return observable on complete periods. -/
theorem unit_return_interval_exact (Q : ℕ) (hQ : 0 < Q) (f : ℕ → ℝ)
    (a k r : ℕ) :
    (∑ i ∈ Finset.range (k * Q + r), centeredUnitSignal Q f (a + i)) =
      ∑ i ∈ Finset.range r, centeredUnitSignal Q f (a + k * Q + i) :=
  centered_interval_exact Q _ (centeredUnitSignal_periodic Q f)
    (centeredUnitSignal_period_sum Q hQ f) a k r

theorem coprime_mod_iff (n Q : ℕ) :
    Nat.Coprime (n % Q) Q ↔ Nat.Coprime n Q := by
  change Nat.gcd (n % Q) Q = 1 ↔ Nat.gcd n Q = 1
  rw [← Nat.gcd_rec Q n, Nat.gcd_comm Q n]

theorem unitMean_abs_le (Q : ℕ) (hQ : 0 < Q) (f : ℕ → ℝ) (M : ℝ)
    (hM : ∀ n ∈ unitResidues Q, |f n| ≤ M) : |unitMean Q f| ≤ M := by
  have hc : (0 : ℝ) < (unitResidues Q).card :=
    lt_of_le_of_ne (by positivity) (Ne.symm (unit_card_ne_zero Q hQ))
  unfold unitMean average
  rw [abs_div, abs_of_pos hc]
  apply (div_le_iff₀ hc).mpr
  calc
    _ ≤ ∑ n ∈ unitResidues Q, |f n| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _n ∈ unitResidues Q, M := Finset.sum_le_sum hM
    _ = _ := by simp [mul_comm]

theorem centeredUnitSignal_abs_le (Q : ℕ) (hQ : 0 < Q)
    (f : ℕ → ℝ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ n ∈ unitResidues Q, |f n| ≤ M) (n : ℕ) :
    |centeredUnitSignal Q f n| ≤ 2 * M := by
  unfold centeredUnitSignal
  split_ifs with hn
  · have hr : n % Q ∈ unitResidues Q :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt n hQ), hn⟩
    have h1 := abs_le.mp (hM _ hr)
    have h2 := abs_le.mp (unitMean_abs_le Q hQ f M hM)
    apply abs_le.mpr
    constructor <;> linarith
  · simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM0

def returnIndices (Q a H : ℕ) : Finset ℕ :=
  (Finset.range H).filter (fun i => Nat.Coprime (a + i) Q)

/-- The periodic signal is exactly the centered sum on actual coprime returns. -/
theorem return_centered_sum (Q a H : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ returnIndices Q a H, (f ((a + i) % Q) - unitMean Q f)) =
      ∑ i ∈ Finset.range H, centeredUnitSignal Q f (a + i) := by
  rw [returnIndices, Finset.sum_filter]
  simp only [centeredUnitSignal, coprime_mod_iff]

/-- Exact sample-average error, retaining the boundary sum and actual return count. -/
theorem return_average_error_exact (Q : ℕ) (hQ : 0 < Q) (f : ℕ → ℝ)
    (a k r : ℕ) (hs : (returnIndices Q a (k * Q + r)).Nonempty) :
    average (returnIndices Q a (k * Q + r)) (fun i => f ((a + i) % Q)) -
      unitMean Q f =
      (∑ i ∈ Finset.range r, centeredUnitSignal Q f (a + k * Q + i)) /
        (returnIndices Q a (k * Q + r)).card := by
  have hc : ((returnIndices Q a (k * Q + r)).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hs)
  rw [← unit_return_interval_exact Q hQ f a k r, ← return_centered_sum]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, sub_div]
  rw [mul_div_cancel_left₀ _ hc]
  rfl

/-- Valid unconditional replacement for the impossible all-character Haar estimate.
It is useful for long intervals, but is deliberately not uniform in Q on short shells. -/
theorem return_average_error_le (Q : ℕ) (hQ : 0 < Q) (f : ℕ → ℝ)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ n ∈ unitResidues Q, |f n| ≤ M)
    (a k r : ℕ) (hs : (returnIndices Q a (k * Q + r)).Nonempty) :
    |average (returnIndices Q a (k * Q + r)) (fun i => f ((a + i) % Q)) -
      unitMean Q f| ≤
      (r * (2 * M)) / (returnIndices Q a (k * Q + r)).card := by
  rw [return_average_error_exact Q hQ f a k r hs, abs_div,
    abs_of_nonneg (show (0 : ℝ) ≤ (returnIndices Q a (k * Q + r)).card by positivity)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∑ i ∈ Finset.range r, |centeredUnitSignal Q f (a + k * Q + i)| :=
      Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _i ∈ Finset.range r, 2 * M := Finset.sum_le_sum
      (fun i hi => centeredUnitSignal_abs_le Q hQ f M hM0 hM _)
    _ = _ := by simp

/-- Unconditional corrected mean-square transfer, with both bias and boundary cost.
The scale is explicit; it does not assert a power saving for short intervals. -/
theorem return_second_moment_le (Q : ℕ) (hQ : 0 < Q) (f : ℕ → ℝ)
    (center L : ℝ)
    (hbound : ∀ n ∈ unitResidues Q, |f n - center| ≤ L)
    (a k r : ℕ) (hs : (returnIndices Q a (k * Q + r)).Nonempty) :
    average (returnIndices Q a (k * Q + r))
        (fun i => (f ((a + i) % Q) - center) ^ 2) ≤
      unitVariance Q f + (unitMean Q f - center) ^ 2 +
        (r * (2 * L ^ 2)) / (returnIndices Q a (k * Q + r)).card := by
  have hsquare : ∀ n ∈ unitResidues Q, |(f n - center) ^ 2| ≤ L ^ 2 := by
    intro n hn
    rw [abs_of_nonneg (sq_nonneg _)]
    have h := abs_le.mp (hbound n hn)
    nlinarith [sq_nonneg (L - (f n - center)),
      mul_nonneg (sub_nonneg.mpr h.2) (show 0 ≤ L + (f n - center) by linarith)]
  have he := return_average_error_le Q hQ (fun n => (f n - center) ^ 2)
    (L ^ 2) (sq_nonneg L) hsquare a k r hs
  have hupper := (abs_le.mp he).2
  rw [unit_second_moment Q hQ] at hupper
  linarith

end RiemannResearch.NumberTheory.UnitCenteredReturnSampling
