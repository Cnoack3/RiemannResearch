import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Finite algebra for the two-cutoff prime-sieve obstruction

Source: user-directed research continuation, October 7, 2026; see
`IndependentPrimeResearchContinuation20261007.md`, equations (10), (14),
and (15), for the statements and their arithmetic interpretation. These are exact finite identities
and inequalities. The asymptotic Mertens input and the arithmetic
identification of the prime increments are not hypotheses discharged here.

-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.PrimeSieveSecant

theorem two_cutoff_secant_identity
    (a b A B : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    (a * (b * B) - b * (a * A)) / (a - b) =
      (B - A) / (1 / b - 1 / a) := by
  field_simp [ha, hb, sub_ne_zero.mpr hab]

theorem finite_secant_as_weighted_average
    {ι : Type*} (s : Finset ι) (u g : ι → ℝ) :
    (∑ i ∈ s, u i * g i) / (∑ i ∈ s, u i) =
      ∑ i ∈ s, (u i / (∑ j ∈ s, u j)) * g i := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem prime_increment_normalization
    (p a fOld fNew : ℝ) (ha : a ≠ 0) (hp : p ≠ 0)
    (hp1 : p - 1 ≠ 0) :
    fNew / (a * (1 - 1 / p)) - fOld / a =
      (1 / (a * (1 - 1 / p)) - 1 / a) *
        (p * fNew - (p - 1) * fOld) := by
  have hfactor : 1 - 1 / p ≠ 0 := by
    intro h
    have he : p - 1 = 0 := by
      have hm := congrArg (fun x : ℝ => x * p) h
      field_simp [hp] at hm
      linarith
    exact hp1 he
  (field_simp [ha, hp, hp1, hfactor]; ring)

/-- Signed affine combinations pay the full coefficient total variation. -/
theorem affine_mean_deviation_le
    {ι : Type*} (s : Finset ι) (c m : ι → ℝ) (L η : ℝ)
    (hc : (∑ i ∈ s, c i) = 1)
    (hm : ∀ i ∈ s, |m i - L| ≤ η) :
    |(∑ i ∈ s, c i * m i) - L| ≤ η * ∑ i ∈ s, |c i| := by
  have he : (∑ i ∈ s, c i * m i) - L =
      ∑ i ∈ s, c i * (m i - L) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hc]
    ring
  rw [he]
  calc
    _ ≤ ∑ i ∈ s, |c i * (m i - L)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, |c i| * |m i - L| := by simp only [abs_mul]
    _ ≤ ∑ i ∈ s, |c i| * η :=
      Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_left (hm i hi) (abs_nonneg _))
    _ = η * ∑ i ∈ s, |c i| := by rw [← Finset.sum_mul]; ring

/-- A convex average of slopes in an η-band stays in the same band. -/
theorem convex_mean_deviation_le
    {ι : Type*} (s : Finset ι) (w m : ι → ℝ) (L η : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hunit : (∑ i ∈ s, w i) = 1)
    (hm : ∀ i ∈ s, |m i - L| ≤ η) :
    |(∑ i ∈ s, w i * m i) - L| ≤ η := by
  have h := affine_mean_deviation_le s w m L η hunit hm
  have habs : (∑ i ∈ s, |w i|) = 1 := by
    calc
      _ = ∑ i ∈ s, w i := Finset.sum_congr rfl
        (fun i hi => abs_of_nonneg (hw i hi))
      _ = 1 := hunit
  simpa only [habs, mul_one] using h

/-- The mean target one forces cancellation when the local slopes approach L. -/
theorem signed_variation_necessary
    {ι : Type*} (s : Finset ι) (c m : ι → ℝ) (L η τ : ℝ)
    (hc : (∑ i ∈ s, c i) = 1)
    (hm : ∀ i ∈ s, |m i - L| ≤ η)
    (htarget : |1 - ∑ i ∈ s, c i * m i| ≤ τ) :
    |1 - L| ≤ τ + η * ∑ i ∈ s, |c i| := by
  have h := affine_mean_deviation_le s c m L η hc hm
  calc
    _ = |(1 - ∑ i ∈ s, c i * m i) + ((∑ i ∈ s, c i * m i) - L)| := by
      congr 1
      ring
    _ ≤ |1 - ∑ i ∈ s, c i * m i| + |(∑ i ∈ s, c i * m i) - L| := abs_add_le _ _
    _ ≤ _ := add_le_add htarget h

end RiemannResearch.RH.PrimeSieveSecant
