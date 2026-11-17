import RiemannResearch.Analysis.FiniteProfileEnergy
import Mathlib.Tactic

/-!
# Signed observations on affine normal residuals

The affine part of an observing vector annihilates an affine normal residual.
We retain the exact pairing and Gram remainder before applying Cauchy--Schwarz.
The RH consumer uses the Mobius vector and the actual Green-profile fit.
This is finite weighted Hilbert projection algebra, independently assembled
for the user's exact-head agenda; no asymptotic number-theoretic premise occurs.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteProfileEnergy
variable {ι : Type*}

/-- Every affine correction to the observing vector gives the same pairing. -/
theorem affine_residual_pairing (s : Finset ι) (w t e f : ι → ℝ) (a0 a1 : ℝ)
    (h0 : (∑ i ∈ s, w i * e i) = 0)
    (h1 : (∑ i ∈ s, w i * t i * e i) = 0) :
    pairing s w f e = pairing s w (fun i => f i - a0 - a1 * t i) e := by
  have he : pairing s w (fun i => f i - a0 - a1 * t i) e =
      pairing s w f e - a0 * (∑ i ∈ s, w i * e i) -
        a1 * (∑ i ∈ s, w i * t i * e i) := by
    unfold pairing
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simpa only [h0, h1, mul_zero, sub_zero] using he.symm

/-- Exact two-coordinate remainder after removing the irrelevant affine part. -/
theorem affine_residual_gram_identity (s : Finset ι) (w t e f : ι → ℝ)
    (a0 a1 : ℝ) (h0 : (∑ i ∈ s, w i * e i) = 0)
    (h1 : (∑ i ∈ s, w i * t i * e i) = 0) :
    affineLoss s w t f a0 a1 * energy s w e - pairing s w f e ^ 2 =
      (∑ i ∈ s, ∑ j ∈ s, w i * w j *
        ((f i - a0 - a1 * t i) * e j -
          (f j - a0 - a1 * t j) * e i) ^ 2) / 2 := by
  rw [affine_residual_pairing s w t e f a0 a1 h0 h1]
  exact gram_identity s w (fun i => f i - a0 - a1 * t i) e

/-- The observer's affine residual energy replaces its full energy. -/
theorem affine_residual_pairing_sq_le (s : Finset ι) (w t e f : ι → ℝ)
    (a0 a1 : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (h0 : (∑ i ∈ s, w i * e i) = 0)
    (h1 : (∑ i ∈ s, w i * t i * e i) = 0) :
    pairing s w f e ^ 2 ≤ affineLoss s w t f a0 a1 * energy s w e := by
  rw [affine_residual_pairing s w t e f a0 a1 h0 h1]
  exact pairing_sq_le s w (fun i => f i - a0 - a1 * t i) e hw

/-- Pythagoras identifies exactly the energy removed from a normal fit. -/
theorem affine_normal_energy_split (s : Finset ι) (w t f : ι → ℝ) (a0 a1 : ℝ)
    (h0 : (∑ i ∈ s, w i * (f i - a0 - a1 * t i)) = 0)
    (h1 : (∑ i ∈ s, w i * t i * (f i - a0 - a1 * t i)) = 0) :
    energy s w f = affineLoss s w t f a0 a1 +
      energy s w (fun i => a0 + a1 * t i) := by
  have h := affine_completion s w t f a0 a1 0 0 h0 h1
  have he : energy s w (fun i => (0 - a0) + (0 - a1) * t i) =
      energy s w (fun i => a0 + a1 * t i) := by
    unfold energy
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simpa only [affineLoss, sub_zero, zero_mul, he] using h

theorem affine_normal_loss_le_energy (s : Finset ι) (w t f : ι → ℝ)
    (a0 a1 : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (h0 : (∑ i ∈ s, w i * (f i - a0 - a1 * t i)) = 0)
    (h1 : (∑ i ∈ s, w i * t i * (f i - a0 - a1 * t i)) = 0) :
    affineLoss s w t f a0 a1 ≤ energy s w f := by
  rw [affine_normal_energy_split s w t f a0 a1 h0 h1]
  exact le_add_of_nonneg_right (energy_nonneg _ _ _ hw)

/-- Exact energy removed by the normal affine fit, including the mixed moment. -/
theorem affine_normal_removed_energy (s : Finset ι) (w t f : ι → ℝ) (a0 a1 : ℝ)
    (h0 : (∑ i ∈ s, w i * (f i - a0 - a1 * t i)) = 0)
    (h1 : (∑ i ∈ s, w i * t i * (f i - a0 - a1 * t i)) = 0) :
    (mass s w * energy s w t - (∑ i ∈ s, w i * t i) ^ 2) *
        (energy s w f - affineLoss s w t f a0 a1) =
      energy s w t * (∑ i ∈ s, w i * f i) ^ 2 -
        2 * (∑ i ∈ s, w i * t i) * (∑ i ∈ s, w i * f i) *
          (∑ i ∈ s, w i * t i * f i) +
        mass s w * (∑ i ∈ s, w i * t i * f i) ^ 2 := by
  have hn0 : mass s w * a0 + (∑ i ∈ s, w i * t i) * a1 =
      ∑ i ∈ s, w i * f i := by
    have he : (∑ i ∈ s, w i * (f i - a0 - a1 * t i)) =
        (∑ i ∈ s, w i * f i) - mass s w * a0 - (∑ i ∈ s, w i * t i) * a1 := by
      unfold mass
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [he] at h0
    linarith
  have hn1 : (∑ i ∈ s, w i * t i) * a0 + energy s w t * a1 =
      ∑ i ∈ s, w i * t i * f i := by
    have he : (∑ i ∈ s, w i * t i * (f i - a0 - a1 * t i)) =
        (∑ i ∈ s, w i * t i * f i) - (∑ i ∈ s, w i * t i) * a0 -
          energy s w t * a1 := by
      unfold energy
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [he] at h1
    linarith
  have he : energy s w (fun i => a0 + a1 * t i) =
      a0 * (∑ i ∈ s, w i * f i) + a1 * (∑ i ∈ s, w i * t i * f i) := by
    rw [← hn0, ← hn1]
    unfold energy mass
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [affine_normal_energy_split s w t f a0 a1 h0 h1, add_sub_cancel_left, he]
  have h := affine_moment_numerator (mass s w) (∑ i ∈ s, w i * t i) (energy s w t)
    (∑ i ∈ s, w i * f i) (∑ i ∈ s, w i * t i * f i)
    (∑ i ∈ s, w i * f i) (∑ i ∈ s, w i * t i * f i) a0 a1 hn0 hn1
  rw [h]
  ring

end RiemannResearch.Analysis.FiniteProfileEnergy
