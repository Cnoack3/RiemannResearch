import RiemannResearch.Analysis.FiniteProfileEnergy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Two-region signed covariance budget
Finite consequences of Cauchy--Schwarz and opposite signed covariances.
The exact remainder precedes the bound; zero-energy regions are permitted.
Consumer: the actual exact-head three-prime return in the A1--A2 program.
-/
noncomputable section
namespace RiemannResearch.Analysis.FiniteWeightedReturnBounds
open FiniteProfileEnergy
variable {ι : Type*}

/-- Each parenthesized defect is the complete minor sum of gram_identity. -/
theorem two_region_gram_identity (L T : Finset ι) (w R F : ι → ℝ)
    (hn : pairing L w R F + pairing T w R F = 0) :
    (energy L w R + energy T w R) * energy L w F * energy T w F -
      (energy L w F + energy T w F) * pairing L w R F ^ 2 =
    energy T w F * (energy L w R * energy L w F - pairing L w R F ^ 2) +
    energy L w F * (energy T w R * energy T w F - pairing T w R F ^ 2) := by
  have ht : pairing T w R F = -pairing L w R F := by linarith
  rw [ht]
  ring

theorem two_region_pairing_sq_le (L T : Finset ι) (w R F : ι → ℝ)
    (hwL : ∀ i ∈ L, 0 ≤ w i) (hwT : ∀ i ∈ T, 0 ≤ w i)
    (hn : pairing L w R F + pairing T w R F = 0) :
    (energy L w F + energy T w F) * pairing L w R F ^ 2 ≤
      (energy L w R + energy T w R) * energy L w F * energy T w F := by
  have h := two_region_gram_identity L T w R F hn
  have hL := mul_nonneg (energy_nonneg T w F hwT)
    (sub_nonneg.mpr (pairing_sq_le L w R F hwL))
  have hT := mul_nonneg (energy_nonneg L w F hwL)
    (sub_nonneg.mpr (pairing_sq_le T w R F hwT))
  linarith

/-- Harmonic combination of the two exact geometric energies.
The theorem also handles zero denominators without a rank hypothesis. -/
theorem two_region_pairing_sq_le_harmonic (L T : Finset ι) (w R F : ι → ℝ)
    (hwL : ∀ i ∈ L, 0 ≤ w i) (hwT : ∀ i ∈ T, 0 ≤ w i)
    (hn : pairing L w R F + pairing T w R F = 0) :
    pairing L w R F ^ 2 ≤
      (energy L w R + energy T w R) *
      (energy L w F * energy T w F / (energy L w F + energy T w F)) := by
  have hL := energy_nonneg L w F hwL
  have hT := energy_nonneg T w F hwT
  by_cases hd : 0 < energy L w F + energy T w F
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hd).mpr
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      two_region_pairing_sq_le L T w R F hwL hwT hn
  · have hz : energy L w F = 0 := by linarith
    have hh := pairing_sq_le L w R F hwL
    rw [hz] at hh ⊢
    simpa using hh

end RiemannResearch.Analysis.FiniteWeightedReturnBounds
