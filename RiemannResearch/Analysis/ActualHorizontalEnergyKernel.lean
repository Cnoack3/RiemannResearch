/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.SummableOrdinateKernel
import RiemannResearch.Analysis.ActualZeroSecondEnergy

/-!
# A beta-sensitive harmonic kernel of all actual zeta zeros

The absolutely convergent fourth-energy kernel is positive definite and has
an explicit uniform height-tail bound supplied by the second energy.
Its value at zero is exactly the RH-equivalent fourth energy.
The final arithmetic cancellation criterion is a conditional research
reduction: its detection and cancellation hypotheses remain Open.
Source: user-provided unconditional zeta-zero agenda, priorities 2 and 4.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ActualHorizontalEnergyKernel
open ActualZeroHorizontalEnergy OrdinateSpectralKernel

def energyKernel (u : ℝ) : ℂ :=
  infiniteKernel horizontalTerm (fun ρ : ActualZero => (ρ : ℂ).im) u

def finiteEnergyKernel (s : Finset ActualZero) (u : ℝ) : ℂ :=
  kernel s horizontalTerm (fun ρ => (ρ : ℂ).im) u

theorem energyKernel_zero : energyKernel 0 = (horizontalFourthEnergy : ℂ) :=
  infiniteKernel_zero _ _ horizontalTerm_summable

theorem energyKernel_mass_bound (u : ℝ) : ‖energyKernel u‖ ≤ horizontalFourthEnergy :=
  infiniteKernel_mass_bound _ _ horizontalTerm_summable horizontalTerm_nonneg u

theorem energyKernel_positive_definite {ι : Type*}
    (s : Finset ι) (u : ι → ℝ) (a : ι → ℂ) :
    0 ≤ (ZeroSamplingQuadratic.form s (fun i j => energyKernel (u i - u j)) a).re :=
  infiniteKernel_positive_definite _ _ horizontalTerm_summable horizontalTerm_nonneg s u a

/-- This equivalence is unconditional; its left-hand side is not asserted. -/
theorem energyKernel_zero_iff_RH : energyKernel 0 = 0 ↔ RiemannHypothesis := by
  rw [energyKernel_zero, Complex.ofReal_eq_zero]
  exact horizontalFourthEnergy_eq_zero_iff_RH

/-- Every zero outside the chosen finite set must be at the stated height.
This is a geometric cutoff condition, with both signs and multiplicity retained. -/
theorem energyTail_le_secondEnergy (s : Finset ActualZero) (H : ℝ)
    (hcut : ∀ ρ : ActualZero, ρ ∉ s → H ^ 2 ≤ (ρ : ℂ).im ^ 2) :
    tailMass horizontalTerm s ≤ horizontalSecondEnergy / (1 + H ^ 2) := by
  have hD : 0 < 1 + H ^ 2 := by positivity
  have hp (ρ : {ρ : ActualZero // ρ ∉ s}) :
      horizontalTerm ρ ≤ horizontalSecondTerm ρ / (1 + H ^ 2) := by
    apply (le_div_iff₀ hD).mpr
    have hm := mul_le_mul_of_nonneg_left (hcut ρ ρ.property) (horizontalTerm_nonneg ρ)
    have he := horizontalCurvatureTerm_eq ρ
    nlinarith
  have hsub : Summable (fun ρ : {ρ : ActualZero // ρ ∉ s} => horizontalSecondTerm ρ) :=
    horizontalSecondTerm_summable.subtype _
  have hle := (horizontalTerm_summable.subtype (fun ρ => ρ ∉ s)).tsum_le_tsum hp
    (hsub.div_const (1 + H ^ 2))
  have hmass : (∑' ρ : {ρ : ActualZero // ρ ∉ s}, horizontalSecondTerm ρ) ≤
      horizontalSecondEnergy := by
    have he := horizontalSecondTerm_summable.sum_add_tsum_compl (s := s)
    change (∑ ρ ∈ s, horizontalSecondTerm ρ) +
      (∑' ρ : {ρ : ActualZero // ρ ∉ s}, horizontalSecondTerm ρ) =
        (∑' ρ : ActualZero, horizontalSecondTerm ρ) at he
    have hn : 0 ≤ ∑ ρ ∈ s, horizontalSecondTerm ρ :=
      Finset.sum_nonneg (fun ρ _ => horizontalSecondTerm_nonneg ρ)
    change (∑' ρ : {ρ : ActualZero // ρ ∉ s}, horizontalSecondTerm ρ) ≤
      ∑' ρ : ActualZero, horizontalSecondTerm ρ
    linarith
  calc
    _ ≤ (∑' ρ : {ρ : ActualZero // ρ ∉ s}, horizontalSecondTerm ρ) / (1 + H ^ 2) := by
      simpa only [tailMass, tsum_div_const] using hle
    _ ≤ _ := div_le_div_of_nonneg_right hmass hD.le

/-- An explicit tail bound uniform over every real Fourier frequency. -/
theorem energyKernel_uniform_height_tail (s : Finset ActualZero) (H u : ℝ)
    (hcut : ∀ ρ : ActualZero, ρ ∉ s → H ^ 2 ≤ (ρ : ℂ).im ^ 2) :
    ‖energyKernel u - finiteEnergyKernel s u‖ ≤
      horizontalSecondEnergy / (1 + H ^ 2) :=
  (infiniteKernel_sub_kernel_bound _ _ horizontalTerm_summable
    horizontalTerm_nonneg s u).trans (energyTail_le_secondEnergy s H hcut)

/-- A genuine growing-test error bound with its complete omitted zero tail. -/
theorem energyKernel_growing_test_height_bound {ι : Type*}
    (s : Finset ActualZero) (H : ℝ)
    (hcut : ∀ ρ : ActualZero, ρ ∉ s → H ^ 2 ≤ (ρ : ℂ).im ^ 2)
    (support : Finset ι) (u : ι → ℝ) (a : ι → ℂ) :
    ‖(∑ i ∈ support, a i * energyKernel (u i)) -
      ∑ i ∈ support, a i * finiteEnergyKernel s (u i)‖ ≤
      (∑ i ∈ support, ‖a i‖) * (horizontalSecondEnergy / (1 + H ^ 2)) :=
  (finite_test_tail_bound _ _ horizontalTerm_summable horizontalTerm_nonneg s
    support u a).trans (mul_le_mul_of_nonneg_left (energyTail_le_secondEnergy s H hcut)
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))

/-- Conditional research reduction. The finite arithmetic moments must tend
to zero, their complete tail budget must vanish, and their full moments must
detect a fixed strict fraction of the positive energy. None is asserted here. -/
theorem riemannHypothesis_of_detecting_growing_tests {ι : Type*}
    (samples : ℕ → Finset ActualZero) (support : ℕ → Finset ι)
    (u : ℕ → ι → ℝ) (a : ℕ → ι → ℂ) (θ : ℝ) (hθ : θ < 1)
    (hdetect : ∀ n, ‖(horizontalFourthEnergy : ℂ) -
      ∑ i ∈ support n, a n i * energyKernel (u n i)‖ ≤ θ * horizontalFourthEnergy)
    (htail : Tendsto (fun n => (∑ i ∈ support n, ‖a n i‖) *
      tailMass horizontalTerm (samples n)) atTop (𝓝 0))
    (hcancel : Tendsto (fun n => ∑ i ∈ support n,
      a n i * finiteEnergyKernel (samples n) (u n i)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  have hdiff := growing_test_tail_tendsto_zero horizontalTerm
    (fun ρ : ActualZero => (ρ : ℂ).im) horizontalTerm_summable horizontalTerm_nonneg
    samples support u a htail
  have hfull : Tendsto (fun n => ∑ i ∈ support n, a n i * energyKernel (u n i))
      atTop (𝓝 0) := by
    simpa only [sub_add_cancel, add_zero, energyKernel, finiteEnergyKernel] using
      hdiff.add hcancel
  have hnorm := ((tendsto_const_nhds (x := (horizontalFourthEnergy : ℂ))).sub hfull).norm
  have hle : horizontalFourthEnergy ≤ θ * horizontalFourthEnergy := by
    have hh := le_of_tendsto hnorm (Eventually.of_forall hdetect)
    simpa only [sub_zero, Complex.norm_of_nonneg horizontalFourthEnergy_nonneg] using hh
  apply horizontalFourthEnergy_eq_zero_iff_RH.mp
  nlinarith [horizontalFourthEnergy_nonneg]

/-- The geometric height cutoff makes the tail obligation automatic under
the explicit coefficient-growth budget. Detection and arithmetic cancellation
are the only domain-specific open inputs in this specialization. -/
theorem riemannHypothesis_of_detecting_height_tests {ι : Type*}
    (samples : ℕ → Finset ActualZero) (support : ℕ → Finset ι)
    (u : ℕ → ι → ℝ) (a : ℕ → ι → ℂ) (H : ℕ → ℝ) (θ : ℝ) (hθ : θ < 1)
    (hcut : ∀ n, ∀ ρ : ActualZero, ρ ∉ samples n → (H n) ^ 2 ≤ (ρ : ℂ).im ^ 2)
    (hbudget : Tendsto (fun n => (∑ i ∈ support n, ‖a n i‖) / (1 + (H n) ^ 2))
      atTop (𝓝 0))
    (hdetect : ∀ n, ‖(horizontalFourthEnergy : ℂ) -
      ∑ i ∈ support n, a n i * energyKernel (u n i)‖ ≤ θ * horizontalFourthEnergy)
    (hcancel : Tendsto (fun n => ∑ i ∈ support n,
      a n i * finiteEnergyKernel (samples n) (u n i)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_detecting_growing_tests samples support u a θ hθ hdetect
    ?_ hcancel
  have hmajor := hbudget.mul_const horizontalSecondEnergy
  simp only [zero_mul] at hmajor
  apply squeeze_zero _ _ hmajor
  · intro n
    exact mul_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
      (tailMass_nonneg horizontalTerm horizontalTerm_nonneg (samples n))
  · intro n
    calc
      _ ≤ (∑ i ∈ support n, ‖a n i‖) *
          (horizontalSecondEnergy / (1 + (H n) ^ 2)) :=
        mul_le_mul_of_nonneg_left (energyTail_le_secondEnergy (samples n) (H n) (hcut n))
          (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
      _ = _ := by ring

end RiemannResearch.Analysis.ActualHorizontalEnergyKernel
