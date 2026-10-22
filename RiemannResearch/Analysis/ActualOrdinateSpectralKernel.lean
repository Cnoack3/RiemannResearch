/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.OrdinateSpectralKernel
import RiemannResearch.Analysis.HankelMomentPositivity

/-!
# Actual zeta-zero Gaussian spectral cutoffs

The spectrum is the imaginary part of every actual nontrivial zeta zero in
the positive-height cutoff, with analytic multiplicity. No RH or simplicity
assumption occurs. Positivity of these ordinate-only objects is unconditional
and cannot establish the full-zero Gaussian RH criterion.

Source: the user research report `Zero_Ordinates_Primes_Proved_Refinements`
and the elementary positive atomic spectral construction. This module checks
the finite cutoff specialization, not the infinite explicit formula.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualOrdinateSpectralKernel

open ActualZeroOrdinate ZeroOrdinate ZeroSamplingQuadratic
open OrdinateSpectralKernel HankelMomentPositivity

def gaussianWeight (a : ℝ) (ρ : ℂ) : ℝ :=
  (Zeta23.zeroMult ρ : ℝ) * Real.exp (-a * ρ.im ^ 2)

theorem gaussianWeight_pos {T a : ℝ} {ρ : ℂ} (hρ : ρ ∈ cutoff T) :
    0 < gaussianWeight a ρ := by
  apply mul_pos
  · exact_mod_cast multiplicity_pos hρ
  · exact Real.exp_pos _

def gaussianKernel (T a u : ℝ) : ℂ :=
  kernel (cutoff T) (gaussianWeight a) (fun ρ => ρ.im) u

theorem gaussianKernel_positive_definite {ι : Type*}
    (s : Finset ι) (time : ι → ℝ) (coefficient : ι → ℂ) (T a : ℝ) :
    0 ≤ (form s (fun i j => gaussianKernel T a (time i - time j)) coefficient).re :=
  kernel_positive_definite s (cutoff T) (gaussianWeight a) (fun ρ => ρ.im)
    time coefficient (fun _ hρ => (gaussianWeight_pos hρ).le)

theorem gaussianKernel_mass_bound (T a u : ℝ) :
    ‖gaussianKernel T a u‖ ≤ ∑ ρ ∈ cutoff T, gaussianWeight a ρ :=
  kernel_mass_bound (cutoff T) (gaussianWeight a) (fun ρ => ρ.im) u
    (fun _ hρ => (gaussianWeight_pos hρ).le)

theorem gaussianKernel_neg (T a u : ℝ) :
    gaussianKernel T a (-u) = star (gaussianKernel T a u) :=
  kernel_neg (cutoff T) (gaussianWeight a) (fun ρ => ρ.im) u

theorem gaussianEnergy_zero_iff {ι : Type*}
    (s : Finset ι) (time : ι → ℝ) (coefficient : ι → ℂ) (T a : ℝ) :
    (form s (samplingGram (cutoff T) (gaussianWeight a)
      (fun ρ i => phase (time i) ρ.im)) coefficient).re = 0 ↔
      ∀ ρ ∈ cutoff T, (∑ i ∈ s, coefficient i * phase (time i) ρ.im) = 0 :=
  sampling_form_zero_iff s (cutoff T) (gaussianWeight a)
    (fun ρ i => phase (time i) ρ.im) coefficient (fun _ hρ => gaussianWeight_pos hρ)

def gaussianMoment (T a : ℝ) (k : ℕ) : ℝ :=
  atomicMoment (cutoff T) (gaussianWeight a) (fun ρ => ρ.im ^ 2) k

theorem gaussianMoment_shiftedHankelPSD (T a : ℝ) :
    ShiftedHankelPSD (gaussianMoment T a) :=
  atomicMoment_shiftedHankelPSD (cutoff T) (gaussianWeight a) (fun ρ => ρ.im ^ 2)
    (fun _ hρ => (gaussianWeight_pos hρ).le) (fun _ _ => sq_nonneg _)

theorem gaussianMoment_log_convex (T a : ℝ) (k : ℕ) :
    gaussianMoment T a (k + 1) ^ 2 ≤
      gaussianMoment T a k * gaussianMoment T a (k + 2) :=
  moment_log_convex (gaussianMoment_shiftedHankelPSD T a) k

end RiemannResearch.Analysis.ActualOrdinateSpectralKernel
