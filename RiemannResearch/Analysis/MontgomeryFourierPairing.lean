/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryFormFactor
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring


/-! # Exact Fourier pairing for the raw multiplicity-aware form factor

Source: the finite Fourier-inversion identity in Montgomery (1973),
https://websites.umich.edu/~hlm/paircor1.pdf, and the user Montgomery handoff.
The Fourier convention is Mathlib's exp(-2*pi*i*alpha*x). Continuity and
integrability of f and its Fourier transform are explicit. No RH or
asymptotic pair-correlation assertion is assumed or proved here.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace RiemannResearch.Analysis.MontgomeryFormFactor
open MontgomeryPoisson ZeroOrdinate
variable {ι : Type*} [Fintype ι]

theorem integral_phase_fourier {f : ℝ → ℂ} (hc : Continuous f)
    (hf : Integrable f) (hF : Integrable (𝓕 f)) (x : ℝ) :
    (∫ α : ℝ, phase (2*Real.pi*α) x * 𝓕 f α) = f x := by
  have h := congrFun (hc.fourierInv_fourier_eq hf hF) x
  rw [Real.fourierInv_eq'] at h
  simpa only [phase, RCLike.inner_apply', starRingEnd_apply, star_trivial,
    smul_eq_mul, mul_assoc] using h

theorem integrable_phase_mul {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    Integrable (fun α : ℝ => phase (2*Real.pi*α) x * f α) := by
  apply hf.bdd_mul (c := 1)
  · have hcont : Continuous (fun α : ℝ => phase (2*Real.pi*α) x) := by
      unfold phase
      fun_prop
    exact hcont.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun α => le_of_eq (phase_norm _ _))

/-- Exact finite Fourier pairing, with the 2*pi convention fixed explicitly. -/
theorem finite_fourier_pairing (t : ι → ℝ) (L : ℝ) {f : ℝ → ℂ}
    (hc : Continuous f) (hf : Integrable f) (hF : Integrable (𝓕 f)) :
    (∫ α : ℝ, 𝓕 f α * pairSum t (2*Real.pi*α*L)) =
      ∑ i, ∑ j, (cauchyWeight (t i-t j) : ℂ) * f (L*(t i-t j)) := by
  have he (α : ℝ) :
      𝓕 f α * pairSum t (2*Real.pi*α*L) =
        ∑ i, ∑ j, (cauchyWeight (t i-t j) : ℂ) *
          (phase (2*Real.pi*α) (L*(t i-t j)) * 𝓕 f α) := by
    unfold pairSum
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have hp : phase (2*Real.pi*α*L) (t i-t j) =
        phase (2*Real.pi*α) (L*(t i-t j)) := by
      unfold phase
      congr 1
      push_cast
      ring
    rw [hp]
    ring
  have hi (i j : ι) : Integrable (fun α : ℝ =>
      (cauchyWeight (t i-t j) : ℂ) *
        (phase (2*Real.pi*α) (L*(t i-t j)) * 𝓕 f α)) :=
    (integrable_phase_mul hF _).const_mul _
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, integral_phase_fourier hc hf hF]

theorem actual_fourier_pairing (T : ℝ) {f : ℝ → ℂ}
    (hc : Continuous f) (hf : Integrable f) (hF : Integrable (𝓕 f)) :
    (∫ α : ℝ, 𝓕 f α *
      pairSum (ActualZeroOrdinate.copyOrdinate T) (α*Real.log T)) =
      ∑ i : ActualZeroOrdinate.Copies T, ∑ j : ActualZeroOrdinate.Copies T,
        (cauchyWeight (ActualZeroOrdinate.copyOrdinate T i-
          ActualZeroOrdinate.copyOrdinate T j) : ℂ) *
        f ((Real.log T/(2*Real.pi))*(ActualZeroOrdinate.copyOrdinate T i-
          ActualZeroOrdinate.copyOrdinate T j)) := by
  have h := finite_fourier_pairing (ActualZeroOrdinate.copyOrdinate T)
    (Real.log T/(2*Real.pi)) hc hf hF
  have he (α : ℝ) : 2*Real.pi*α*(Real.log T/(2*Real.pi)) = α*Real.log T := by
    field_simp
  simpa only [he] using h

theorem ofReal_formFactor (T α : ℝ) :
    (formFactor T α : ℂ) =
      pairSum (ActualZeroOrdinate.copyOrdinate T) (α*Real.log T) /
        ((T*Real.log T/(2*Real.pi) : ℝ) : ℂ) := by
  rw [formFactor, Complex.ofReal_div]
  congr 1
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im, pairSum_real]

/-- The exact Montgomery normalization, for every integrable Fourier pair. -/
theorem normalized_fourier_pairing (T : ℝ) {f : ℝ → ℂ}
    (hc : Continuous f) (hf : Integrable f) (hF : Integrable (𝓕 f)) :
    (∫ α : ℝ, 𝓕 f α * (formFactor T α : ℂ)) =
      (∑ i : ActualZeroOrdinate.Copies T, ∑ j : ActualZeroOrdinate.Copies T,
        (cauchyWeight (ActualZeroOrdinate.copyOrdinate T i -
          ActualZeroOrdinate.copyOrdinate T j) : ℂ) *
        f ((Real.log T/(2*Real.pi))*(ActualZeroOrdinate.copyOrdinate T i -
          ActualZeroOrdinate.copyOrdinate T j))) /
        ((T*Real.log T/(2*Real.pi) : ℝ) : ℂ) := by
  simp_rw [ofReal_formFactor, ← mul_div_assoc]
  rw [integral_div, actual_fourier_pairing T hc hf hF]

end RiemannResearch.Analysis.MontgomeryFormFactor
