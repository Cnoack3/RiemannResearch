/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.Analysis.SquarePartitionLocalization
import RiemannResearch.RH.ScrewPrimePart

/-!
# Exact signed correlation bookkeeping

Source: Sections 2, 4, and 5 of
`RH_Exact_Arithmetic_Channel_Effects_2026-09-07.md`.

The finite arithmetic value below uses the actual von Mangoldt weights.
Integral linearity is proved with explicit integrability hypotheses. Its
identification with the zero-side Weil distribution, the removal of the finite
cutoff, and uniform estimates are not asserted here.
-/

open MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.RH.SignedWeilCorrelation

noncomputable section

abbrev positiveMeasure : Measure ℝ := volume.restrict (Ioi 0)

/-- A full signed correlation expression, with its subtraction at zero retained. -/
def correlationValue (s : Finset ℕ) (w τ : ℕ → ℝ) (P K reg : ℝ → ℝ) (c : ℝ)
    (C : ℝ → ℝ) : ℝ :=
  2 * (∫ t, P t * C t ∂positiveMeasure) -
    2 * ∑ n ∈ s, w n * C (τ n) - c * C 0 -
    2 * (∫ t, K t * (C t - reg t * C 0) ∂positiveMeasure)

/-- The polar kernel, including both completed-zeta pole contributions. -/
def weilPoleKernel (t : ℝ) : ℝ := Real.exp (t / 2) + Real.exp (-t / 2)

/-- The gamma kernel. The integrals use the open positive half-line. -/
def weilGammaKernel (t : ℝ) : ℝ := Real.exp (t / 2) / (Real.exp t - Real.exp (-t))

/-- The diagonal regularizer in the completed explicit formula. -/
def weilRegulator (t : ℝ) : ℝ := Real.exp (-t / 2)

/-- Explicit integrability, so the actual integrals do not use a default value. -/
def AdmissibleCorrelation (C : ℝ → ℝ) : Prop :=
  Integrable (fun t => weilPoleKernel t * C t) positiveMeasure ∧
  Integrable (fun t => weilGammaKernel t * (C t - weilRegulator t * C 0))
    positiveMeasure

/-- The actual finite prime-power specialization of the paper's arithmetic side.
The archimedean diagonal constant is a parameter because the identities are
valid for every value of that constant. -/
def primePowerCorrelationValue (N : ℕ) (c : ℝ) (C : ℝ → ℝ) : ℝ :=
  correlationValue (Finset.range N) primePowerWeight (fun n => Real.log n)
    weilPoleKernel weilGammaKernel weilRegulator c C

theorem correlationValue_sub (s : Finset ℕ) (w τ : ℕ → ℝ) (P K reg : ℝ → ℝ) (c : ℝ)
    (C D : ℝ → ℝ)
    (hPC : Integrable (fun t => P t * C t) positiveMeasure)
    (hPD : Integrable (fun t => P t * D t) positiveMeasure)
    (hKC : Integrable (fun t => K t * (C t - reg t * C 0)) positiveMeasure)
    (hKD : Integrable (fun t => K t * (D t - reg t * D 0)) positiveMeasure) :
    correlationValue s w τ P K reg c (C - D) =
      correlationValue s w τ P K reg c C - correlationValue s w τ P K reg c D := by
  have hp : (fun t => P t * (C - D) t) =
      (fun t => P t * C t - P t * D t) := by ext t; simp [mul_sub]
  have hk : (fun t => K t * ((C - D) t - reg t * (C - D) 0)) =
      (fun t => K t * (C t - reg t * C 0) -
        K t * (D t - reg t * D 0)) := by ext t; simp only [Pi.sub_apply]; ring
  unfold correlationValue
  rw [hp, hk, integral_sub hPC hPD, integral_sub hKC hKD]
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Finite-sum linearity, proved for the actual integrals rather than postulated. -/
theorem correlationValue_sum {ι : Type*} [Fintype ι]
    (s : Finset ℕ) (w τ : ℕ → ℝ) (P K reg : ℝ → ℝ) (c : ℝ) (C : ι → ℝ → ℝ)
    (hP : ∀ j, Integrable (fun t => P t * C j t) positiveMeasure)
    (hK : ∀ j, Integrable (fun t => K t * (C j t - reg t * C j 0)) positiveMeasure) :
    correlationValue s w τ P K reg c (fun t => ∑ j, C j t) =
      ∑ j, correlationValue s w τ P K reg c (C j) := by
  have hp : (fun t => P t * ∑ j, C j t) =
      (fun t => ∑ j, P t * C j t) := by ext t; simp [Finset.mul_sum]
  have hk : (fun t => K t * ((∑ j, C j t) - reg t * ∑ j, C j 0)) =
      (fun t => ∑ j, K t * (C j t - reg t * C j 0)) := by
    ext t
    simp [Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]
  unfold correlationValue
  rw [hp, hk, integral_finsetSum _ (fun j _ => hP j),
    integral_finsetSum _ (fun j _ => hK j)]
  simp only [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Exact net effect of a correlation difference; every signed component stays. -/
theorem correlationValue_net_effect (s : Finset ℕ) (w τ : ℕ → ℝ) (P K reg : ℝ → ℝ)
    (c : ℝ) (C D : ℝ → ℝ)
    (hPC : Integrable (fun t => P t * C t) positiveMeasure)
    (hPD : Integrable (fun t => P t * D t) positiveMeasure)
    (hKC : Integrable (fun t => K t * (C t - reg t * C 0)) positiveMeasure)
    (hKD : Integrable (fun t => K t * (D t - reg t * D 0)) positiveMeasure) :
    correlationValue s w τ P K reg c C - correlationValue s w τ P K reg c D =
      2 * (∫ t, P t * (C t - D t) ∂positiveMeasure) -
      2 * ∑ n ∈ s, w n * (C (τ n) - D (τ n)) - c * (C 0 - D 0) -
      2 * (∫ t, K t * ((C t - D t) - reg t * (C 0 - D 0)) ∂positiveMeasure) := by
  rw [← correlationValue_sub s w τ P K reg c C D hPC hPD hKC hKD]
  rfl

/-- Complete gluing defect with zero diagonal. Poles, prime powers, and gamma
retain their signs; no positivity of this defect is claimed. -/
theorem correlationValue_gluing {ι : Type*} [Fintype ι]
    (s : Finset ℕ) (w τ : ℕ → ℝ) (P K reg : ℝ → ℝ) (c : ℝ)
    (C R : ℝ → ℝ) (Cj : ι → ℝ → ℝ)
    (hrel : (fun t => ∑ j, Cj j t) = C - R) (hR0 : R 0 = 0)
    (hPj : ∀ j, Integrable (fun t => P t * Cj j t) positiveMeasure)
    (hKj : ∀ j, Integrable (fun t => K t * (Cj j t - reg t * Cj j 0)) positiveMeasure)
    (hPC : Integrable (fun t => P t * C t) positiveMeasure)
    (hPR : Integrable (fun t => P t * R t) positiveMeasure)
    (hKC : Integrable (fun t => K t * (C t - reg t * C 0)) positiveMeasure)
    (hKR : Integrable (fun t => K t * (R t - reg t * R 0)) positiveMeasure) :
    (∑ j, correlationValue s w τ P K reg c (Cj j)) -
      correlationValue s w τ P K reg c C =
      2 * ∑ n ∈ s, w n * R (τ n) +
      2 * (∫ t, K t * R t ∂positiveMeasure) -
      2 * (∫ t, P t * R t ∂positiveMeasure) := by
  rw [← correlationValue_sum s w τ P K reg c Cj hPj hKj, hrel,
    correlationValue_sub s w τ P K reg c C R hPC hPR hKC hKR]
  simp only [correlationValue, hR0, mul_zero, sub_zero]
  ring

open RiemannResearch.Analysis.SquarePartitionLocalization

/-- Real autocorrelation used by the real-valued Weil form. -/
def realAutocorrelation (f : ℝ → ℂ) (t : ℝ) : ℝ := (autocorrelation f t).re

/-- Real part of the complete gluing autocorrelation. -/
def realGluingCorrelation {ι : Type*} [Fintype ι]
    (χ : ι → ℝ → ℝ) (f : ℝ → ℂ) (t : ℝ) : ℝ :=
  (gluingCorrelation χ f t).re

theorem realAutocorrelation_localization {ι : Type*} [Fintype ι]
    (χ : ι → ℝ → ℝ) (f : ℝ → ℂ)
    (hf : ∀ t, Integrable (fun x => f (x+t) * star (f x)))
    (hl : ∀ j t, Integrable
      (fun x => localized (χ j) f (x+t) * star (localized (χ j) f x))) :
    (fun t => ∑ j, realAutocorrelation (localized (χ j) f) t) =
      realAutocorrelation f - realGluingCorrelation χ f := by
  ext t
  have h := congrArg Complex.re (sum_autocorrelation_localized χ f t (hf t)
    (fun j => hl j t))
  have hs : (∑ j, autocorrelation (localized (χ j) f) t).re =
      ∑ j, (autocorrelation (localized (χ j) f) t).re :=
    map_sum Complex.reAddGroupHom _ _
  rw [hs, Complex.sub_re] at h
  exact h

/-- The paper's complete finite prime-power gluing formula on actual tests.
The square partition cancels the diagonal exactly. All nonlocal terms remain. -/
theorem primePowerCorrelationValue_localization {ι : Type*} [Fintype ι]
    (N : ℕ) (c : ℝ) (χ : ι → ℝ → ℝ) (f : ℝ → ℂ)
    (hsq : ∀ x, ∑ j, χ j x ^ 2 = 1)
    (hf : ∀ t, Integrable (fun x => f (x+t) * star (f x)))
    (hl : ∀ j t, Integrable
      (fun x => localized (χ j) f (x+t) * star (localized (χ j) f x)))
    (hC : AdmissibleCorrelation (realAutocorrelation f))
    (hR : AdmissibleCorrelation (realGluingCorrelation χ f))
    (hCj : ∀ j, AdmissibleCorrelation (realAutocorrelation (localized (χ j) f))) :
    (∑ j, primePowerCorrelationValue N c (realAutocorrelation (localized (χ j) f))) -
      primePowerCorrelationValue N c (realAutocorrelation f) =
      2 * ∑ n ∈ Finset.range N, primePowerWeight n * realGluingCorrelation χ f (Real.log n) +
      2 * (∫ t, weilGammaKernel t * realGluingCorrelation χ f t ∂positiveMeasure) -
      2 * (∫ t, weilPoleKernel t * realGluingCorrelation χ f t ∂positiveMeasure) := by
  apply correlationValue_gluing (Finset.range N) primePowerWeight
    (fun n => Real.log n) weilPoleKernel weilGammaKernel weilRegulator c
    (realAutocorrelation f) (realGluingCorrelation χ f)
    (fun j => realAutocorrelation (localized (χ j) f))
  · exact realAutocorrelation_localization χ f hf hl
  · simp only [realGluingCorrelation, gluingCorrelation_zero χ f hsq, Complex.zero_re]
  · exact fun j => (hCj j).1
  · exact fun j => (hCj j).2
  · exact hC.1
  · exact hR.1
  · exact hC.2
  · exact hR.2

/-- An old compactly supported correlation is unchanged by extending an already
adequate arithmetic cutoff. The hypothesis records the actual omitted values. -/
theorem primePowerCorrelationValue_cutoff_stable (N M : ℕ) (hNM : N ≤ M)
    (c : ℝ) (C : ℝ → ℝ)
    (hvanish : ∀ n, N ≤ n → n < M → primePowerWeight n * C (Real.log n) = 0) :
    primePowerCorrelationValue N c C = primePowerCorrelationValue M c C := by
  have hs : (∑ n ∈ Finset.range N, primePowerWeight n * C (Real.log n)) =
      ∑ n ∈ Finset.range M, primePowerWeight n * C (Real.log n) := by
    apply Finset.sum_subset (Finset.range_mono hNM)
    intro n hn hnN
    exact hvanish n (by simpa using hnN) (by simpa using hn)
  unfold primePowerCorrelationValue correlationValue
  rw [hs]

end
end RiemannResearch.RH.SignedWeilCorrelation
