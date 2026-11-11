/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PrimeTorusFourierProducts
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# Centered finite prime-torus measure functionals

Source: Section 7, Proposition 9 of the user's FRZ strengthening note.
Centering removes only the Haar component. The nonconstant characters determine
the entire centered continuous functional, by finite-torus Fourier density.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace RiemannResearch.Analysis.PrimeTorusCenteredMeasure
open PrimeTorusHaar ZeroOrdinate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem continuousMap_integrable (μ : Measure (Torus ι)) [IsFiniteMeasure μ]
    (f : C(Torus ι, ℂ)) : Integrable f μ :=
  (integrable_const ‖f‖).mono' f.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm x))

def integralMap (μ : FiniteMeasure (Torus ι)) : C(Torus ι, ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∫ x, f x ∂(μ : Measure (Torus ι))
  map_add' f g := integral_add (continuousMap_integrable _ f) (continuousMap_integrable _ g)
  map_smul' c f := by
    simp only [ContinuousMap.smul_apply, integral_smul, RingHom.id_apply]

theorem real_mass (μ : FiniteMeasure (Torus ι)) :
    (μ : Measure (Torus ι)).real Set.univ = (μ.mass : ℝ) := by
  rw [measureReal_def, ← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal]

def integralCLM (μ : FiniteMeasure (Torus ι)) : C(Torus ι, ℂ) →L[ℂ] ℂ :=
  (integralMap μ).mkContinuous μ.mass (fun f => by
    simpa only [integralMap, LinearMap.coe_mk, AddHom.coe_mk, real_mass, mul_comm] using
      (norm_integral_le_of_norm_le_const (μ := (μ : Measure (Torus ι)))
        (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm x))))

@[simp] theorem integralCLM_apply (μ : FiniteMeasure (Torus ι)) (f : C(Torus ι, ℂ)) :
    integralCLM μ f = ∫ x, f x ∂(μ : Measure (Torus ι)) := rfl

def centeredIntegral (μ : FiniteMeasure (Torus ι)) : C(Torus ι, ℂ) →L[ℂ] ℂ :=
  integralCLM μ - ((μ.mass : ℝ) : ℂ) • integralCLM ⟨haar ι, inferInstance⟩

theorem centeredIntegral_apply (μ : FiniteMeasure (Torus ι)) (f : C(Torus ι, ℂ)) :
    centeredIntegral μ f =
      (∫ x, f x ∂(μ : Measure (Torus ι))) - ((μ.mass : ℝ) : ℂ) * haarIntegral f := rfl

theorem centeredIntegral_eq_of_haar_zero (μ : FiniteMeasure (Torus ι))
    (f : C(Torus ι, ℂ)) (hf : haarIntegral f = 0) :
    centeredIntegral μ f = ∫ x, f x ∂(μ : Measure (Torus ι)) := by
  rw [centeredIntegral_apply, hf, mul_zero, sub_zero]

theorem centeredIntegral_character (μ : FiniteMeasure (Torus ι)) (k : ι → ℤ)
    (hk : k ≠ 0) :
    centeredIntegral μ (character k) =
      ∫ x, character k x ∂(μ : Measure (Torus ι)) := by
  apply centeredIntegral_eq_of_haar_zero
  rw [haarIntegral_character_eq, if_neg hk]

theorem centeredIntegral_one (μ : FiniteMeasure (Torus ι)) :
    centeredIntegral μ 1 = 0 := by
  rw [centeredIntegral_apply]
  change (∫ _x, (1 : ℂ) ∂(μ : Measure (Torus ι))) -
    ((μ.mass : ℝ) : ℂ) * (∫ _x, (1 : ℂ) ∂haar ι) = 0
  simp only [integral_const, Complex.real_smul, mul_one, real_mass]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, Complex.ofReal_one,
    mul_one, sub_self]

theorem centeredIntegral_ext (μ ν : FiniteMeasure (Torus ι))
    (h : ∀ k : ι → ℤ, k ≠ 0 →
      (∫ x, character k x ∂(μ : Measure (Torus ι))) =
      ∫ x, character k x ∂(ν : Measure (Torus ι))) :
    centeredIntegral μ = centeredIntegral ν := by
  apply ContinuousLinearMap.ext_on (s := Set.range (character (ι := ι)))
  · rw [show character (ι := ι) = UnitAddTorus.mFourier by
      funext k; exact character_eq_mFourier k]
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
      UnitAddTorus.span_mFourier_closure_eq_top]
    rfl
  · rintro _ ⟨k, rfl⟩
    by_cases hk : k = 0
    · subst k
      have hc : character (0 : ι → ℤ) = 1 := by
        ext x
        simp [character_apply, fourier_zero]
      rw [hc, centeredIntegral_one, centeredIntegral_one]
    · rw [centeredIntegral_character μ k hk, centeredIntegral_character ν k hk]
      exact h k hk


def haarFinite : FiniteMeasure (Torus ι) := ⟨haar ι, inferInstance⟩

/-- A positive Haar measure has zero centered functional. Thus centered
third corrections cannot detect a surviving constant Haar component. -/
theorem centeredIntegral_haar (f : C(Torus ι, ℂ)) :
    centeredIntegral (haarFinite (ι := ι)) f = 0 := by
  rw [centeredIntegral_apply]
  have hm : ((haarFinite (ι := ι)).mass : ℝ) = 1 := by
    rw [← real_mass]
    change (haar ι).real Set.univ = 1
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one]
  rw [hm]
  change haarIntegral f - (1 : ℂ) * haarIntegral f = 0
  ring

end RiemannResearch.Analysis.PrimeTorusCenteredMeasure
