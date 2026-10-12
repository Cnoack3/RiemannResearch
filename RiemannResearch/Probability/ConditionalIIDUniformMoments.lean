/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Probability.ConditionalIIDUniformModel
import RiemannResearch.Analysis.CesaroFiniteCalculus
import Mathlib.Probability.CondVar

/-! Actual conditional coordinate distributions and arithmetic conditional means. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Probability.ConditionalIID

/-- The exact uniform atomic probabilities, including the null zero coordinate. -/
theorem uniformLaw_singleton (k n : ℕ) :
    uniformLaw k {n} = if 1 ≤ n ∧ n ≤ k + 1 then (k + 1 : ℝ≥0∞)⁻¹ else 0 := by
  rw [uniformLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton n)]
  simp [uniformPMF, PMF.uniformOfFinset_apply, Nat.card_Icc]

theorem uniformLaw_support (k : ℕ) :
    ∀ᵐ n ∂uniformLaw k, n ∈ Finset.Icc 1 (k + 1) := by
  rw [ae_iff]
  rw [uniformLaw_apply]
  calc
    _ = (0 : ℝ≥0∞) / (k + 1 : ℝ≥0∞) := by
      congr 1
      norm_cast
      apply Finset.card_eq_zero.mpr
      ext n
      simp
    _ = 0 := by simp

theorem uniformLaw_restrict (k : ℕ) :
    (uniformLaw k).restrict (↑(Finset.Icc 1 (k + 1)) : Set ℕ) = uniformLaw k :=
  Measure.restrict_eq_self_of_ae_mem (uniformLaw_support k)

/-- Every real arithmetic function is integrable on each finite conditional fiber. -/
theorem uniform_integrable (k : ℕ) (F : ℕ → ℝ) : Integrable F (uniformLaw k) := by
  have h : IntegrableOn F (↑(Finset.Icc 1 (k + 1)) : Set ℕ) (uniformLaw k) :=
    IntegrableOn.finset
  simpa only [IntegrableOn, uniformLaw_restrict] using h

/-- Uniform-fiber integration is exactly arithmetic Cesaro averaging. -/
theorem uniform_integral (k : ℕ) (F : ℕ → ℝ) :
    (∫ n, F n ∂uniformLaw k) = cesaro F (k + 1) := by
  calc
    _ = ∫ n in (↑(Finset.Icc 1 (k + 1)) : Set ℕ), F n ∂uniformLaw k := by
      rw [uniformLaw_restrict]
    _ = ∑ n ∈ Finset.Icc 1 (k + 1), (uniformLaw k).real {n} • F n :=
      setIntegral_finset _ IntegrableOn.finset
    _ = cesaro F (k + 1) := by
      unfold cesaro
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro n hn
      have hn' : 1 ≤ n ∧ n ≤ k + 1 := Finset.mem_Icc.mp hn
      simp [Measure.real, uniformLaw_singleton, hn', smul_eq_mul,
        div_eq_mul_inv, mul_comm, ENNReal.toReal_add]

/-- Each coordinate of the infinite product has its prescribed one-dimensional integral. -/
theorem path_integral_coordinate (k i : ℕ) (F : ℕ → ℝ) :
    (∫ x : Path, F (x i) ∂pathLaw k) = cesaro F (k + 1) := by
  have hm : StronglyMeasurable F := (measurable_of_countable F).stronglyMeasurable
  have h := integral_map_of_stronglyMeasurable (μ := pathLaw k)
    (measurable_pi_apply i) hm
  rw [show Measure.map (fun x : Path => x i) (pathLaw k) = uniformLaw k from
    Measure.infinitePi_map_eval _ i, uniform_integral] at h
  exact h.symm

/-- Actual conditional means, assuming exactly the required global integrability. -/
theorem conditional_coordinate_expectation (i : ℕ) (F : ℕ → ℝ)
    (hF : Integrable (fun ω => F (coordinate i ω)) probability) :
    probability[(fun ω => F (coordinate i ω)) | latentSigma] =ᵐ[probability]
      (fun ω => cesaro F (endpoint ω)) := by
  have hm : StronglyMeasurable (fun x : Path => F (x i)) :=
    ((measurable_of_countable F).comp (measurable_pi_apply i)).stronglyMeasurable
  have h := conditional_path_expectation (fun x => F (x i)) hm hF
  filter_upwards [h] with ω hω
  rw [hω, path_integral_coordinate]
  rfl

/-- Conditional distributions are identical across all sample indices. -/
theorem conditional_coordinate_law (i : ℕ) :
    (fun k => condDistrib (coordinate i) latentIndex probability k)
      =ᵐ[Measure.map latentIndex probability] uniformLaw := by
  have hc := condDistrib_comp (μ := probability) (mβ := (inferInstance : MeasurableSpace ℕ))
    latentIndex
    (Y := (Prod.snd : Omega → Path)) measurable_snd.aemeasurable (measurable_pi_apply i)
  filter_upwards [hc, conditional_path_law] with k hk hp
  change condDistrib ((fun x : Path => x i) ∘ Prod.snd) latentIndex probability k = _
  rw [hk, Kernel.map_apply _ (measurable_pi_apply i), hp]
  exact Measure.infinitePi_map_eval _ i

end RiemannResearch.Probability.ConditionalIID
