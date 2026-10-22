/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.OrdinateSpectralKernel

/-!
# Absolutely convergent ordinate kernels and growing tests

Elementary Fourier analysis of a finite positive atomic measure. The intended
RH consumer weights each actual zero by its summable horizontal displacement.
No zero-distribution input, RH, or vanishing of that displacement is assumed.
Source: the attached unconditional research agenda, priorities 2 and 4;
the proofs use the standard absolute-convergence argument.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.OrdinateSpectralKernel
open ZeroOrdinate
variable {κ ι : Type*}

def infiniteKernel (weight frequency : κ → ℝ) (time : ℝ) : ℂ :=
  ∑' k, (weight k : ℂ) * phase time (frequency k)

def tailMass (weight : κ → ℝ) (samples : Finset κ) : ℝ :=
  ∑' k : {k // k ∉ samples}, weight k

theorem kernelTerm_summable (weight frequency : κ → ℝ)
    (hw : Summable weight) (hpos : ∀ k, 0 ≤ weight k) (time : ℝ) :
    Summable (fun k => (weight k : ℂ) * phase time (frequency k)) := by
  apply hw.of_norm_bounded
  intro k
  simp only [norm_mul, phase_norm, mul_one, Complex.norm_of_nonneg (hpos k)]
  exact le_rfl

theorem infiniteKernel_mass_bound (weight frequency : κ → ℝ)
    (hw : Summable weight) (hpos : ∀ k, 0 ≤ weight k) (time : ℝ) :
    ‖infiniteKernel weight frequency time‖ ≤ ∑' k, weight k := by
  have hn : (fun k => ‖(weight k : ℂ) * phase time (frequency k)‖) = weight := by
    funext k
    rw [norm_mul, phase_norm, mul_one, Complex.norm_of_nonneg (hpos k)]
  have hs : Summable (fun k => ‖(weight k : ℂ) * phase time (frequency k)‖) := by
    rwa [hn]
  simpa only [infiniteKernel, hn] using norm_tsum_le_tsum_norm hs

theorem infiniteKernel_zero (weight frequency : κ → ℝ)
    (hw : Summable weight) :
    infiniteKernel weight frequency 0 = ((∑' k, weight k : ℝ) : ℂ) := by
  simp only [infiniteKernel, phase_zero, mul_one]
  exact (Complex.ofRealCLM.map_tsum hw).symm

theorem kernel_add_tail_exact (weight frequency : κ → ℝ)
    (hw : Summable weight) (hpos : ∀ k, 0 ≤ weight k)
    (samples : Finset κ) (time : ℝ) :
    kernel samples weight frequency time +
      (∑' k : {k // k ∉ samples}, (weight k : ℂ) * phase time (frequency k)) =
      infiniteKernel weight frequency time := by
  exact (kernelTerm_summable weight frequency hw hpos time).sum_add_tsum_compl

theorem infiniteKernel_sub_kernel_bound (weight frequency : κ → ℝ)
    (hw : Summable weight) (hpos : ∀ k, 0 ≤ weight k)
    (samples : Finset κ) (time : ℝ) :
    ‖infiniteKernel weight frequency time - kernel samples weight frequency time‖ ≤
      tailMass weight samples := by
  have he := kernel_add_tail_exact weight frequency hw hpos samples time
  rw [← he, add_sub_cancel_left]
  exact infiniteKernel_mass_bound (fun k : {k // k ∉ samples} => weight k)
    (fun k => frequency k) (hw.subtype _) (fun k => hpos k) time

theorem tailMass_nonneg (weight : κ → ℝ) (hpos : ∀ k, 0 ≤ weight k)
    (samples : Finset κ) : 0 ≤ tailMass weight samples :=
  tsum_nonneg (fun k => hpos k)

theorem tailMass_tendsto_zero (weight : κ → ℝ) :
    Tendsto (tailMass weight) atTop (𝓝 0) :=
  tendsto_tsum_compl_atTop_zero weight

/-- A moving Fourier support costs only its actual coefficient norm.
The omitted infinite tail is retained in `tailMass`. -/
theorem finite_test_tail_bound (weight frequency : κ → ℝ)
    (hw : Summable weight) (hpos : ∀ k, 0 ≤ weight k)
    (samples : Finset κ) (s : Finset ι) (time : ι → ℝ) (a : ι → ℂ) :
    ‖(∑ i ∈ s, a i * infiniteKernel weight frequency (time i)) -
      ∑ i ∈ s, a i * kernel samples weight frequency (time i)‖ ≤
      (∑ i ∈ s, ‖a i‖) * tailMass weight samples := by
  rw [← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  calc
    _ ≤ ∑ i ∈ s, ‖a i * (infiniteKernel weight frequency (time i) -
        kernel samples weight frequency (time i))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖a i‖ * tailMass weight samples := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (infiniteKernel_sub_kernel_bound weight frequency hw hpos samples (time i))
        (norm_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

/-- Growing-support convergence requires the product budget, not merely
pointwise convergence for every fixed character. -/
theorem growing_test_tail_tendsto_zero (weight frequency : κ → ℝ)
    (hw : Summable weight) (hpos : ∀ k, 0 ≤ weight k)
    (samples : ℕ → Finset κ) (s : ℕ → Finset ι)
    (time : ℕ → ι → ℝ) (a : ℕ → ι → ℂ)
    (hbudget : Tendsto (fun n => (∑ i ∈ s n, ‖a n i‖) * tailMass weight (samples n))
      atTop (𝓝 0)) :
    Tendsto (fun n => (∑ i ∈ s n, a n i * infiniteKernel weight frequency (time n i)) -
      ∑ i ∈ s n, a n i * kernel (samples n) weight frequency (time n i))
      atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => finite_test_tail_bound weight frequency hw hpos (samples n) (s n) (time n) (a n))
    hbudget

/-- Every finite Gram test of the infinite kernel is positive semidefinite.
This follows by passing the exact finite nonnegative forms to the limit. -/
theorem infiniteKernel_positive_definite (weight frequency : κ → ℝ)
    (hw : Summable weight) (hpos : ∀ k, 0 ≤ weight k)
    (s : Finset ι) (time : ι → ℝ) (a : ι → ℂ) :
    0 ≤ (ZeroSamplingQuadratic.form s
      (fun i j => infiniteKernel weight frequency (time i - time j)) a).re := by
  have hkernel (t : ℝ) : Tendsto (fun samples : Finset κ =>
      kernel samples weight frequency t) atTop
      (𝓝 (infiniteKernel weight frequency t)) :=
    (kernelTerm_summable weight frequency hw hpos t).hasSum
  have hform : Tendsto (fun samples : Finset κ => ZeroSamplingQuadratic.form s
      (fun i j => kernel samples weight frequency (time i - time j)) a)
      atTop (𝓝 (ZeroSamplingQuadratic.form s
        (fun i j => infiniteKernel weight frequency (time i - time j)) a)) := by
    unfold ZeroSamplingQuadratic.form
    apply tendsto_finsetSum
    intro i hi
    apply tendsto_finsetSum
    intro j hj
    exact tendsto_const_nhds.mul (hkernel (time i - time j))
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hform
  exact ge_of_tendsto hre (Eventually.of_forall (fun samples =>
    kernel_positive_definite s samples weight frequency time a (fun k _ => hpos k)))

end RiemannResearch.Analysis.OrdinateSpectralKernel
