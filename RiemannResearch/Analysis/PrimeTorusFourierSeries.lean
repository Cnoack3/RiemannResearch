/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PrimeTorusHaarSpecialization
import RiemannResearch.Analysis.ActualZeroOrdinate

/-!
# Absolutely summable Fourier series on the finite prime torus

The Fourier series here is an actual continuous function obtained as a
convergent series in the supremum norm. Continuous linear maps justify every
interchange with product Haar integration and the actual finite, multiplicity
weighted zero sample. This module does not assume an arithmetic limit.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.Analysis.PrimeTorusHaar
open RiemannResearch.Analysis.PoissonHaar
open RiemannResearch.Analysis.ZeroOrdinate
open Zeta23

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem norm_character_apply (k : ι → ℤ) (x : Torus ι) :
    ‖character k x‖ = 1 := by
  simp [character_apply, norm_prod, fourier_apply, Circle.norm_coe]

theorem norm_character_le (k : ι → ℤ) : ‖character k‖ ≤ 1 := by
  apply ((character k).norm_le (by norm_num)).2
  intro x
  rw [norm_character_apply]

def fourierSeries (a : κ → ℂ) (k : κ → ι → ℤ) : C(Torus ι, ℂ) :=
  ∑' j, a j • character (k j)

theorem summable_fourierSeries (a : κ → ℂ) (k : κ → ι → ℤ)
    (ha : Summable (fun j => ‖a j‖)) :
    Summable (fun j => a j • character (k j)) := by
  apply Summable.of_norm_bounded ha
  intro j
  rw [norm_smul]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (norm_character_le (k j)) (norm_nonneg (a j))

theorem fourierSeries_apply (a : κ → ℂ) (k : κ → ι → ℤ)
    (ha : Summable (fun j => ‖a j‖)) (x : Torus ι) :
    fourierSeries a k x = ∑' j, a j * character (k j) x := by
  simpa [fourierSeries, smul_eq_mul] using
    (ContinuousMap.evalCLM ℂ x).map_tsum (summable_fourierSeries a k ha)

def torusHaarIntegralCLM : C(Torus ι, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous (haarIntegral : C(Torus ι, ℂ) →ₗ[ℂ] ℂ) 1
    (fun f => by simpa only [haarIntegral, one_mul] using
      probabilityIntegral_bound (haar ι) f)

@[simp] theorem torusHaarIntegralCLM_apply (f : C(Torus ι, ℂ)) :
    torusHaarIntegralCLM f = haarIntegral f := rfl

theorem haarIntegral_fourierSeries (a : κ → ℂ) (k : κ → ι → ℤ)
    (ha : Summable (fun j => ‖a j‖)) :
    haarIntegral (fourierSeries a k) =
      ∑' j, a j * (if k j = 0 then 1 else 0) := by
  simpa only [fourierSeries, torusHaarIntegralCLM_apply, map_smul,
    smul_eq_mul, haarIntegral_character_eq] using
    torusHaarIntegralCLM.map_tsum (summable_fourierSeries a k ha)

def densityIntegralCLM (c r : ι → ℝ) : C(Torus ι, ℂ) →L[ℂ] ℂ :=
  torusHaarIntegralCLM.comp
    ((ContinuousLinearMap.mul ℂ C(Torus ι, ℂ)) (density c r))

@[simp] theorem densityIntegralCLM_apply (c r : ι → ℝ) (f : C(Torus ι, ℂ)) :
    densityIntegralCLM c r f = haarIntegral (f * density c r) := by
  simp [densityIntegralCLM, mul_comm]

theorem haarIntegral_fourierSeries_density (a : κ → ℂ) (k : κ → ι → ℤ)
    (ha : Summable (fun j => ‖a j‖)) (c r : ι → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1) :
    haarIntegral (fourierSeries a k * density c r) =
      ∑' j, a j * axisMultiplier c r (k j) := by
  simpa only [fourierSeries, densityIntegralCLM_apply, map_smul,
    smul_eq_mul, haarIntegral_character_density c r hr hr1] using
    (densityIntegralCLM c r).map_tsum (summable_fourierSeries a k ha)

def actualSampleCLM (orbit : ℝ → Torus ι) (T : ℝ) : C(Torus ι, ℂ) →L[ℂ] ℂ := by
  classical
  exact ∑ ρ ∈ ActualZeroOrdinate.cutoff T,
    (zeroMult ρ : ℂ) • ContinuousMap.evalCLM ℂ (orbit ρ.im)

@[simp] theorem actualSampleCLM_apply (orbit : ℝ → Torus ι) (T : ℝ)
    (f : C(Torus ι, ℂ)) :
    actualSampleCLM orbit T f =
      ActualZeroOrdinate.sum T (fun ρ => f (orbit ρ.im)) := by
  classical
  simp [actualSampleCLM, ActualZeroOrdinate.sum]

def actualDiscrepancyCLM (orbit : ℝ → Torus ι) (T : ℝ) :
    C(Torus ι, ℂ) →L[ℂ] ℂ :=
  (T : ℂ)⁻¹ • (actualSampleCLM orbit T - (Ncount 0 T : ℂ) • torusHaarIntegralCLM)

@[simp] theorem actualDiscrepancyCLM_apply (orbit : ℝ → Torus ι) (T : ℝ)
    (f : C(Torus ι, ℂ)) :
    actualDiscrepancyCLM orbit T f =
      (ActualZeroOrdinate.sum T (fun ρ => f (orbit ρ.im)) -
        (Ncount 0 T : ℂ) * haarIntegral f) / (T : ℂ) := by
  simp [actualDiscrepancyCLM, div_eq_mul_inv, mul_comm]

/-- Exact exchange of the infinite Fourier series with the actual centered
zero statistic; all zero multiplicities and the Haar constant are retained. -/
theorem actualDiscrepancy_fourierSeries (a : κ → ℂ) (k : κ → ι → ℤ)
    (ha : Summable (fun j => ‖a j‖)) (orbit : ℝ → Torus ι) (T : ℝ) :
    (ActualZeroOrdinate.sum T (fun ρ => fourierSeries a k (orbit ρ.im)) -
      (Ncount 0 T : ℂ) * haarIntegral (fourierSeries a k)) / (T : ℂ) =
      ∑' j, a j * ((ActualZeroOrdinate.sum T
        (fun ρ => character (k j) (orbit ρ.im)) -
          (Ncount 0 T : ℂ) * (if k j = 0 then 1 else 0)) / (T : ℂ)) := by
  simpa only [fourierSeries, actualDiscrepancyCLM_apply, map_smul,
    smul_eq_mul, haarIntegral_character_eq] using
    (actualDiscrepancyCLM orbit T).map_tsum (summable_fourierSeries a k ha)

end RiemannResearch.Analysis.PrimeTorusHaar
