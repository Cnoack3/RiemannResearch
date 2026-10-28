/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.FiniteTorusWiener

/-!
# Haar Plancherel and the dense A2 inclusion into L2

Source: the user's prime-torus Plancherel question (2026-10-28),
Mathlib finite-torus Fourier theory, and the cited project modules.
-/


noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace RiemannResearch.Analysis.PrimeTorusHaar
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem haar_eq_volume : haar ι = (volume : Measure (Torus ι)) := by rfl

theorem hasSum_sq_mFourierCoeff_continuous (f : C(Torus ι, ℂ)) :
    HasSum (fun k : ι → ℤ => ‖UnitAddTorus.mFourierCoeff (f : Torus ι → ℂ) k‖ ^ 2)
      (∫ x, ‖f x‖ ^ 2 ∂haar ι) := by
  have h := UnitAddTorus.hasSum_sq_mFourierCoeff (f.toLp 2 volume ℂ)
  simp only [UnitAddTorus.mFourierCoeff_toLp] at h
  rw [haar_eq_volume]
  convert h using 1
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume f] with x hx
  rw [hx]

theorem hasSum_prod_mFourierCoeff_continuous (f g : C(Torus ι, ℂ)) :
    HasSum (fun k : ι → ℤ =>
      UnitAddTorus.mFourierCoeff (f : Torus ι → ℂ) k *
        conj (UnitAddTorus.mFourierCoeff (g : Torus ι → ℂ) k))
      (haarIntegral (f * star g)) := by
  have h := UnitAddTorus.hasSum_prod_mFourierCoeff
    (g.toLp 2 volume ℂ) (f.toLp 2 volume ℂ)
  simp only [UnitAddTorus.mFourierCoeff_toLp] at h
  have hi : (∫ x, conj ((g.toLp 2 volume ℂ) x) *
      ((f.toLp 2 volume ℂ) x) ∂volume) = haarIntegral (f * star g) := by
    rw [haarIntegral_apply, haar_eq_volume]
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume f,
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume g] with x hxf hxg
    change conj ((g.toLp 2 volume ℂ) x) *
      ((f.toLp 2 volume ℂ) x) = f x * conj (g x)
    rw [hxf, hxg, mul_comm]
  rw [hi] at h
  exact h.congr_fun (fun k => mul_comm _ _)

end RiemannResearch.Analysis.PrimeTorusHaar

namespace RiemannResearch.Analysis.PrimeTorusHaar
open Filter MeasureTheory FiniteTorusWiener
open scoped Topology BigOperators ENNReal
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem haarIntegral_mul_star_self (f : C(Torus ι, ℂ)) :
    haarIntegral (f * star f) =
      ((∑' k : ι → ℤ, ‖coeff f k‖ ^ 2 : ℝ) : ℂ) := by
  have h := (hasSum_prod_mFourierCoeff_continuous f f).tsum_eq
  rw [← h]
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_tsum]

theorem denseRange_a2_toLp (ell : ι → ℝ) :
    DenseRange (fun f : {f : C(Torus ι, ℂ) // MemA2 ell f} =>
      f.1.toLp 2 volume ℂ) := by
  intro F
  let a : (ι → ℤ) → ℂ := UnitAddTorus.mFourierCoeff (F : Torus ι → ℂ)
  let q (s : Finset (ι → ℤ)) : {f : C(Torus ι, ℂ) // MemA2 ell f} :=
    ⟨∑ k ∈ s, a k • character k, memA2_fourierPolynomial ell s a⟩
  have h : Tendsto
      (fun s : Finset (ι → ℤ) => ∑ k ∈ s, a k • UnitAddTorus.mFourierLp 2 k)
      atTop (𝓝 F) := UnitAddTorus.hasSum_mFourier_series_L2 F
  have hq (s : Finset (ι → ℤ)) :
      (q s).1.toLp 2 volume ℂ =
        ∑ k ∈ s, a k • UnitAddTorus.mFourierLp 2 k := by
    change (ContinuousMap.toLp 2 volume ℂ) (∑ k ∈ s, a k • character k) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [map_smul]
    congr 1
    rw [character_eq_mFourier]
  have ht : Tendsto (fun s : Finset (ι → ℤ) => (q s).1.toLp 2 volume ℂ)
      atTop (𝓝 F) := by
    convert h using 1
    funext s
    exact hq s
  exact mem_closure_of_tendsto ht
    (Filter.Eventually.of_forall (fun s => ⟨q s, rfl⟩))

theorem a2_toLp_injective (ell : ι → ℝ) :
    Function.Injective (fun f : {f : C(Torus ι, ℂ) // MemA2 ell f} =>
      f.1.toLp 2 volume ℂ) := by
  intro f g h
  apply Subtype.ext
  exact ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) volume h

theorem character_haar_energy (k : ι → ℤ) :
    (∫ x : Torus ι, ‖character k x‖^2 ∂haar ι) = 1 := by
  simp only [norm_character_apply, one_pow]
  simp

theorem a2Mass_sq_ne_haar_energy_character (ell : ι → ℝ) (k : ι → ℤ)
    (hk : 0 < height ell k) :
    (a2Mass ell (character k))^2 ≠
      ∫ x : Torus ι, ‖character k x‖^2 ∂haar ι := by
  rw [a2Mass_character, character_haar_energy]
  have hw : 1 < weight ell k := by unfold weight; linarith
  have hw2 : 1 < (weight ell k)^2 := by nlinarith
  have hw4 : 1 < ((weight ell k)^2)^2 := by nlinarith
  exact ne_of_gt hw4

end RiemannResearch.Analysis.PrimeTorusHaar
