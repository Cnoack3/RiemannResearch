/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PrimeTorusFourierSeries
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Reconstruction from conventional finite-torus Fourier coefficients

The explicit product characters coincide with mathlib's multidimensional
Fourier characters. Its absolute-summability inversion theorem identifies
our continuous series with the original arbitrary continuous test function.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.Analysis.PrimeTorusHaar

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem character_eq_mFourier (k : ι → ℤ) :
    character k = UnitAddTorus.mFourier k := by
  ext x
  exact character_apply k x

/-- Absolute summability of the conventional Fourier coefficients identifies
the continuous series with the original arbitrary continuous function. -/
theorem fourierSeries_mFourierCoeff (f : C(Torus ι, ℂ))
    (ha : Summable (fun k => ‖UnitAddTorus.mFourierCoeff (f : Torus ι → ℂ) k‖)) :
    fourierSeries (UnitAddTorus.mFourierCoeff (f : Torus ι → ℂ)) id = f := by
  simpa only [fourierSeries, id_eq, character_eq_mFourier] using
    (UnitAddTorus.hasSum_mFourier_series_of_summable ha.of_norm).tsum_eq

end RiemannResearch.Analysis.PrimeTorusHaar
