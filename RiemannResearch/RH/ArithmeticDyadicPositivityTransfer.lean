/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.DyadicL2Density
import RiemannResearch.Analysis.CompactKernelQuadraticContinuity
import RiemannResearch.Analysis.ComplexKernelQuadratic
import RiemannResearch.RH.ArithmeticScrewKernel

/-!
# Conditional arithmetic dyadic positivity transfer

Source: user-provided task, supports the dense-test transfer statement.
The proof combines the verified constructive dyadic L2 density theorem with
the verified compact-kernel quadratic continuity theorem.

This is a conditional research reduction for the defined elementary arithmetic
screw function, not an identification with the completed Weil form. The signed
prime-power, gamma, polar and linear terms and the exact unnormalized Haar
matrix are unchanged. Arithmetic positivity and the Weil identity remain
separate obligations; the complex transfer below makes no RH claim.
The existing density theorem includes the zero-radius case and the literal
Ioc boundary convention. The limiting step below is proved, not assumed.
-/

open scoped BigOperators
open MeasureTheory Set Filter
open RiemannResearch.Analysis
open RiemannResearch.RH.PrimeGapCurvature

namespace RiemannResearch.RH

/-- Positivity on every literal real dyadic Haar step transfers to every real,
integrable, square-integrable, mean-zero test on the same compact window.
The arithmetic positivity premise is not proved by this theorem. -/
theorem arithmeticScrew_quadratic_nonneg_of_dyadicHaarStep_nonneg
    {R : ℝ} (hR : 0 ≤ R)
    (hpos : ∀ (m : ℕ) (c : FiniteDyadicHaarIndex m → ℝ),
      0 ≤ realKernelQuadratic (fun x y => arithmeticScrewFunction (x - y))
        (dyadicHaarStep R m c))
    {u : ℝ → ℝ} (hu : Integrable u)
    (hu2 : Integrable (fun x => u x ^ 2))
    (hus : ∀ x ∉ Icc (-R) R, u x = 0)
    (hu0 : (∫ x, u x) = 0) :
    0 ≤ realKernelQuadratic (fun x y => arithmeticScrewFunction (x - y)) u := by
  obtain ⟨c, hc, hlim⟩ :=
    exists_dyadicHaarStep_tendsto_sq_error hR hu hu2 hus hu0
  have huLp : MemLp u 2 :=
    (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).2 hu2
  have hv (m : ℕ) : Integrable (dyadicHaarStep R m (c m)) := by
    simpa only [mul_one] using
      integrable_dyadicHaarStep_mul_continuous R m (c m)
        (fun _ => (1 : ℝ)) continuous_const
  have hd2 (m : ℕ) :
      Integrable (fun x => (dyadicHaarStep R m (c m) x - u x) ^ 2) := by
    rw [hc m]
    exact ((memLp_dyadicAverageStep R m u).sub huLp).integrable_sq
  have hvs (m : ℕ) : ∀ x ∉ Icc (-R) R, dyadicHaarStep R m (c m) x = 0 := by
    intro x hx
    rw [hc m]
    exact dyadicAverageStep_eq_zero_of_not_mem hR m u hx
  exact realKernelQuadratic_nonneg_of_approx hR
    (continuous_arithmeticScrewFunction.comp (continuous_fst.sub continuous_snd))
    hu hv hd2 hus hvs hlim (fun m => hpos m (c m))

/-- Matrix-facing form of the conditional transfer, using the exact existing
cell-integral reconstruction and the original unnormalized Haar compression.
Nonnegativity at all levels and coefficients remains an explicit hypothesis. -/
theorem arithmeticScrew_quadratic_nonneg_of_haarMatrix_nonneg
    {R : ℝ} (hR : 0 ≤ R)
    (hpos : ∀ (m : ℕ) (c : FiniteDyadicHaarIndex m → ℝ),
      0 ≤ dotProduct c ((arithmeticScrewHaarMatrix R m).mulVec c))
    {u : ℝ → ℝ} (hu : Integrable u)
    (hu2 : Integrable (fun x => u x ^ 2))
    (hus : ∀ x ∉ Icc (-R) R, u x = 0)
    (hu0 : (∫ x, u x) = 0) :
    0 ≤ realKernelQuadratic (fun x y => arithmeticScrewFunction (x - y)) u := by
  apply arithmeticScrew_quadratic_nonneg_of_dyadicHaarStep_nonneg hR _ hu hu2 hus hu0
  intro m c
  change 0 ≤ ∫ x, dyadicHaarStep R m c x *
    (∫ y, arithmeticScrewFunction (x - y) * dyadicHaarStep R m c y)
  rw [dyadicHaarStep_quadratic_reconstruction hR m
    (fun x y => arithmeticScrewFunction (x - y))
    (continuous_arithmeticScrewFunction.comp (continuous_fst.sub continuous_snd)) c]
  exact hpos m c

/-- All-level positivity of the exact real arithmetic Haar matrices also
transfers to the conjugate-first complex quadratic form on the same window.
The conclusion is stated through real and imaginary parts because ℂ is not ordered. -/
theorem arithmeticScrew_complexQuadratic_nonneg_of_haarMatrix_nonneg
    {R : ℝ} (hR : 0 ≤ R)
    (hpos : ∀ (m : ℕ) (c : FiniteDyadicHaarIndex m → ℝ),
      0 ≤ dotProduct c ((arithmeticScrewHaarMatrix R m).mulVec c))
    {u : ℝ → ℂ} (hu : Integrable u)
    (hur2 : Integrable (fun x => (u x).re ^ 2))
    (hui2 : Integrable (fun x => (u x).im ^ 2))
    (hus : ∀ x ∉ Icc (-R) R, u x = 0)
    (hu0 : (∫ x, u x) = 0) :
    (complexKernelQuadratic
      (fun x y => arithmeticScrewFunction (x - y)) u).im = 0 ∧
      0 ≤ (complexKernelQuadratic
        (fun x y => arithmeticScrewFunction (x - y)) u).re := by
  apply complexKernelQuadratic_nonneg_of_real_meanZero_nonneg
    (k := fun x y => arithmeticScrewFunction (x - y))
    (continuous_arithmeticScrewFunction.comp (continuous_fst.sub continuous_snd))
    _ _ hu hur2 hui2 hus hu0
  · intro x y
    rw [show x - y = -(y - x) by ring, arithmeticScrewFunction_neg]
  · intro f hf hf2 hfs hf0
    exact arithmeticScrew_quadratic_nonneg_of_haarMatrix_nonneg
      hR hpos hf hf2 hfs hf0

end RiemannResearch.RH
