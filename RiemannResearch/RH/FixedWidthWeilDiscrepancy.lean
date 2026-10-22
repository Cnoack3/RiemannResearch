/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.HatMassIntegral
import RiemannResearch.RH.WeilEnergyNormalization
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Actual fixed-width hats and the prime discrepancy

Source: user-provided RH layer-cake continuation, sections 29 and 36--38,
September 2026. The integral and prime expressions here are actual functions,
using the project's von Mangoldt weights and complete arithmetic Weil form.

Support, nonnegativity, and finite-prime cutoff facts below are elementary.
They do not provide the complete analytic calculation of the Laplace transform,
the two-hat Weil identity, or Landau's zero-detection argument. The latter two
are named propositions with no asserted proof. In particular no field silently
postulates that the fixed-width RH-strength bound is true.

Bochner integrals are total definitions. Nonnegativity below does not establish
integrability. Admissibility and all exchanges of integrals/sums needed to prove
`TwoHatWeilIdentity` and `FixedWidthLandauDetection` remain provider obligations.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators
open RiemannResearch.Analysis
open RiemannResearch.RH.SignedWeilCorrelation

namespace RiemannResearch.RH.FixedWidthWeilDiscrepancy

/-- The one fixed width used by the logarithmic mesh program. -/
def fixedHatWidth : ℝ := Real.log 2 / 4

theorem fixedHatWidth_pos : 0 < fixedHatWidth := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold fixedHatWidth
  linarith

theorem two_mul_fixedHatWidth_lt_log_two : 2 * fixedHatWidth < Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold fixedHatWidth
  linarith

/-- Autocorrelation of the actual real centered hat of half-width `h`. -/
def hatCorrelation (h x : ℝ) : ℝ :=
  ∫ u : ℝ, centeredHat h u * centeredHat h (u + x)

/-- The actual diagonal correlation is the squared mass, computed by integration. -/
theorem hatCorrelation_zero {h : ℝ} (hh : 0 < h) :
    hatCorrelation h 0 = 2 * h / 3 := by
  simpa only [hatCorrelation, add_zero, pow_two] using integral_centeredHat_sq hh

theorem hatCorrelation_nonneg (h x : ℝ) : 0 ≤ hatCorrelation h x := by
  apply integral_nonneg
  intro u
  exact mul_nonneg (centeredHat_nonneg h u) (centeredHat_nonneg h (u + x))

/-- Disjoint supports force every pointwise product to vanish, including
touching endpoints, when the centers are at least `2*h` apart. -/
theorem centeredHat_mul_translate_eq_zero {h x : ℝ} (hh : 0 < h)
    (hx : 2 * h ≤ |x|) (u : ℝ) :
    centeredHat h u * centeredHat h (u + x) = 0 := by
  by_cases hu : h ≤ |u|
  · rw [(centeredHat_eq_zero_iff hh).2 hu, zero_mul]
  by_cases hv : h ≤ |u + x|
  · rw [(centeredHat_eq_zero_iff hh).2 hv, mul_zero]
  have hu' : |u| < h := lt_of_not_ge hu
  have hv' : |u + x| < h := lt_of_not_ge hv
  have htri : |x| ≤ |u + x| + |u| := by
    calc
      |x| = |(u + x) - u| := by congr 1; ring
      _ ≤ |u + x| + |u| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (u + x) u
  linarith

theorem hatCorrelation_eq_zero_of_two_mul_le_abs {h x : ℝ} (hh : 0 < h)
    (hx : 2 * h ≤ |x|) : hatCorrelation h x = 0 := by
  have hz := centeredHat_mul_translate_eq_zero hh hx
  simp [hatCorrelation, hz]

/-- The actual positive polar moment; its closed hyperbolic formula is not
required by the definitions and is not asserted in this module. -/
def hatMoment (h : ℝ) : ℝ :=
  ∫ u : ℝ, Real.exp (u / 2) * centeredHat h u

theorem hatMoment_nonneg (h : ℝ) : 0 ≤ hatMoment h := by
  apply integral_nonneg
  intro u
  exact mul_nonneg (Real.exp_pos _).le (centeredHat_nonneg h u)

/-- This strict integer cutoff includes every possible nonzero prime term.
Terms with `log n = x + 2*h` are also zero by the support theorem. -/
def primeDiscrepancyCutoff (h x : ℝ) : ℕ :=
  ⌈Real.exp (x + 2 * h)⌉₊ + 1

theorem exp_lt_primeDiscrepancyCutoff (h x : ℝ) :
    Real.exp (x + 2 * h) < (primeDiscrepancyCutoff h x : ℝ) := by
  have hn : Real.exp (x + 2 * h) ≤ (⌈Real.exp (x + 2 * h)⌉₊ : ℝ) :=
    Nat.le_ceil _
  unfold primeDiscrepancyCutoff
  push_cast
  linarith

/-- The actual discrepancy, using the von Mangoldt weight at every integer;
non-prime-powers and `0,1` have zero weight. -/
def hatPrimeDiscrepancy (h x : ℝ) : ℝ :=
  (∑ n ∈ Finset.range (primeDiscrepancyCutoff h x),
    primePowerWeight n * hatCorrelation h (x - Real.log n)) -
      hatMoment h ^ 2 * Real.exp (x / 2)

theorem primeHatTerm_eq_zero_of_upper_edge {h x : ℝ} (hh : 0 < h)
    (n : ℕ) (hn : x + 2 * h ≤ Real.log n) :
    primePowerWeight n * hatCorrelation h (x - Real.log n) = 0 := by
  have hs : 2 * h ≤ |x - Real.log n| := by
    have ha := neg_le_abs (x - Real.log n)
    linarith
  rw [hatCorrelation_eq_zero_of_two_mul_le_abs hh hs, mul_zero]

theorem primeHatTerm_eq_zero_of_lower_edge {h x : ℝ} (hh : 0 < h)
    (n : ℕ) (hn : Real.log n ≤ x - 2 * h) :
    primePowerWeight n * hatCorrelation h (x - Real.log n) = 0 := by
  have hs : 2 * h ≤ |x - Real.log n| := by
    have ha := le_abs_self (x - Real.log n)
    linarith
  rw [hatCorrelation_eq_zero_of_two_mul_le_abs hh hs, mul_zero]

/-- The actual finite cutoff equals the complete locally finite arithmetic sum.
This assertion needs no unproved asymptotic prime distribution estimate. -/
theorem hatPrimeDiscrepancy_eq_tsum {h : ℝ} (hh : 0 < h) (x : ℝ) :
    hatPrimeDiscrepancy h x =
      (∑' n : ℕ, primePowerWeight n * hatCorrelation h (x - Real.log n)) -
        hatMoment h ^ 2 * Real.exp (x / 2) := by
  have hs : (∑' n : ℕ, primePowerWeight n * hatCorrelation h (x - Real.log n)) =
      ∑ n ∈ Finset.range (primeDiscrepancyCutoff h x),
        primePowerWeight n * hatCorrelation h (x - Real.log n) := by
    apply tsum_eq_sum
    intro n hn
    have hnN : primeDiscrepancyCutoff h x ≤ n :=
      Nat.le_of_not_lt (by simpa only [Finset.mem_range] using hn)
    have hne : Real.exp (x + 2 * h) < (n : ℝ) :=
      lt_of_lt_of_le (exp_lt_primeDiscrepancyCutoff h x) (by exact_mod_cast hnN)
    have hnp : 0 < (n : ℝ) := lt_trans (Real.exp_pos _) hne
    exact primeHatTerm_eq_zero_of_upper_edge hh n
      ((Real.le_log_iff_exp_le hnp).2 hne.le)
  unfold hatPrimeDiscrepancy
  rw [hs]

theorem hatPrimeDiscrepancy_ge_negative_pole (h x : ℝ) :
    -(hatMoment h ^ 2 * Real.exp (x / 2)) ≤ hatPrimeDiscrepancy h x := by
  have hs : 0 ≤ ∑ n ∈ Finset.range (primeDiscrepancyCutoff h x),
      primePowerWeight n * hatCorrelation h (x - Real.log n) := by
    apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg (primePowerWeight_nonneg n) (hatCorrelation_nonneg _ _)
  unfold hatPrimeDiscrepancy
  linarith

/-- The decaying archimedean remainder after the leading pole cancellation. -/
def archimedeanHatRemainder (h x : ℝ) : ℝ :=
  ∫ u : ℝ, (Real.exp (-5 * u / 2) / (1 - Real.exp (-2 * u))) *
    hatCorrelation h (x - u) ∂positiveMeasure

theorem archimedeanHatRemainder_nonneg (h x : ℝ) :
    0 ≤ archimedeanHatRemainder h x := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have he : Real.exp (-2 * u) ≤ 1 := by
    have hh : -2 * u ≤ 0 := by linarith [show 0 < u from hu]
    simpa using Real.exp_le_exp.mpr hh
  exact mul_nonneg
    (div_nonneg (Real.exp_pos _).le (sub_nonneg.mpr he))
    (hatCorrelation_nonneg h (x - u))

/-- The completed arithmetic Weil form with its exact diagonal constant.
Its identification with a zero-side distribution is a separate analytic theorem. -/
def completedWeilForm (f : ℝ → ℂ) : ℝ :=
  infinitePrimePowerCorrelationValue
    (Real.eulerMascheroniConstant + Real.log (4 * Real.pi))
    (realAutocorrelation f)

def hatTest (h : ℝ) (u : ℝ) : ℂ := (centeredHat h u : ℂ)

/-- The plus combination at the original fixed width, with separation `x`. -/
def twoHatTest (h x : ℝ) (u : ℝ) : ℂ :=
  hatTest h u + hatTest h (u - x)

/-- OPEN analytic provider: the exact completed two-hat formula (38.3).
Defining this proposition does not prove the identity or admissibility. -/
def TwoHatWeilIdentity (h : ℝ) : Prop :=
  ∀ x : ℝ, 2 * h < x →
    completedWeilForm (twoHatTest h x) =
      2 * completedWeilForm (hatTest h) - 2 * hatPrimeDiscrepancy h x -
        2 * archimedeanHatRemainder h x

/-- OPEN analytic provider: a right-strip zero forces the actual fixed-width
discrepancy above every polynomial arbitrarily far out. This is the one-sided
Landau/Laplace detection implication; it is not an assertion that RH holds.
The intended analytic width assumptions are `0 < h` and `2*h < log 2`.
They must be used to prove a provider, not hidden inside the definition. -/
def FixedWidthLandauDetection (h : ℝ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → (1 / 2 : ℝ) < ρ.re → ρ.re < 1 →
    ∀ C : ℝ, 0 ≤ C → ∀ A : ℕ, ∀ R : ℝ,
      ∃ x : ℝ, 0 ≤ x ∧ R ≤ x ∧ C * (1 + x) ^ A < hatPrimeDiscrepancy h x

/-- The algebraic implication needed by the fixed-width RH reduction, with
the actual two-hat identity retained as an explicit provider hypothesis. -/
theorem hatPrimeDiscrepancy_le_of_twoHat_lower {h x B : ℝ}
    (hidentity : TwoHatWeilIdentity h) (hx : 2 * h < x)
    (hlower : -B ≤ completedWeilForm (twoHatTest h x)) :
    hatPrimeDiscrepancy h x ≤ completedWeilForm (hatTest h) + B / 2 := by
  have hi := hidentity x hx
  have hj := archimedeanHatRemainder_nonneg h x
  linarith

end RiemannResearch.RH.FixedWidthWeilDiscrepancy
