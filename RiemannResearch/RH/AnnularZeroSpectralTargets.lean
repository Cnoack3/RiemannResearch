import RiemannResearch.RH.AnnularPrimePairTargets
import RiemannResearch.Analysis.TwistedRieszFilterAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Complete zero data, actual Riesz vectors, and spectral obligations

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

Provider definitions name propositions; they supply neither proofs nor axioms.
FullZeroData expressly covers all strip zeros and
identifies multiplicities. It does not select only critical-line zeros.

Source: the October 9 centered-arithmetic report, Sections 5--11 and 18--21.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.AnnularZeroSpectral
open AnnularPrimePair
open RiemannResearch.Analysis.AnnularMellin

structure FullZeroData (ι : Type*) where
  rho : ι → ℂ
  multiplicity : ι → ℕ
  distinct : Function.Injective rho
  is_zero : ∀ i, riemannZeta (rho i) = 0
  strip_left : ∀ i, 0 < (rho i).re
  strip_right : ∀ i, (rho i).re < 1
  multiplicity_pos : ∀ i, 0 < multiplicity i
  multiplicity_correct :
    ∀ i, analyticOrderAt riemannZeta (rho i) = (multiplicity i : ℕ∞)
  covers :
    ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      ∃ i, rho i = z

def annularCoefficient {ι : Type*} (D : FullZeroData ι) (i : ι) : ℂ :=
  -(D.multiplicity i : ℂ) * multiplier (D.rho i)

theorem annularCoefficient_ne_zero {ι : Type*}
    (D : FullZeroData ι) (i : ι) : annularCoefficient D i ≠ 0 :=
  full_zero_coefficient_ne_zero (D.strip_left i) (D.multiplicity_pos i)

def zeroRealSup {ι : Type*} (D : FullZeroData ι) : ℝ :=
  sSup (Set.range (fun i => (D.rho i).re))

/-- The supremum's existence/boundedness facts are not supplied by sSup's
totalized definition. The exact real coordinate remains unknown. -/
def ZeroSupremumProvider {ι : Type*} (D : FullZeroData ι) : Prop :=
  (1 / 2 : ℝ) ≤ zeroRealSup D ∧ zeroRealSup D ≤ 1 ∧
    (∀ i, (D.rho i).re ≤ zeroRealSup D) ∧
    (∀ a : ℝ, a < zeroRealSup D → ∃ i, a < (D.rho i).re)

def actualRieszTwo (x : ℝ) : ℝ :=
  (∑ n ∈ indices x,
    ArithmeticFunction.vonMangoldt n * rieszTwoWeight ((n : ℝ) / x)) - x / 3

def actualRieszTwoEnergy (Y : ℝ) : ℝ :=
  ∫ x in Set.Icc (1 : ℝ) (Real.exp Y), actualRieszTwo x ^ 2 / x ^ 2

def actualRieszTwoMellin (s : ℂ) : ℂ :=
  ∫ x in Set.Ioi (1 : ℝ),
    (actualRieszTwo x : ℂ) * (x : ℂ) ^ (-s - 1)

def ActualRieszMellinProvider : Prop :=
  ∀ s : ℂ, 1 < s.re →
    actualRieszTwoMellin s =
      -2 * logDeriv riemannZeta s / (s * (s + 1) * (s + 2)) -
        1 / (3 * (s - 1))

/-- The actual twisted prime-power sum includes the exact complex main term.
The frequency parameter is unrestricted and no zero location is assumed. -/
def actualTwistedRieszTwo (τ x : ℝ) : ℂ :=
  (∑ n ∈ indices x,
    (ArithmeticFunction.vonMangoldt n : ℂ) *
      (n : ℂ) ^ (-Complex.I * (τ : ℂ)) *
      (rieszTwoWeight ((n : ℝ) / x) : ℂ)) -
    2 * (x : ℂ) ^ (1 - Complex.I * (τ : ℂ)) /
      ((1 - Complex.I * (τ : ℂ)) *
        (2 - Complex.I * (τ : ℂ)) * (3 - Complex.I * (τ : ℂ)))

def ActualTwistedMellinProvider : Prop :=
  ∀ τ : ℝ, ∀ s : ℂ, 1 < s.re →
    (∫ x in Set.Ioi (1 : ℝ),
      actualTwistedRieszTwo τ x * (x : ℂ) ^ (-s - 1)) =
      -2 * logDeriv riemannZeta (s + Complex.I * (τ : ℂ)) /
        (s * (s + 1) * (s + 2)) -
      2 / ((1 - Complex.I * (τ : ℂ)) *
        (2 - Complex.I * (τ : ℂ)) * (3 - Complex.I * (τ : ℂ)) *
          (s - 1 + Complex.I * (τ : ℂ)))

/-- The constants may depend on the chosen frequency. No uniform-in-τ
remainder estimate is silently asserted. -/
def ActualTwistedExplicitFormulaProvider {ι : Type*}
    (D : FullZeroData ι) : Prop :=
  ∀ τ : ℝ, ∃ B : ℝ → ℂ,
    (∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → ‖B x‖ ≤ C) ∧
    ∀ x : ℝ, 1 ≤ x →
      Summable (fun i =>
        -2 * (D.multiplicity i : ℂ) *
          (x : ℂ) ^ (D.rho i - Complex.I * (τ : ℂ)) /
          ((D.rho i - Complex.I * (τ : ℂ)) *
            (D.rho i + 1 - Complex.I * (τ : ℂ)) *
            (D.rho i + 2 - Complex.I * (τ : ℂ)))) ∧
      actualTwistedRieszTwo τ x =
        (∑' i, -2 * (D.multiplicity i : ℂ) *
          (x : ℂ) ^ (D.rho i - Complex.I * (τ : ℂ)) /
          ((D.rho i - Complex.I * (τ : ℂ)) *
            (D.rho i + 1 - Complex.I * (τ : ℂ)) *
            (D.rho i + 2 - Complex.I * (τ : ℂ)))) + B x

def ActualRieszExplicitFormulaProvider {ι : Type*}
    (D : FullZeroData ι) : Prop :=
  ∃ B : ℝ → ℂ, (∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → ‖B x‖ ≤ C) ∧
    ∀ x : ℝ, 1 ≤ x →
      Summable (fun i =>
        -2 * (D.multiplicity i : ℂ) * (x : ℂ) ^ D.rho i /
          (D.rho i * (D.rho i + 1) * (D.rho i + 2))) ∧
      (actualRieszTwo x : ℂ) =
        (∑' i, -2 * (D.multiplicity i : ℂ) * (x : ℂ) ^ D.rho i /
          (D.rho i * (D.rho i + 1) * (D.rho i + 2))) + B x

def ActualAnnularExplicitFormulaProvider {ι : Type*}
    (D : FullZeroData ι) : Prop :=
  ∃ B : ℝ → ℂ, (∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → ‖B x‖ ≤ C) ∧
    ∀ x : ℝ, 1 ≤ x →
      Summable (fun i => annularCoefficient D i * (x : ℂ) ^ D.rho i) ∧
      (actualPrimeSignal x : ℂ) =
        (∑' i, annularCoefficient D i * (x : ℂ) ^ D.rho i) + B x

def AnnularSupportHeightProvider {ι : Type*} (D : FullZeroData ι) : Prop :=
  ∃ C : ℝ, ∀ X T x : ℝ,
    1 ≤ x → x ≤ X → 2 ≤ T →
    Summable (fun i =>
      if T < |(D.rho i).im| then
        annularCoefficient D i * (x : ℂ) ^ (D.rho i - (1 / 2 : ℂ))
      else 0) ∧
    ‖∑' i, if T < |(D.rho i).im| then
      annularCoefficient D i * (x : ℂ) ^ (D.rho i - (1 / 2 : ℂ))
      else 0‖ ≤ C * Real.sqrt X * Real.log T / T ^ 2

def logPlus (t : ℝ) : ℝ := Real.log (max 1 t)

def ResidualZeroGrowthProvider {ι : Type*} (D : FullZeroData ι) : Prop :=
  Filter.limsup
    (fun X : ℝ => logPlus (actualResidual X) / Real.log X)
    atTop = 2 * zeroRealSup D - 1

def annularSpectralConstant {ι : Type*} (D : FullZeroData ι) : ℝ :=
  ∑' i, ‖annularCoefficient D i‖ ^ 2

def ActualAnnularSpectralProvider {ι : Type*} (D : FullZeroData ι) : Prop :=
  RiemannHypothesis →
    Summable (fun i => ‖annularCoefficient D i‖ ^ 2) ∧
    Tendsto (fun X : ℝ => actualQuadraticEnergy X / Real.log X)
      atTop (𝓝 (annularSpectralConstant D))

/-- The spectral coefficient is transported exactly if the two actual
limits are supplied. This is a conditional reduction with named providers. -/
theorem actualResidual_slope_of_two_limits {ι : Type*} (D : FullZeroData ι)
    (henergy :
      Tendsto (fun X : ℝ => actualQuadraticEnergy X / Real.log X)
        atTop (𝓝 (annularSpectralConstant D)))
    (hmodel :
      Tendsto (fun X : ℝ => actualModel X / Real.log X)
        atTop (𝓝 ModelCoefficient)) :
    Tendsto (fun X : ℝ => actualResidual X / Real.log X)
      atTop (𝓝 (annularSpectralConstant D - ModelCoefficient)) :=
  RiemannResearch.Analysis.CenteredResidualTransfer.tendsto_residual_ratio_of_model_and_energy
    actualQuadraticEnergy_eq_model_add_residual henergy hmodel

def ActualZeroFreeEnvelopeProvider : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 2 * Real.sqrt (2 / (4.896 : ℝ)) →
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |actualRieszTwo x| ≤ C * x * Real.exp (-κ * Real.sqrt (Real.log x))

end RiemannResearch.RH.AnnularZeroSpectral
