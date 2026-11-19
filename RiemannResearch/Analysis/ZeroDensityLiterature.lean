/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualSelbergDensityConventions
import RiemannResearch.Analysis.ActualSelbergDensityInterpolation
import RiemannResearch.Analysis.ActualOneSidedHorizontalDisplacement
import RiemannResearch.Analysis.ActualConreyBaluyotConsequences
import RiemannResearch.Analysis.ActualPrimeTorusFMZRate
import RiemannResearch.Analysis.MontgomeryTransitionFrequency
import RiemannResearch.Analysis.MontgomeryBoundedTransitionPeak
import RiemannResearch.Analysis.MontgomeryQuantitativeTransitionGap
import RiemannResearch.Analysis.MontgomeryCenteredTransition
import RiemannResearch.Analysis.MontgomeryTransitionHorizontalDefect

/-!
# Opt-in literature inputs for the zero-density and Montgomery programs

Each input is an independent proposition that a caller may supply locally.
Baluyot, *On the Zeros of Riemann's Zeta-function* (2017), Theorem 1.2.1
and §3.6, proves the strict right-count estimate stated below.
<https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320>

Baluyot, Goldston, Suriajaya and Turnage-Butterbaugh, arXiv:2501.14545v3,
§3 (3.5), gives the positive-ordinate complex pair estimate for 1 ≤ x ≤ T.
<https://arxiv.org/html/2501.14545v3#S3.E5>

The class arguments record exactly which external analysis a caller invokes.
All constants and height thresholds are chosen after the fixed exponent.
-/

noncomputable section
open Set Filter Zeta23
open scoped Topology
namespace RiemannResearch.Analysis.ZeroDensityLiterature
open ActualZeroOrdinate MontgomeryHorizontalBessel
open ActualPrimeTorusFMZ PrimePhaseTorus PrimeTorusHaar

/-- Baluyot's strict source count with theta in its original normalization. -/
class ConreyBaluyot2017 : Prop where
  rightCount : ∀ θ : ℝ, 0 < θ → θ < 4 / 7 →
    ∃ C H : ℝ, 0 ≤ C ∧ 1 < H ∧ ∀ T : ℝ, H ≤ T →
      ∀ σ ∈ Ioc (1 / 2 : ℝ) 1,
        rightStrictTail T (σ - 1 / 2) ≤ C * T ^ (1 + θ * (1 - 2 * σ)) * Real.log T

/-- Corrected complex pair-sum estimate in BGSTB version 3. -/
class BGSTB2026 : Prop where
  positiveCutoff : BGSTBPositiveCutoffEstimate

/-- Conversion to the actual inclusive multiplicity count includes the
critical-line boundary and doubles the source's mollifier exponent. -/
theorem conreyBaluyot [ConreyBaluyot2017] : ConreyBaluyotDensityHypothesis :=
  conreyBaluyotDensity_iff_strict_source.mpr ConreyBaluyot2017.rightCount

/-- Every fixed exponent in the full one-logarithm interval is available.
The height threshold and multiplicative constant may depend on a. -/
theorem oneLogSlope [ConreyBaluyot2017] {a : ℝ} (ha : 0 < a) (ha' : a < 8/7) :
    UniformSelbergDensity a := conreyBaluyot a ha ha'

/-- With the published density input, the one-sided o(T) height mass is
equivalent to the quadratic horizontal condition used in the PCC program. -/
theorem quadraticPCCCondition [ConreyBaluyot2017] :
    Tendsto oneSidedHeightMean atTop (𝓝 0) ↔
      Tendsto (fun T : ℝ => displacementMoment T 2 * Real.log T ^ 2) atTop (𝓝 0) :=
  oneSidedHeightMean_tendsto_zero_iff_quadratic (a := 1) (by norm_num)
    (oneLogSlope (by norm_num) (by norm_num))

/-- Use the limiting slope with any prescribed positive logarithmic loss. -/
theorem limitingSlope [ConreyBaluyot2017] {ε : ℝ} (hε : 0 < ε) :
    UniformLogLossDensity (8 / 7) (1 + ε) := conreyBaluyot.endpoint_log_loss hε

/-- The literature-normalized one-point FMZ budget applies even when the
prime set, harmonics, and coefficients all move with height. -/
theorem movingPrimeTorus [ConreyBaluyot2017] {ι : Type*}
    (P : ℝ → Finset ℕ) (a : ℝ → ι → ℂ) (k : ℝ → ι → ℕ → ℤ)
    (hP : ∀ T p, p ∈ P T → p.Prime)
    (ha : ∀ T, Summable (fun i => ‖a T i‖ * primeModeWeight (P T) (k T i) ^ 2))
    (hsmall : Tendsto (fun T : ℝ =>
      Fourier.weightedFourierMass (a T)
        (fun i => primeModeWeight (P T) (k T i) ^ 2) / Real.log T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ =>
      (sampleFunctional (P T) T
          (fourierSeries (a T) (fun i => fun p : P T => k T i p)) -
        (Ncount 0 T : ℂ) * haarIntegral
          (fourierSeries (a T) (fun i => fun p : P T => k T i p))) / (T : ℂ) -
      haarIntegral (fourierSeries (a T) (fun i => fun p : P T => k T i p) *
        primeDensity (P T))) atTop (𝓝 0) :=
  tendsto_moving_fourierSeries_remainder P a k hP ha hsmall conreyBaluyot.classical

/-- At the shrinking transition, the source estimates give a rate uniform
in each bounded interval of c for the raw ordinate form factor. -/
theorem rawTransition [BGSTB2026] (A : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
      |MontgomeryFormFactor.formFactor T (transitionFrequency c T) - Real.exp (-c)| ≤
        K / Real.sqrt (Real.log T) := by
  obtain ⟨K,hK,h⟩ := raw_transition_uniform_rate_of_bgstb_scaled_defect
    eventually_transition_horizontalDefect_scaled_le BGSTB2026.positiveCutoff A
  refine ⟨K+1,by linarith,?_⟩
  filter_upwards [h] with T hT
  intro c hc
  exact (hT c hc).trans (div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))

/-- The raw and complex statistics agree at signed order 1/log T under the
same positive-cutoff source. -/
theorem rawComplexGap [BGSTB2026] : RawSharpTransitionScaledGap :=
  rawSharpTransitionScaledGap_of_corrected_scaled_defect
    eventually_transition_horizontalDefect_scaled_le
    (correctedComplexFormFactorEstimate_of_bgstb BGSTB2026.positiveCutoff)

/-- With the centered positive-cutoff and prime-diagonal refinements,
the signed archimedean coefficient transfers to the actual ordinates. -/
theorem rawArchimedean [BGSTB2026] (hcut : CenteredPositiveCutoffRemainder)
    (hprime : NarrowPrimeMeanSquareRemainder) :
    TransitionArchimedeanCorrection MontgomeryFormFactor.formFactor :=
  raw_transition_archimedean_of_scaled_gap rawComplexGap
    (sharpTransitionArchimedean_of_centered_component_bounds hcut hprime)

end RiemannResearch.Analysis.ZeroDensityLiterature
