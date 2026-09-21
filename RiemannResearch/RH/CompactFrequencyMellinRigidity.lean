import RiemannResearch.RH.MellinFrequencyKernel
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Compact-frequency Mellin mixtures: definitions and analytic reductions

Source: user-provided `RH_Obstruction_Compact_Frequency_Rigidity_2026-09-21.md`,
Sections 3--4. This module formalizes the actual sequences and integrals and
separates the arithmetic reduction from its analytic inputs.

The Mellin/Fubini identity, entire-defect estimate, and Fourier uniqueness
for weighted complex measures are proved in `CompactMixtureResidueIdentity`,
`CompactFrequencyMellinEntire`, and `WeightedDensityFourierUniqueness`.
The logarithmic-sampling input is proved in `LogIntegerSamplingUniqueness`.
`compactFrequencyRigidity_proved` in `CompactFrequencyRigidity` assembles these
results with no additional analytic provider hypothesis. These modules import
the definitions here; the dependency direction is intentional.

A finite complex measure is represented here by an integrable complex density
against a finite positive measure, as in its polar decomposition. The proofs
below do not assume positivity of that complex density.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.SpectralObstruction

/-- Array index `n` represents the physical integer `n + 1`. -/
def mellinMode (s : ℂ) (n : ℕ) : ℂ :=
  (((n : ℂ) + 1) * ((n : ℂ) + 2)) *
    (((n : ℂ) + 1) ^ (-s) - ((n : ℂ) + 2) ^ (-s))

def verticalPoint (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I

@[simp] theorem verticalPoint_re (σ t : ℝ) : (verticalPoint σ t).re = σ := by
  simp [verticalPoint]

@[simp] theorem verticalPoint_half (t : ℝ) :
    verticalPoint (1 / 2) t = MellinFrequency.criticalPoint t := by
  simp [verticalPoint, MellinFrequency.criticalPoint]

def normalizedResidueCoordinate (d n : ℕ) : ℂ :=
  (((n + 1) % d : ℕ) : ℂ) / (d : ℂ)

/-- Complex-linear pairing; this is not a conjugate-linear inner product. -/
def residuePairing (v : ℕ → ℂ) (d : ℕ) : ℂ :=
  ∑' n, (paretoWeight n : ℂ) * v n * normalizedResidueCoordinate d n

def continuumMixture (σ : ℝ) (μ : Measure ℝ) (a : ℝ → ℂ) (n : ℕ) : ℂ :=
  ∫ t, a t * mellinMode (verticalPoint σ t) n ∂μ

def zetaWeightedDensity (σ : ℝ) (a : ℝ → ℂ) (t : ℝ) : ℂ :=
  riemannZeta (verticalPoint σ t) * a t

def densityFourier (μ : Measure ℝ) (b : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t, b t * Complex.exp (-(t : ℂ) * Complex.I * z) ∂μ

def densityMass (μ : Measure ℝ) (b : ℝ → ℂ) : ℂ := ∫ t, b t ∂μ

def samplingDefect (σ : ℝ) (μ : Measure ℝ) (a : ℝ → ℂ) (z : ℂ) : ℂ :=
  densityFourier μ (zetaWeightedDensity σ a) z -
    densityMass μ (zetaWeightedDensity σ a) * Complex.exp (((σ : ℂ) - 1) * z)

/-- The precise compact-frequency assumptions on a measure representation. -/
def CompactFrequencyData (σ T : ℝ) (μ : Measure ℝ) (a : ℝ → ℂ) : Prop :=
  (1 / 2 : ℝ) ≤ σ ∧ σ < 1 ∧ 0 ≤ T ∧ IsFiniteMeasure μ ∧
    Integrable a μ ∧ ∀ᵐ t ∂μ, |t| ≤ T

/-- The complete continuum rigidity statement. It is proved by
`compactFrequencyRigidity_proved` in `CompactFrequencyRigidity`; the
definitions and general reductions here are shared by its analytic proofs. -/
def CompactFrequencyRigidityTarget : Prop :=
  ∀ (σ T : ℝ) (μ : Measure ℝ) (a : ℝ → ℂ),
    CompactFrequencyData σ T μ a →
    ((∀ d : ℕ, 2 ≤ d → residuePairing (continuumMixture σ μ a) d = 0) ↔
      zetaWeightedDensity σ a =ᵐ[μ] 0)

/-- Section 4's full bounded-frequency critical-line conclusion. The theorem
`compactCriticalMixtureTriviality_proved` in `CompactCriticalMixtureTriviality`
proves this statement from the finite zero-support decomposition and the
fully proved critical-line mixture energy law. -/
def CompactCriticalMixtureTrivialityTarget : Prop :=
  ∀ (T : ℝ) (μ : Measure ℝ) (a : ℝ → ℂ),
    CompactFrequencyData (1 / 2) T μ a →
    Summable (fun n => paretoWeight n * ‖continuumMixture (1 / 2) μ a n‖ ^ 2) →
    (∀ d : ℕ, 2 ≤ d → residuePairing (continuumMixture (1 / 2) μ a) d = 0) →
    a =ᵐ[μ] 0 ∧ continuumMixture (1 / 2) μ a = 0

/-- The standard global bound for an entire function of exponential type. -/
def EntireExponentialType (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧
    ∀ z, ‖f z‖ ≤ A * Real.exp (K * ‖z‖)

/-- Jensen's zero-count input versus the zeros `log d`. A proof is supplied
by `logIntegerSamplingUniqueness_proved` in the sibling module. -/
def LogIntegerSamplingUniqueness : Prop :=
  ∀ f : ℂ → ℂ, EntireExponentialType f →
    (∀ d : ℕ, 2 ≤ d → f (Real.log (d : ℝ)) = 0) → ∀ z, f z = 0

/-- Arithmetic/analytic identity on the actual coordinate mixture, including
absolute convergence and the Mellin/Fubini interchange. Under compact-frequency
data it is proved by `mixtureResidueIdentity_of_compact_data`. -/
def MixtureResidueIdentity (σ : ℝ) (μ : Measure ℝ) (a : ℝ → ℂ) : Prop :=
  ∀ d : ℕ, 2 ≤ d →
    Summable (fun n => (paretoWeight n : ℂ) * continuumMixture σ μ a n *
      normalizedResidueCoordinate d n) ∧
    residuePairing (continuumMixture σ μ a) d =
      -Complex.exp (-(σ : ℂ) * (Real.log (d : ℝ) : ℂ)) *
        samplingDefect σ μ a (Real.log (d : ℝ))

/-- Fourier uniqueness for the actual zeta-weighted density. The theorem
`weightedFourierUniqueness_of_integrable` supplies this input. -/
def WeightedFourierUniqueness (σ : ℝ) (μ : Measure ℝ) (a : ℝ → ℂ) : Prop :=
  (∀ x : ℝ, densityFourier μ (zetaWeightedDensity σ a) x = 0) →
    zetaWeightedDensity σ a =ᵐ[μ] 0

/-- Fourier transforms of integrable densities are uniformly bounded on ℝ. -/
theorem densityFourier_norm_le (μ : Measure ℝ) (b : ℝ → ℂ) (x : ℝ) :
    ‖densityFourier μ b x‖ ≤ ∫ t, ‖b t‖ ∂μ := by
  unfold densityFourier
  calc
    _ ≤ ∫ t, ‖b t * Complex.exp (-(t : ℂ) * Complex.I * (x : ℂ))‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = ∫ t, ‖b t‖ ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp [Complex.norm_exp]

/-- A bounded real-axis function cannot equal a nonzero decreasing
exponential on the whole real axis. The negative half-axis is essential. -/
theorem bounded_exponential_coefficient_eq_zero
    (F : ℝ → ℂ) (B : ℂ) (c C : ℝ) (hc : c < 0)
    (hbound : ∀ x, ‖F x‖ ≤ C)
    (heq : ∀ x, F x = B * (Real.exp (c * x) : ℂ)) : B = 0 := by
  by_contra hB
  have hnorm : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have hC : 0 ≤ C := le_trans (norm_nonneg (F 0)) (hbound 0)
  let y : ℝ := (C + 1) / ‖B‖
  have hy : 0 < y := div_pos (by linarith) hnorm
  have hc0 : c ≠ 0 := ne_of_lt hc
  have hexp : Real.exp (c * (Real.log y / c)) = y := by
    have he : c * (Real.log y / c) = Real.log y := by field_simp [hc0]
    rw [he, Real.exp_log hy]
  have h := hbound (Real.log y / c)
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), hexp] at h
  have hm : ‖B‖ * y = C + 1 := by
    dsimp [y]
    field_simp [ne_of_gt hnorm]
  rw [hm] at h
  linarith

theorem samplingDefect_zero_implies_mass_zero (σ : ℝ) (hσ : σ < 1)
    (μ : Measure ℝ) (a : ℝ → ℂ)
    (hzero : ∀ z, samplingDefect σ μ a z = 0) :
    densityMass μ (zetaWeightedDensity σ a) = 0 := by
  apply bounded_exponential_coefficient_eq_zero
    (fun x => densityFourier μ (zetaWeightedDensity σ a) x)
    _ (σ - 1) (∫ t, ‖zetaWeightedDensity σ a t‖ ∂μ) (by linarith)
    (densityFourier_norm_le μ (zetaWeightedDensity σ a))
  intro x
  have h := sub_eq_zero.mp (hzero (x : ℂ))
  convert h using 1
  simp [Complex.ofReal_exp, Complex.ofReal_mul,
    Complex.ofReal_sub]

/-- General reduction of all arithmetic equations to zero weighted measure.
The explicit analytic arguments are discharged for compact-frequency data by
the theorems assembled in `CompactFrequencyRigidity`. -/
theorem weightedDensity_zero_of_annihilates
    (σ : ℝ) (hσ : σ < 1) (μ : Measure ℝ) (a : ℝ → ℂ)
    (hidentity : MixtureResidueIdentity σ μ a)
    (hentire : EntireExponentialType (samplingDefect σ μ a))
    (hsampling : LogIntegerSamplingUniqueness)
    (hfourier : WeightedFourierUniqueness σ μ a)
    (hann : ∀ d : ℕ, 2 ≤ d → residuePairing (continuumMixture σ μ a) d = 0) :
    zetaWeightedDensity σ a =ᵐ[μ] 0 := by
  have hsamples : ∀ d : ℕ, 2 ≤ d →
      samplingDefect σ μ a (Real.log (d : ℝ)) = 0 := by
    intro d hd
    have h := (hidentity d hd).2
    rw [hann d hd] at h
    have hm := (mul_eq_zero.mp h.symm)
    exact hm.resolve_left (neg_ne_zero.mpr (Complex.exp_ne_zero _))
  have hg := hsampling _ hentire hsamples
  have hmass := samplingDefect_zero_implies_mass_zero σ hσ μ a hg
  apply hfourier
  intro x
  have h := hg (x : ℂ)
  simpa [samplingDefect, hmass] using h

/-- Reverse direction needs only the actual residue identity. -/
theorem annihilates_of_weightedDensity_zero
    (σ : ℝ) (μ : Measure ℝ) (a : ℝ → ℂ)
    (hidentity : MixtureResidueIdentity σ μ a)
    (hzero : zetaWeightedDensity σ a =ᵐ[μ] 0) :
    ∀ d : ℕ, 2 ≤ d → residuePairing (continuumMixture σ μ a) d = 0 := by
  have hmass : densityMass μ (zetaWeightedDensity σ a) = 0 := by
    simpa [densityMass] using integral_congr_ae hzero
  have hF : ∀ z, densityFourier μ (zetaWeightedDensity σ a) z = 0 := by
    intro z
    unfold densityFourier
    calc
      _ = ∫ _t : ℝ, (0 : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hzero] with t ht
        simp [ht]
      _ = 0 := by simp
  intro d hd
  rw [(hidentity d hd).2]
  simp [samplingDefect, hmass, hF]

/-- Exact a.e. meaning of support on the actual zeta zero set. -/
theorem weightedDensity_zero_iff_supported_on_zeros
    (σ : ℝ) (μ : Measure ℝ) (a : ℝ → ℂ) :
    zetaWeightedDensity σ a =ᵐ[μ] 0 ↔
      ∀ᵐ t ∂μ, a t ≠ 0 → riemannZeta (verticalPoint σ t) = 0 := by
  constructor
  · intro h
    filter_upwards [h] with t ht hat
    exact (mul_eq_zero.mp ht).resolve_right hat
  · intro h
    filter_upwards [h] with t ht
    by_cases ha : a t = 0
    · simp [zetaWeightedDensity, ha]
    · simp [zetaWeightedDensity, ht ha]

/-- On a zero-free line, rigidity forces the original density to vanish. -/
theorem density_zero_of_weightedDensity_zero_of_zeroFree
    (σ : ℝ) (μ : Measure ℝ) (a : ℝ → ℂ)
    (hzero : zetaWeightedDensity σ a =ᵐ[μ] 0)
    (hfree : ∀ᵐ t ∂μ, riemannZeta (verticalPoint σ t) ≠ 0) : a =ᵐ[μ] 0 := by
  filter_upwards [hzero, hfree] with t ht hf
  exact (mul_eq_zero.mp ht).resolve_left hf

/-- Vanishing complex measure gives the zero coordinate mixture. -/
theorem continuumMixture_eq_zero_of_density_zero
    (σ : ℝ) (μ : Measure ℝ) (a : ℝ → ℂ) (hzero : a =ᵐ[μ] 0) :
    continuumMixture σ μ a = 0 := by
  funext n
  unfold continuumMixture
  calc
    _ = ∫ _t : ℝ, (0 : ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hzero] with t ht
      simp [ht]
    _ = 0 := by simp

/-- The exact measure-analytic inputs, proved jointly by
`compactMixtureAnalyticProvider_proved` in `CompactFrequencyRigidity`. -/
def CompactMixtureAnalyticProvider : Prop :=
  ∀ (σ T : ℝ) (μ : Measure ℝ) (a : ℝ → ℂ),
    CompactFrequencyData σ T μ a →
    MixtureResidueIdentity σ μ a ∧
    EntireExponentialType (samplingDefect σ μ a) ∧
    WeightedFourierUniqueness σ μ a

/-- General assembly from analytic inputs. The sampling input is proved in
the sibling Jensen module; `CompactFrequencyRigidity` supplies the analytic
input and applies this assembly to the actual compact-frequency mixtures. -/
theorem compactFrequencyRigidity_of_providers
    (hanalytic : CompactMixtureAnalyticProvider)
    (hsampling : LogIntegerSamplingUniqueness) : CompactFrequencyRigidityTarget := by
  intro σ T μ a hdata
  obtain ⟨hidentity, hentire, hfourier⟩ := hanalytic σ T μ a hdata
  exact ⟨weightedDensity_zero_of_annihilates σ hdata.2.1 μ a
    hidentity hentire hsampling hfourier,
    annihilates_of_weightedDensity_zero σ μ a hidentity⟩

end RiemannResearch.RH.Pareto.SpectralObstruction
