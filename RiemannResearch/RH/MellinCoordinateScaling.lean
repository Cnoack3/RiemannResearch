import RiemannResearch.RH.MellinCoordinateDefect
import RiemannResearch.RH.MellinFrequencyScalingTargets

/-!
# Coordinate-cutoff scaling and a defect invisible at leading order

Source: ArithmeticProjectionDPPDraft20260921.md (2026-09-21), Sections
5--7. We prove that the explicit omitted-first-coordinate correction tends
to zero after logarithmic normalization, while its compensated correction
has a nonzero limit. The sine and full ambient second-order asymptotics
are separately named formalization targets, not conclusions of this file.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.CoordinateMellin

def logLength (M : ℕ) : ℝ := Real.log ((M : ℝ) + 1)

def unfoldedFrequency (t₀ x : ℝ) (M : ℕ) : ℝ :=
  t₀ + 2 * Real.pi * x / logLength M

def ambientKernel (M : ℕ) (t u : ℝ) : ℂ :=
  ∑ n ∈ Finset.range M, coordinateFeature n t * star (coordinateFeature n u)

def scaledAmbientKernel (t₀ : ℝ) (M : ℕ) (x y : ℝ) : ℂ :=
  ambientKernel M (unfoldedFrequency t₀ x M) (unfoldedFrequency t₀ y M) /
    (logLength M : ℂ)

def firstCoordinateCorrection (t₀ : ℝ) (M : ℕ) (x y : ℝ) : ℂ :=
  coordinateFeature 0 (unfoldedFrequency t₀ x M) *
    star (coordinateFeature 0 (unfoldedFrequency t₀ y M)) / (logLength M : ℂ)

def scaledMissingFirstKernel (t₀ : ℝ) (M : ℕ) (x y : ℝ) : ℂ :=
  scaledAmbientKernel t₀ M x y - firstCoordinateCorrection t₀ M x y

theorem logLength_tendsto : Tendsto logLength atTop atTop := by
  have hn : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    have hb := (tendsto_natCast_atTop_atTop : Tendsto (fun M : ℕ => (M : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop b)
    exact hb.mono fun M hM => by linarith
  exact Real.tendsto_log_atTop.comp hn

theorem unfoldedFrequency_tendsto (t₀ x : ℝ) :
    Tendsto (unfoldedFrequency t₀ x) atTop (𝓝 t₀) := by
  change Tendsto (fun M : ℕ => t₀ + 2 * Real.pi * x / logLength M) atTop (𝓝 t₀)
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => t₀) atTop (𝓝 t₀)).add
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => 2 * Real.pi * x) atTop (𝓝 _)).div_atTop logLength_tendsto)
  simpa only [add_zero] using h

theorem firstCoordinateCorrection_tendsto_zero (t₀ x y : ℝ) :
    Tendsto (fun M => firstCoordinateCorrection t₀ M x y) atTop (𝓝 0) := by
  have hx := (coordinateFeature_continuous 0).continuousAt.tendsto.comp (unfoldedFrequency_tendsto t₀ x)
  have hy := (coordinateFeature_continuous 0).continuousAt.tendsto.comp (unfoldedFrequency_tendsto t₀ y)
  have hr := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).div_atTop logLength_tendsto
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  have h := (hx.mul hy.star).mul hc
  simpa [firstCoordinateCorrection, Complex.ofReal_div, div_eq_mul_inv] using h

/-- Compensating the lost factor recovers a nonzero rank-one profile. -/
theorem compensated_firstCoordinateCorrection_tendsto (t₀ x y : ℝ) :
    Tendsto (fun M => (logLength M : ℂ) * firstCoordinateCorrection t₀ M x y)
      atTop (𝓝 (coordinateFeature 0 t₀ * star (coordinateFeature 0 t₀))) := by
  have hx := (coordinateFeature_continuous 0).continuousAt.tendsto.comp (unfoldedFrequency_tendsto t₀ x)
  have hy := (coordinateFeature_continuous 0).continuousAt.tendsto.comp (unfoldedFrequency_tendsto t₀ y)
  apply (hx.mul hy.star).congr'
  have hl : ∀ᶠ M in atTop, 0 < logLength M := logLength_tendsto.eventually (eventually_gt_atTop 0)
  filter_upwards [hl] with M hM
  unfold firstCoordinateCorrection
  simp only [Function.comp_apply]
  field_simp [Complex.ofReal_ne_zero.mpr hM.ne']

theorem compensated_firstCoordinateCorrection_limit_ne_zero (t₀ : ℝ) :
    coordinateFeature 0 t₀ * star (coordinateFeature 0 t₀) ≠ 0 :=
  mul_ne_zero (coordinateFeature_ne_zero 0 t₀) (star_ne_zero.mpr (coordinateFeature_ne_zero 0 t₀))

/-- An explicit identity and proper projection share any existing leading
kernel limit. This does not assume that the limit is the sine kernel. -/
theorem same_limit_iff_missing_first (t₀ x y : ℝ) (k : ℂ) :
    Tendsto (fun M => scaledAmbientKernel t₀ M x y) atTop (𝓝 k) ↔
      Tendsto (fun M => scaledMissingFirstKernel t₀ M x y) atTop (𝓝 k) := by
  constructor
  · intro h
    simpa [scaledMissingFirstKernel] using h.sub (firstCoordinateCorrection_tendsto_zero t₀ x y)
  · intro h
    have ht := h.add (firstCoordinateCorrection_tendsto_zero t₀ x y)
    simpa [scaledMissingFirstKernel] using ht

def phasedSineKernel (x y : ℝ) : ℂ :=
  Complex.exp (-(Real.pi * (x - y) : ℝ) * Complex.I) *
    MellinFrequency.sineKernel x y

/-- FORMALIZATION TARGET: local uniform convergence for physical cutoffs.
This is distinct from the existing arithmetic-rank scaling target. -/
def CoordinateSineLimitTarget : Prop :=
  ∀ t₀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ M in atTop, ∀ x ∈ Set.Icc (-R) R, ∀ y ∈ Set.Icc (-R) R,
      ‖scaledAmbientKernel t₀ M x y - phasedSineKernel x y‖ < ε

def geometricCellRemainder (n : ℕ) (t u : ℝ) : ℂ :=
  (∫ x in Set.Ioc ((n : ℝ) + 1) ((n : ℝ) + 2),
    (x : ℂ) ^ (-1 - (t - u : ℝ) * Complex.I)) -
      coordinateFeature n t * star (coordinateFeature n u)

def geometricRemainder (t u : ℝ) : ℂ := ∑' n, geometricCellRemainder n t u

/-- FORMALIZATION TARGET: the un-gauged second-order ambient coefficient. -/
def CoordinateSecondOrderTarget : Prop :=
  ∀ t₀ x y : ℝ, Tendsto (fun M => (logLength M : ℂ) *
    (scaledAmbientKernel t₀ M x y - phasedSineKernel x y)) atTop
      (𝓝 (-geometricRemainder t₀ t₀))

end RiemannResearch.RH.Pareto.CoordinateMellin
