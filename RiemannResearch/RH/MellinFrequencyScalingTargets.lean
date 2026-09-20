import RiemannResearch.Analysis.ComplexKernelScaling
import RiemannResearch.RH.MellinFrequencyKernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Open sine-scaling targets for the arithmetic Mellin kernel

Source: user-provided Montgomery pair-correlation comparison, 2026-09-20.
The sine profile is the Fourier band-projection kernel. The statements named
`...Target` below are explicit research propositions, not proved assertions.
The conditional theorem proves the normalized two-point limit from the
specified kernel limit. Nothing identifies frequency-DPP samples with actual
zeta-zero ordinates or proves their pair-correlation conjecture.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.MellinFrequency
open RiemannResearch.Analysis.ComplexKernel

/-- The unit-intensity sine kernel, including its removable diagonal value. -/
def sineKernel (x y : ℝ) : ℂ := (Real.sinc (Real.pi * (x - y)) : ℝ)

@[simp] theorem sineKernel_diagonal (x : ℝ) : sineKernel x x = 1 := by
  simp [sineKernel]

/-- Rank, center, local inverse-spacing scale, and a real gauge phase. -/
structure FrequencyScaling where
  rank : ℕ → ℕ
  center : ℕ → ℝ
  scale : ℕ → ℝ
  phase : ℕ → ℝ → ℝ

/-- Gauge-transformed, unfolded kernel relative to dx. The original kernel
is relative to dt/(2π), so the exact Jacobian factor is 1/(2π r). -/
def scaledKernel (p : FrequencyScaling) (m : ℕ) (x y : ℝ) : ℂ :=
  ((1 / (2 * Real.pi * p.scale m) : ℝ) : ℂ) *
    Complex.exp ((p.phase m x : ℂ) * Complex.I) *
    star (Complex.exp ((p.phase m y : ℂ) * Complex.I)) *
    kernel (p.rank m) (p.center m + x / p.scale m)
      (p.center m + y / p.scale m)

/-- Open: nondegenerate growing arithmetic ranks with the full sine-kernel
limit, including its diagonal intensity normalization. -/
def SineKernelLimitTarget (p : FrequencyScaling) : Prop :=
  (∀ m, 0 < p.scale m) ∧ Tendsto p.rank atTop atTop ∧
    ∀ x y, Tendsto (fun m => scaledKernel p m x y) atTop (𝓝 (sineKernel x y))

/-- Open additional arithmetic matching condition for the zero-spacing
scale. It is not part of the abstract sine-limit implication. -/
def MontgomeryScaleTarget (p : FrequencyScaling) : Prop :=
  Tendsto p.center atTop atTop ∧
    Tendsto (fun m => (2 * Real.pi * p.scale m) / Real.log (p.center m))
      atTop (𝓝 1)

/-- Open existence target, not an assumption discharged by the DPP structure. -/
def ArithmeticSineScalingTarget : Prop :=
  ∃ p : FrequencyScaling, SineKernelLimitTarget p ∧ MontgomeryScaleTarget p

/-- Kernel convergence gives the exact sine pair profile. This is a theorem
about the actual rescaled Mellin kernel, not about zeta-zero ordinates. -/
theorem normalized_pair_tendsto_of_sine_limit (p : FrequencyScaling)
    (hp : SineKernelLimitTarget p) (x y : ℝ) :
    Tendsto (fun m => pairDensity (scaledKernel p m) x y /
      ((scaledKernel p m x x).re * (scaledKernel p m y y).re)) atTop
      (𝓝 (1 - Real.sinc (Real.pi * (x - y)) ^ 2)) := by
  have h := normalized_pairDensity_tendsto (scaledKernel p) sineKernel atTop
    hp.2.2 x y (by simp) (by simp)
  simpa [sineKernel, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

end RiemannResearch.RH.Pareto.MellinFrequency
