import RiemannResearch.Analysis.WeightedMellinHardy
import RiemannResearch.RH.AnnularZeroSpectralTargets
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Quantitative Mellin evaluation in the weighted arithmetic topology

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

The exact point bound is already proved in the project as
`MeasureTheory.WeightedMellin.transform_norm_sq_le`; this module reuses it
at s = 2a and transports it to differences and actual finite truncations.
`energy_to_hardy`, `vertical_plancherel`, `angular_plancherel`, and
`hardy_energy_isLUB` already supply the Hardy statements and norm identity.

Here H_a is membership in a raw weighted L2 seminorm, not a newly constructed
Hilbert completion. Functions equal almost everywhere have zero distance.
The usual H_a space is obtained by the almost-everywhere quotient.

For an infinite arithmetic vector, H_a membership with a < Re(rho)
provides an analytic Mellin transform at rho. If its independently proved
Mellin formula has a nonzero full-zero pole there, such membership is
impossible. Therefore no unconditional infinite-vector membership at all
full zeros is asserted. The actual finite truncations below have no such
infinite-tail obstruction. ActualAnnularTruncationMembership and
ActualAnnularTruncationEnvelope supply membership and an explicit growing
finite norm envelope. Useful infinite-vector control remains open.

Sources for reused declarations:
https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/WeightedMellinEnergy.lean
https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/Analysis/WeightedMellinHardy.lean
The higher derivative coefficient follows from the L2 logarithmic kernel
moment (2k)!/[2(Re(z)-a)]^(2k+1). WeightedMellinLogarithmicKernel and
WeightedMellinDerivativeTopology supply its analytic proof and both named
derivative providers. WeightedMellinDerivativeSharpness supplies an extremizer
and proves the coefficient optimal. These do not supply an arithmetic bound.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped Topology

namespace RiemannResearch.Analysis.WeightedMellinTopology
open MeasureTheory.WeightedMellin

/-- Raw-function membership for H_a = L2((1,infinity), x^(-2a-1) dx). -/
abbrev Ha (a : ℝ) (f : ℝ → ℂ) : Prop := FiniteEnergy f (2 * a)

def normSquared (a : ℝ) (f : ℝ → ℂ) : ℝ := energy f (2 * a)

/-- Closure under differences, proved through the existing actual L2 density. -/
theorem finiteEnergy_sub {f g : ℝ → ℂ} {s : ℝ}
    (hf : FiniteEnergy f s) (hg : FiniteEnergy g s) :
    FiniteEnergy (fun x => f x - g x) s := by
  have hm : Measurable (fun x => f x - g x) := hf.1.sub hg.1
  have hd : density (fun x => f x - g x) s =
      (fun x => density f s x - density g s x) := by
    funext x
    simp only [density, sub_mul]
  have hl : MemLp (density (fun x => f x - g x) s) 2
      (volume.restrict (Ioi (1 : ℝ))) := by
    rw [hd]
    exact (density_memLp hf).sub (density_memLp hg)
  have hmd : Measurable (density (fun x => f x - g x) s) :=
    -- The existing density_memLp proof uses this same complex cpow map.
    hm.mul (Complex.continuous_ofReal.measurable.pow_const
      (((-(s + 1) / 2 : ℝ) : ℂ)))
  have hi := (memLp_two_iff_integrable_sq_norm hmd.aestronglyMeasurable).1 hl
  refine ⟨hm, hi.congr ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact density_norm_sq (fun x => f x - g x) s (lt_trans zero_lt_one hx)

theorem transform_sub {f g : ℝ → ℂ} {s : ℝ}
    (hf : FiniteEnergy f s) (hg : FiniteEnergy g s)
    {z : ℂ} (hz : s / 2 < z.re) :
    transform (fun x => f x - g x) z = transform f z - transform g z := by
  have hfz := transform_integrable hf hz
  have hgz := transform_integrable hg hz
  unfold transform
  rw [← integral_sub hfz hgz]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  exact sub_mul (f x) (g x) ((x : ℂ) ^ (-z - 1))

/-- The existing exact bound at the H_a normalization. -/
theorem evaluation_norm_sq_le {f : ℝ → ℂ} {a : ℝ}
    (hf : Ha a f) {z : ℂ} (hz : a < z.re) :
    ‖transform f z‖ ^ 2 ≤ normSquared a f / (2 * (z.re - a)) := by
  have h := transform_norm_sq_le hf (by linarith : (2 * a) / 2 < z.re)
  simpa only [normSquared, show 2 * z.re - 2 * a = 2 * (z.re - a) by ring] using h

/-- Quantitative continuity in the actual weighted difference seminorm. -/
theorem evaluation_difference_norm_sq_le {f g : ℝ → ℂ} {a : ℝ}
    (hf : Ha a f) (hg : Ha a g) {z : ℂ} (hz : a < z.re) :
    ‖transform f z - transform g z‖ ^ 2 ≤
      normSquared a (fun x => f x - g x) / (2 * (z.re - a)) := by
  rw [← transform_sub hf hg (by linarith : (2 * a) / 2 < z.re)]
  exact evaluation_norm_sq_le (finiteEnergy_sub hf hg) hz

/-- Interface for all derivative evaluation constants. The companion
WeightedMellinDerivativeTopology supplies this proposition, and
WeightedMellinDerivativeSharpness proves optimality. The definition itself
supplies no proof or provider axiom. -/
def DerivativeEvaluationBoundProvider (a : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, Ha a f → ∀ k : ℕ, ∀ z : ℂ, a < z.re →
    ‖iteratedDeriv k (transform f) z‖ ^ 2 ≤
      normSquared a f * ((2 * k).factorial : ℝ) /
        (2 * (z.re - a)) ^ (2 * k + 1)

/-- Interface for the all-order derivative identity, supplied by the
WeightedMellinLogarithmicKernel and WeightedMellinDerivativeTopology companions.
The definition itself is not a proof or axiom. -/
def HigherDerivativeIntegralProvider (a : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, Ha a f → ∀ k : ℕ, ∀ z : ℂ, a < z.re →
    iteratedDeriv k (transform f) z =
      ∫ x in Ioi (1 : ℝ),
        f x * (x : ℂ) ^ (-z - 1) * (-(Real.log x : ℂ)) ^ k

open RiemannResearch.RH.AnnularPrimePair
open RiemannResearch.RH.AnnularZeroSpectral

/-- Every full strip zero is a uniformly bounded evaluation on H_a when
a<0. This uses only Re(rho)>0, so it does not assume RH or a zero-free strip.
It still requires membership of the vector being evaluated. -/
theorem fullZero_evaluation_uniform_of_negative_weight
    {ι : Type*} (D : FullZeroData ι) {f : ℝ → ℂ} {a : ℝ}
    (hf : Ha a f) (ha : a < 0) :
    ∀ i : ι, ‖transform f (D.rho i)‖ ^ 2 ≤ normSquared a f / (-2 * a) := by
  intro i
  have hzero := D.strip_left i
  have hmargin : a < (D.rho i).re := by linarith
  have hden : 0 < 2 * ((D.rho i).re - a) := by linarith
  have h := (le_div_iff₀ hden).mp (evaluation_norm_sq_le hf hmargin)
  apply (le_div_iff₀ (by linarith : 0 < -2 * a)).mpr
  have hprod := mul_nonneg (sq_nonneg ‖transform f (D.rho i)‖) hzero.le
  nlinarith

/-- The actual centered prime signal, including all von Mangoldt prime powers. -/
def actualAnnularVector : ℝ → ℂ := fun x => (actualPrimeSignal x : ℂ)

/-- Finite support in x, retaining the centered arithmetic signal itself. -/
def actualAnnularTruncation (X : ℝ) : ℝ → ℂ :=
  (Icc (1 : ℝ) X).indicator actualAnnularVector

/-- Local membership interface supplied by ActualAnnularTruncationMembership.
ActualAnnularTruncationEnvelope supplies a finite growing envelope; critical
infinite-vector control remains a separate arithmetic obligation. -/
def ActualTruncationMembershipProvider : Prop :=
  ∀ a X : ℝ, 1 ≤ X → Ha a (actualAnnularTruncation X)

/-- An actual arithmetic norm target; no uniform bound or convergence is assumed. -/
def ActualTruncationEnvelope (a : ℝ) (N : ℝ → ℝ) : Prop :=
  ∀ X : ℝ, 1 ≤ X → normSquared a (actualAnnularTruncation X) ≤ N X

/-- Full-zero evaluations are quantitatively controlled once the actual
truncated membership and its exact norm envelope are supplied. -/
theorem actualTruncation_fullZero_evaluation_bound
    {ι : Type*} (D : FullZeroData ι) (i : ι)
    {a X : ℝ} {N : ℝ → ℝ}
    (hmem : Ha a (actualAnnularTruncation X))
    (hnorm : normSquared a (actualAnnularTruncation X) ≤ N X)
    (ha : a < (D.rho i).re) :
    ‖transform (actualAnnularTruncation X) (D.rho i)‖ ^ 2 ≤
      N X / (2 * ((D.rho i).re - a)) := by
  have hden : 0 < 2 * ((D.rho i).re - a) := by linarith
  apply (le_div_iff₀ hden).mpr
  have h := (le_div_iff₀ hden).mp (evaluation_norm_sq_le hmem ha)
  exact h.trans hnorm

/-- The exact arithmetic family has a controlled evaluation difference at
every full zero with Re(rho)>a; no ordinate-only zero selection is made. -/
theorem actualTruncation_fullZero_difference_bound
    {ι : Type*} (D : FullZeroData ι) (i : ι) {a X Y : ℝ}
    (hX : Ha a (actualAnnularTruncation X))
    (hY : Ha a (actualAnnularTruncation Y))
    (ha : a < (D.rho i).re) :
    ‖transform (actualAnnularTruncation X) (D.rho i) -
      transform (actualAnnularTruncation Y) (D.rho i)‖ ^ 2 ≤
      normSquared a (fun x => actualAnnularTruncation X x - actualAnnularTruncation Y x) /
        (2 * ((D.rho i).re - a)) :=
  evaluation_difference_norm_sq_le hX hY ha

end RiemannResearch.Analysis.WeightedMellinTopology
