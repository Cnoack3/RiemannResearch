/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualSmallGapProportion
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Support

/-!
# Lamzouri's compact Fourier test for a positive proportion of small gaps

Theorem 3.3 of Y. Lamzouri, *The distribution of small gaps between zeros
of the Riemann zeta function*, arXiv:2611.14486v1 (10 November 2026).
<https://arxiv.org/html/2611.14486v1#S3>

Real even tests have real Fourier transform equal to their cosine
transform. The exact internal-gap count differs from the source convention
by at most the single pair crossing T. The denominator is the count of all
positive zero occurrences through T; it tends to infinity by Riemann–von
Mangoldt. The named proposition class lets callers provide the general literature
criterion explicitly. No instance is installed by this module.
-/

noncomputable section

open MeasureTheory
open scoped Interval

namespace RiemannResearch.Analysis.LamzouriSmallGapCriterion

open ActualZeroOrdinate

/-- Real Fourier transform of an even test, with the source's 2π normalization. -/
def cosineTransform (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ x : ℝ, f x * Real.cos (2 * Real.pi * x * u)

/-- Formula (3.12) in the source. -/
def objective (θ : ℝ) (f : ℝ → ℝ) : ℝ :=
  f 0 + 2 * ∫ x in (0 : ℝ)..θ, x * f x

/-- A compact witness for every function hypothesis of Theorem 3.3. -/
structure Admissible (gapLimit θ : ℝ) (f : ℝ → ℝ) : Prop where
  compact : HasCompactSupport f
  smooth : ContDiff ℝ 2 f
  even : Function.Even f
  nonnegative : ∀ x, 0 ≤ f x
  normalization : cosineTransform f 0 = 1
  outside : ∀ u, gapLimit < |u| → cosineTransform f u ≤ 0
  excess : 1 < objective θ f

/-- The source theorem as a proposition, independently usable by callers
which supply their own proof or import policy. -/
def SourceCriterion : Prop :=
  ∀ (θ gapLimit : ℝ) (f : ℝ → ℝ), 1 / 2 < θ → θ < 4 / 7 →
    0 < gapLimit → gapLimit ≤ 1 → Admissible gapLimit θ f → 0 < smallGapProportion gapLimit

/-- Scoped external source provider for Lamzouri (2026), Theorem 3.3.
The degree, polynomial coefficients, and target gap are quantified. -/
class Lamzouri2026 : Prop where
  theorem33 : SourceCriterion

/-- A compactification or direct compact certificate can supply the
remaining witness without presupposing a positive actual-gap proportion. -/
theorem smallGapProportion_pos_of_compact_witness
    [hsource : Lamzouri2026] {θ gapLimit : ℝ} (hlo : 1 / 2 < θ) (hhi : θ < 4 / 7)
    (hgapLimit : 0 < gapLimit) (hgapLimit' : gapLimit ≤ 1) (hw : ∃ f, Admissible gapLimit θ f) :
    0 < smallGapProportion gapLimit := by
  obtain ⟨f, hf⟩ := hw
  exact hsource.theorem33 θ gapLimit f hlo hhi hgapLimit hgapLimit' hf

end RiemannResearch.Analysis.LamzouriSmallGapCriterion
