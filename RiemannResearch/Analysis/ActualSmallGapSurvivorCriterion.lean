/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualSmallGapPairBound

/-!
# The compact deletion estimate on an actual separated zero array

Lamzouri's Proposition 3.2 controls the compact physical test after removal
of both endpoints of each small adjacent gap. A larger integrable test can
be used for the finite upper bound even if it has no compact support.
All comparisons retain the original zero count in the denominator.

<https://arxiv.org/html/2611.14486v1#S3>
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped Topology
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open LamzouriSmallGapCriterion

/-- Lower estimate for a particular compact test from the deletion theorem.
The same two functions control every sufficiently large height. -/
def compactDeletionLower (gapLimit θ : ℝ) (g : ℝ → ℝ) : Prop :=
  ∃ loss error : ℝ → ℝ, ContinuousAt loss 0 ∧ loss 0 = 0 ∧
    Tendsto error atTop (𝓝 0) ∧
    ∀ᶠ T : ℝ in atTop, smallGapFraction gapLimit T < 1/4 →
      objective θ g ≤ unmarkedGapPairSum gapLimit T (cosineTransform g) / (Ncount 0 T : ℝ)
        + loss (smallGapFraction gapLimit T) + error T

/-- A normalized Fourier test with a nonpositive separated tail can dominate
any compact test whose objective exceeds one. Only the smaller test needs
a deletion estimate. -/
theorem smallGapProportion_pos_of_dominated_cutoff {gapLimit θ : ℝ} {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (hgf : ∀ x, g x ≤ f x)
    (hunit : cosineTransform f 0 = 1)
    (htail : ∀ u, gapLimit < |u| → cosineTransform f u ≤ 0)
    (hM : 1 < objective θ g) (hd : compactDeletionLower gapLimit θ g) :
    0 < smallGapProportion gapLimit := by
  apply smallGapProportion_pos_of_separatedPairEstimate hM
  obtain ⟨loss,error,hcont,hzero,hlim,hpair⟩ := hd
  refine ⟨loss,error,hcont,hzero,hlim,?_⟩
  filter_upwards [hpair,eventually_ge_atTop (1:ℝ)] with T hp hT
  intro hs
  have hmono := div_le_div_of_nonneg_right (unmarked_pairSum_mono hg hf hgf gapLimit T)
    (Nat.cast_nonneg (Ncount 0 T) : (0:ℝ) ≤ (Ncount 0 T : ℝ))
  have hcap := normalized_unmarkedGapPairSum_le_one (gapLimit := gapLimit)
    (Real.log_nonneg hT) hunit htail
  linarith only [hp hs,hmono,hcap]

end RiemannResearch.Analysis.ActualZeroOrdinate
