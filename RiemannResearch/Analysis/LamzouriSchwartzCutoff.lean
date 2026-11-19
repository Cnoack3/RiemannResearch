/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualSmallGapSurvivorCriterion
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Extending the small-gap test to integrable smooth functions

A smooth physical cutoff on the strictly available support preserves the
objective and is dominated pointwise by the original nonnegative function.
The compact source is Lamzouri's Proposition 3.2 specialized to deletion of
the two endpoints of each small internal gap, with the zero-count factor
and the logarithmic height error retained. Its deleted set is invariant
under reflection because all copies at a repeated ordinate are marked.
-/

noncomputable section
open MeasureTheory Filter Zeta23 Set
open scoped Topology Interval
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open LamzouriSmallGapCriterion

/-- Specialized compact-test consequence of Lemma 3.1 and Proposition 3.2.
Each original zero occurrence enters the normalized count. -/
class LamzouriCompactDeletion2026 : Prop where
  lower {gapLimit θ : ℝ} (g : ℝ → ℝ) :
    0 < gapLimit → gapLimit ≤ 1 → 1/2 < θ → θ < 4/7 →
    ContDiff ℝ 2 g → Function.Even g → (∀ x, θ ≤ |x| → g x = 0) →
      compactDeletionLower gapLimit θ g

/-- The original Fourier test may have unbounded physical support. -/
theorem smallGapProportion_pos_of_smooth_integrable_test [s : LamzouriCompactDeletion2026]
    {gapLimit θ : ℝ} {f : ℝ → ℝ}
    (hgapPos : 0 < gapLimit) (hgapOne : gapLimit ≤ 1) (hθ : 1/2 < θ) (hθ₁ : θ < 4/7)
    (hf : Integrable f) (hs : ContDiff ℝ 2 f) (he : Function.Even f)
    (hn : ∀ x, 0 ≤ f x) (hunit : cosineTransform f 0 = 1)
    (htail : ∀ u, gapLimit < |u| → cosineTransform f u ≤ 0) (hM : 1 < objective θ f) :
    0 < smallGapProportion gapLimit := by
  obtain ⟨θ',hlo,hhi⟩ := exists_between hθ₁
  have hθ₀ : 0 < θ := by linarith
  let χ : ContDiffBump (0:ℝ) := ⟨θ,θ',hθ₀,hlo⟩
  let g := fun x : ℝ => χ x * f x
  have hgs : ContDiff ℝ 2 g := χ.contDiff.mul hs
  have hgc : HasCompactSupport g := χ.hasCompactSupport.mul_right
  have hgd : ∀ x, g x ≤ f x := fun x => (mul_le_mul_of_nonneg_right χ.le_one (hn x)).trans_eq (one_mul _)
  have hgn (x : ℝ) : 0 ≤ g x := mul_nonneg χ.nonneg (hn x)
  have hinner {x : ℝ} (hx : |x| ≤ θ) : g x = f x := by
    have hball : x ∈ Metric.closedBall (0:ℝ) χ.rIn := by simpa [Real.dist_eq] using hx
    simp only [g,χ.one_of_mem_closedBall hball,one_mul]
  have hzero : g 0 = f 0 := hinner (by simpa using hθ₀.le)
  have hsame : (∫ x in (0:ℝ)..θ, x * g x) = ∫ x in (0:ℝ)..θ, x * f x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hθ₀.le] at hx
    change x * g x = x * f x
    rw [hinner (x := x) (by simpa only [abs_of_nonneg hx.1] using hx.2)]
  have hnextra := intervalIntegral.integral_nonneg (f := fun x : ℝ => x*g x) (μ := volume)
    hlo.le (fun x hx => mul_nonneg (hθ₀.le.trans hx.1) (hgn x))
  have hcont : Continuous (fun x : ℝ => x*g x) := continuous_id.mul hgs.continuous
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) 0 θ) (hcont.intervalIntegrable (μ := volume) θ θ')
  have hM' : 1 < objective θ' g := by
    unfold objective at hM ⊢
    linarith only [hM,hzero,hsame,hnextra,hadd]
  apply smallGapProportion_pos_of_dominated_cutoff hf (hgs.continuous.integrable_of_hasCompactSupport hgc)
    hgd hunit htail hM'
  apply s.lower g hgapPos hgapOne (hθ.trans hlo) hhi hgs
  · intro x
    simp only [g,χ.neg,he x]
  · intro x hx
    have hh : χ.rOut ≤ dist x (0:ℝ) := by simpa [Real.dist_eq] using hx
    simp only [g,χ.zero_of_le_dist hh,zero_mul]

end RiemannResearch.Analysis.ActualZeroOrdinate
