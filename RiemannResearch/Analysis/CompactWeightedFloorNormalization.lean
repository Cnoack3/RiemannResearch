import RiemannResearch.Analysis.SignedOptimizerMoment
import RiemannResearch.Analysis.FiniteHeadWeakContinuity
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Normalize a small weighted floor without an inverse-log lower bound

Source: the exact optimizer cancellation continuation, 8 October 2026.
If the limiting residual is nonzero, its complete energy has a nonzero limit,
so ordinary division preserves absolute weighted-floor decay. If the limiting
residual is zero, domination by the compact weighted residual supplies the
normalized decay. This case distinction is exact and does not assume RH.

The zero-case compact-ratio input is stated explicitly in this general
assembly theorem. It is a Hilbert-geometric provider, rather than an assumed
arithmetic cancellation estimate. Rates are not asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.CompactWeightedFloorNormalization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Absolute floor decay plus compact domination proves relative floor decay
by considering the zero and nonzero limiting residual separately. -/
theorem weightedFloor_ratio_tendsto_zero
    (r : ℕ → H) (rLimit : H) (D : H →L[ℝ] H) (ε : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 rLimit)) (hpos : ∀ n, 0 < ‖r n‖ ^ 2)
    (hε : ∀ n, 0 ≤ ε n) (hbound : ∀ n, ε n ≤ ‖D (r n)‖ ^ 2)
    (hfloor : Tendsto ε atTop (𝓝 0))
    (hcompact : rLimit = 0 →
      Tendsto (fun n => ‖D (r n)‖ ^ 2 / ‖r n‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => ε n / ‖r n‖ ^ 2) atTop (𝓝 0) := by
  by_cases hzero : rLimit = 0
  · exact squeeze_zero
      (fun n => div_nonneg (hε n) (hpos n).le)
      (fun n => div_le_div_of_nonneg_right (hbound n) (hpos n).le)
      (hcompact hzero)
  · have hnorm : ‖rLimit‖ ≠ 0 := norm_ne_zero_iff.mpr hzero
    have henergy : ‖rLimit‖ ^ 2 ≠ 0 := pow_ne_zero 2 hnorm
    have h := hfloor.div (hr.norm.pow 2) henergy
    have heq : (ε / (fun n => ‖r n‖ ^ 2)) =
        (fun n => ε n / ‖r n‖ ^ 2) := by
      funext n
      rfl
    rw [heq] at h
    simpa only [zero_div] using h

open RiemannResearch.LinearAlgebra
open RiemannResearch.Analysis.SignedOptimizerMoment

/-- The weighted optimum is bounded by the complete weighted error of the
original coefficient vector, with the optimizer mismatch retained exactly. -/
theorem weightedOptimizerFloor_le_originalWeightedResidual
    {ι : Type*} [Fintype ι] (x : H) (z : ι → H)
    (D : H →ₗ[ℝ] H) (c cD : ι → ℝ)
    (hcD : ∀ i, inner ℝ (D (z i))
      (finiteSchurCombination (fun j => D (z j)) cD) =
        inner ℝ (D (z i)) (D x)) :
    weightedOptimizerFloor x z D cD ≤ ‖D (finiteSchurResidual x z c)‖ ^ 2 := by
  rw [weightedResidual_eq_floor_add_mismatch x z D c cD hcD]
  exact le_add_of_nonneg_right (weightedOptimizerMismatch_nonneg z D c cD)

/-- The floor in this theorem is the actual normal-equation optimum. There
is no Burnol lower bound or assumed relative arithmetic estimate. -/
theorem actualWeightedOptimizerFloor_ratio_tendsto_zero
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (x : H) (z : ∀ n, ι n → H) (D : H →L[ℝ] H)
    (c cD : ∀ n, ι n → ℝ) (rLimit : H)
    (hr : Tendsto (fun n => finiteSchurResidual x (z n) (c n)) atTop (𝓝 rLimit))
    (hpos : ∀ n, 0 < ‖finiteSchurResidual x (z n) (c n)‖ ^ 2)
    (hcD : ∀ n i, inner ℝ (D (z n i))
      (finiteSchurCombination (fun j => D (z n j)) (cD n)) =
        inner ℝ (D (z n i)) (D x))
    (hfloor : Tendsto
      (fun n => weightedOptimizerFloor x (z n) D.toLinearMap (cD n)) atTop (𝓝 0))
    (hcompact : rLimit = 0 → Tendsto
      (fun n => ‖D (finiteSchurResidual x (z n) (c n))‖ ^ 2 /
        ‖finiteSchurResidual x (z n) (c n)‖ ^ 2) atTop (𝓝 0)) :
    Tendsto
      (fun n => weightedOptimizerFloor x (z n) D.toLinearMap (cD n) /
        ‖finiteSchurResidual x (z n) (c n)‖ ^ 2) atTop (𝓝 0) := by
  apply weightedFloor_ratio_tendsto_zero
    (fun n => finiteSchurResidual x (z n) (c n)) rLimit D
    (fun n => weightedOptimizerFloor x (z n) D.toLinearMap (cD n))
    hr hpos (fun n => weightedOptimizerFloor_nonneg x (z n) D.toLinearMap (cD n))
    (fun n => weightedOptimizerFloor_le_originalWeightedResidual
      x (z n) D.toLinearMap (c n) (cD n) (hcD n)) hfloor hcompact

variable [CompleteSpace H]
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.FiniteHeadWeakContinuity

/-- Canonical projection geometry supplies both the strong residual limit and
the zero-limit compact-ratio provider. Only the concrete finite-head operator
approximation and absolute arithmetic floor decay remain as inputs. -/
theorem canonicalWeightedFloor_ratio_tendsto_zero
    (v : ℕ → H) (x : H) (D : H →L[ℝ] H)
    (F : ℕ → H →L[ℝ] H) (ε : ℕ → ℝ)
    (hne : ∀ n, x - (walkSpan v id n).starProjection x ≠ 0)
    (hε : ∀ n, 0 ≤ ε n)
    (hbound : ∀ n, ε n ≤ ‖D (x - (walkSpan v id n).starProjection x)‖ ^ 2)
    (hfloor : Tendsto ε atTop (𝓝 0))
    (htail : Tendsto (fun j => ‖D - F j‖) atTop (𝓝 0))
    (hfinite : ∀ j, ∃ m : ℕ, ∃ a b : Fin m → H,
      ∀ y, F j y = ∑ i : Fin m, inner ℝ (a i) y • b i) :
    Tendsto
      (fun n => ε n / ‖x - (walkSpan v id n).starProjection x‖ ^ 2)
      atTop (𝓝 0) := by
  have hr : Tendsto (fun n => x - (walkSpan v id n).starProjection x) atTop
      (𝓝 (x - (RiemannResearch.Analysis.ExhaustiveWalk.dictionaryClosure v).starProjection x)) :=
    tendsto_const_nhds.sub (walkProjection_tendsto v id Function.surjective_id x)
  apply weightedFloor_ratio_tendsto_zero
    (fun n => x - (walkSpan v id n).starProjection x)
    (x - (RiemannResearch.Analysis.ExhaustiveWalk.dictionaryClosure v).starProjection x) D ε hr
    (fun n => sq_pos_of_pos (norm_pos_iff.mpr (hne n))) hε hbound hfloor
  intro hzero
  apply normalizedWalkResidual_image_energy_ratio_tendsto_zero
    v x D F ?_ hne htail hfinite
  simpa only [hzero] using hr

end RiemannResearch.Analysis.CompactWeightedFloorNormalization
