import RiemannResearch.Analysis.SignedOptimizerMoment
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# A cofinal compressed-moment criterion for a limiting optimizer residual

Source: user-provided `Exact_Optimizer_Cancellation_20261008.tex` and the
continuation of its signed second-moment criterion. The proof below supplies
the cofinal geometric argument; it does not use monotonicity of normalized
moments.

If optimizer residuals converge strongly and the multiplier has a faithful
quadratic form, vanishing normalized screened moments on any cofinal sequence
force the limiting residual to be zero. The exact screening pairing is kept
as a hypothesis in the general theorem and proved from normal equations in
the finite-dictionary application. Strong residual convergence automatically
controls the changing normalization, so no separate uniform-norm bound is
needed.

The signed application preserves the complete weighted floor, mismatch, and
screening terms. Its analytic small-floor input and positive signed-correction
input remain explicit. These are conditional geometric reductions, not a
proved RH statement or an arithmetic provider.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis.CompressedMomentZeroCriterion

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The changing residual normalization is controlled by strong convergence:
`‖s n‖² = ‖r n‖² * (‖s n‖² / ‖r n‖²)` exactly. -/
theorem screenedVector_tendsto_zero_of_normalizedMoment
    (r s : ℕ → H) (rLimit : H)
    (hr : Tendsto r atTop (𝓝 rLimit)) (hpos : ∀ n, 0 < ‖r n‖ ^ 2)
    (hmoment : Tendsto (fun n => ‖s n‖ ^ 2 / ‖r n‖ ^ 2) atTop (𝓝 0)) :
    Tendsto s atTop (𝓝 0) := by
  have heq : (fun n => ‖s n‖ ^ 2) =
      (fun n => ‖r n‖ ^ 2 * (‖s n‖ ^ 2 / ‖r n‖ ^ 2)) := by
    funext n
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt (hpos n))]
  have hsquare : Tendsto (fun n => ‖s n‖ ^ 2) atTop (𝓝 0) := by
    rw [heq]
    simpa using (hr.norm.pow 2).mul hmoment
  have hnorm : Tendsto (fun n => ‖s n‖) atTop (𝓝 0) := by
    simpa [Real.sqrt_sq_eq_abs] using hsquare.sqrt
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa using hnorm

/-- A faithful positive multiplier detects every nonzero limiting residual.
Symmetry is unnecessary for this direction; the actual reciprocal multiplier
is symmetric and positive as well. -/
theorem limit_eq_zero_of_normalizedScreenedMoment
    (D : H →L[ℝ] H)
    (hfaithful : ∀ x : H, inner ℝ x (D x) = 0 → x = 0)
    (r s : ℕ → H) (rLimit : H) (hr : Tendsto r atTop (𝓝 rLimit))
    (hpos : ∀ n, 0 < ‖r n‖ ^ 2)
    (hpairing : ∀ n, inner ℝ (r n) (s n) = inner ℝ (r n) (D (r n)))
    (hmoment : Tendsto (fun n => ‖s n‖ ^ 2 / ‖r n‖ ^ 2) atTop (𝓝 0)) :
    rLimit = 0 := by
  have hs := screenedVector_tendsto_zero_of_normalizedMoment r s rLimit hr hpos hmoment
  have hform : Tendsto (fun n => inner ℝ (r n) (D (r n))) atTop
      (𝓝 (inner ℝ rLimit (D rLimit))) :=
    hr.inner (𝕜 := ℝ) ((D.continuous.tendsto rLimit).comp hr)
  have hzero : Tendsto (fun n => inner ℝ (r n) (D (r n))) atTop (𝓝 0) := by
    have heq : (fun n => inner ℝ (r n) (D (r n))) =
        (fun n => inner ℝ (r n) (s n)) :=
      funext (fun n => (hpairing n).symm)
    rw [heq]
    simpa using hr.inner (𝕜 := ℝ) hs
  exact hfaithful rLimit (tendsto_nhds_unique hform hzero)

/-- Cofinal vanishing suffices even when normalized moments are not monotone. -/
theorem limit_eq_zero_of_cofinal_normalizedScreenedMoment
    (D : H →L[ℝ] H)
    (hfaithful : ∀ x : H, inner ℝ x (D x) = 0 → x = 0)
    (r s : ℕ → H) (rLimit : H) (hr : Tendsto r atTop (𝓝 rLimit))
    (hpos : ∀ n, 0 < ‖r n‖ ^ 2)
    (hpairing : ∀ n, inner ℝ (r n) (s n) = inner ℝ (r n) (D (r n)))
    (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (hmoment : Tendsto (fun j => ‖s (κ j)‖ ^ 2 / ‖r (κ j)‖ ^ 2)
      atTop (𝓝 0)) :
    rLimit = 0 :=
  limit_eq_zero_of_normalizedScreenedMoment D hfaithful
    (fun j => r (κ j)) (fun j => s (κ j)) rLimit (hr.comp hκ)
    (fun j => hpos (κ j)) (fun j => hpairing (κ j)) hmoment

/-- For strongly convergent residuals, zero limiting residual and vanishing
unnormalized complete error are equivalent. -/
theorem residualEnergy_tendsto_zero_iff_limit_eq_zero
    (r : ℕ → H) (rLimit : H) (hr : Tendsto r atTop (𝓝 rLimit)) :
    Tendsto (fun n => ‖r n‖ ^ 2) atTop (𝓝 0) ↔ rLimit = 0 := by
  constructor
  · intro hzero
    have heq : ‖rLimit‖ ^ 2 = 0 := tendsto_nhds_unique (hr.norm.pow 2) hzero
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg rLimit]
  · intro hzero
    subst rLimit
    simpa using hr.norm.pow 2

/-- Cofinal normalized compressed-moment decay yields full error decay. -/
theorem residualEnergy_tendsto_zero_of_cofinal_normalizedScreenedMoment
    (D : H →L[ℝ] H)
    (hfaithful : ∀ x : H, inner ℝ x (D x) = 0 → x = 0)
    (r s : ℕ → H) (rLimit : H) (hr : Tendsto r atTop (𝓝 rLimit))
    (hpos : ∀ n, 0 < ‖r n‖ ^ 2)
    (hpairing : ∀ n, inner ℝ (r n) (s n) = inner ℝ (r n) (D (r n)))
    (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (hmoment : Tendsto (fun j => ‖s (κ j)‖ ^ 2 / ‖r (κ j)‖ ^ 2)
      atTop (𝓝 0)) :
    Tendsto (fun n => ‖r n‖ ^ 2) atTop (𝓝 0) :=
  (residualEnergy_tendsto_zero_iff_limit_eq_zero r rLimit hr).mpr
    (limit_eq_zero_of_cofinal_normalizedScreenedMoment D hfaithful
      r s rLimit hr hpos hpairing κ hκ hmoment)

open RiemannResearch.LinearAlgebra
open RiemannResearch.Analysis.SignedOptimizerMoment

/-- The literal finite optimizer geometry supplies the screening pairing.
The only new decay provider is the cofinal positive signed correction after
the actual weighted floor is small. Both positive squares in `Γ` survive. -/
theorem finiteResidual_limit_eq_zero_of_cofinal_positiveCorrection
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (x : H) (z : ∀ n, ι n → H) (D : H →L[ℝ] H)
    (hfaithful : ∀ v : H, inner ℝ v (D v) = 0 → v = 0)
    (c cD b : ∀ n, ι n → ℝ) (rLimit : H)
    (hr : Tendsto (fun n => finiteSchurResidual x (z n) (c n)) atTop (𝓝 rLimit))
    (hpos : ∀ n, 0 < ‖finiteSchurResidual x (z n) (c n)‖ ^ 2)
    (hc : ∀ n i, inner ℝ (z n i) (finiteSchurCombination (z n) (c n)) =
      inner ℝ (z n i) x)
    (hcD : ∀ n i, inner ℝ (D (z n i))
      (finiteSchurCombination (fun j => D (z n j)) (cD n)) =
        inner ℝ (D (z n i)) (D x))
    (hb : ∀ n i, inner ℝ (z n i) (finiteSchurCombination (z n) (b n)) =
      inner ℝ (z n i) (D (finiteSchurResidual x (z n) (c n))))
    (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (hfloor : Tendsto
      (fun j => weightedOptimizerFloor x (z (κ j)) D.toLinearMap (cD (κ j)) /
        ‖finiteSchurResidual x (z (κ j)) (c (κ j))‖ ^ 2) atTop (𝓝 0))
    (hcorrection : Tendsto
      (fun j => max (signedOptimizerCorrection (z (κ j)) D.toLinearMap
        (c (κ j)) (cD (κ j)) (b (κ j))) 0 /
        ‖finiteSchurResidual x (z (κ j)) (c (κ j))‖ ^ 2) atTop (𝓝 0)) :
    rLimit = 0 := by
  have hmoment := (screenedWeightedMoment_normalized_tendsto_iff
    x (fun j => z (κ j)) D.toLinearMap (fun j => c (κ j))
    (fun j => cD (κ j)) (fun j => b (κ j))
    (fun j => ‖finiteSchurResidual x (z (κ j)) (c (κ j))‖ ^ 2)
    (fun j => hpos (κ j)) (fun j => hcD (κ j)) (fun j => hb (κ j)) hfloor).mpr
      hcorrection
  apply limit_eq_zero_of_cofinal_normalizedScreenedMoment D hfaithful
    (fun n => finiteSchurResidual x (z n) (c n))
    (fun n => finiteSchurResidual
      (D (finiteSchurResidual x (z n) (c n))) (z n) (b n))
    rLimit hr hpos ?_ κ hκ ?_
  · intro n
    exact originalResidual_inner_screened x _ (z n) (c n) (b n) (hc n)
  · exact hmoment

end RiemannResearch.Analysis.CompressedMomentZeroCriterion
