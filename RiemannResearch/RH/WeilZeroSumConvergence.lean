import RiemannResearch.RH.WeilExplicitFormula
import RiemannResearch.Analysis.CompactCutoffVerticalDecay
import Mathlib.Analysis.Normed.Group.Tannery

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual noncompact Weil zero sums and their compact approximation

The zeros and multiplicities are those of Mathlib's actual `riemannZeta`.
The compact explicit formula and inverse-square zero-sum majorant come
from the imported unconditional Weil proof. Uniform transform bounds and
pointwise convergence come from the actual smooth cutoffs of a smooth
superexponential function. No zero-sum identification is assumed.

The last theorem identifies the limit of the *complete compact arithmetic
right-hand sides*. Identifying that limit with the noncompact arithmetic
expression requires the separate pole, prime-power, and gamma limit lemmas.
-/

open MeasureTheory Complex Filter
open scoped Topology
open RiemannResearch.Analysis

namespace RiemannResearch.RH.WeilExplicitFormula

noncomputable section

/-- The sign convention relating the upstream Fourier transform to the
actual bilateral Laplace transform. -/
theorem paperFT_gammaOf_eq_centeredTransform (k : ℝ → ℂ) (s : ℂ) :
    Zeta23.paperFT k (Zeta23.gammaOf s) =
      BilateralLaplace.centeredTransform k (1 - s) := by
  unfold Zeta23.paperFT Zeta23.gammaOf BilateralLaplace.centeredTransform
    BilateralLaplace.transform BilateralLaplace.kernel
  apply integral_congr_ae
  filter_upwards with x
  congr 2
  field_simp [Complex.I_ne_zero]
  <;> ring

/-- Pointwise cutoff convergence at every actual zero, including the exact
sign convention in the explicit formula. -/
theorem tendsto_paperFT_gammaOf_compactCutoff {k : ℝ → ℂ}
    (hk : SmoothSuperexponentialDecay k) (s : ℂ) :
    Tendsto (fun N : ℕ => Zeta23.paperFT (compactCutoff N k) (Zeta23.gammaOf s))
      atTop (𝓝 (Zeta23.paperFT k (Zeta23.gammaOf s))) := by
  simp_rw [paperFT_gammaOf_eq_centeredTransform]
  exact tendsto_centeredTransform_compactCutoff hk (1 - s)

/-- Uniform domination at every zero by the actual summable zero weight. -/
theorem norm_actual_cutoff_zero_term_le {k : ℝ → ℂ}
    (hk : SmoothSuperexponentialDecay k) (N : ℕ)
    (ρ : Zeta23.zetaZeroConfig.carrier) :
    ‖(Zeta23.zeroMult ρ : ℂ) *
      Zeta23.paperFT (compactCutoff N k) (Zeta23.gammaOf ρ)‖ ≤
      (2 * cutoffVerticalBound k (1 / 2)) *
        ((Zeta23.zeroMult ρ : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ))) := by
  have hstrip := Zeta23.zetaZeroConfig.strip (ρ : ℂ) ρ.property
  have hs : |((1 - (ρ : ℂ)) - 1 / 2).re| ≤ (1 / 2 : ℝ) := by
    rw [abs_le]
    constructor <;> norm_num <;> linarith [hstrip.1, hstrip.2]
  have hB := norm_centeredTransform_compactCutoff_le hk
    (by norm_num : (0 : ℝ) ≤ 1 / 2) N (1 - (ρ : ℂ)) hs
  have hFT : ‖Zeta23.paperFT (compactCutoff N k) (Zeta23.gammaOf ρ)‖ ≤
      cutoffVerticalBound k (1 / 2) / (1 + |(ρ : ℂ).im| ^ 2) := by
    rw [paperFT_gammaOf_eq_centeredTransform]
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using hB
  have hgamma := Zeta23.WeilEF.abs_gammaOf_im_le hstrip
  have hgamma' := abs_le.mp hgamma
  have hden : 1 + Complex.normSq (Zeta23.gammaOf ρ) ≤
      2 * (1 + |(ρ : ℂ).im| ^ 2) := by
    rw [Complex.normSq_apply, Zeta23.WeilEF.gammaOf_re, sq_abs]
    nlinarith [hgamma'.1, hgamma'.2, sq_nonneg ((ρ : ℂ).im)]
  have hT : 0 < 1 + |(ρ : ℂ).im| ^ 2 := by positivity
  have hD : 0 < 1 + Complex.normSq (Zeta23.gammaOf ρ) := by
    linarith [Complex.normSq_nonneg (Zeta23.gammaOf (ρ : ℂ))]
  have hBn := cutoffVerticalBound_nonneg k (1 / 2)
  have hratio : cutoffVerticalBound k (1 / 2) / (1 + |(ρ : ℂ).im| ^ 2) ≤
      (2 * cutoffVerticalBound k (1 / 2)) /
        (1 + Complex.normSq (Zeta23.gammaOf ρ)) := by
    apply (div_le_div_iff₀ hT hD).2
    nlinarith [mul_le_mul_of_nonneg_left hden hBn]
  rw [norm_mul, Complex.norm_natCast]
  calc
    (Zeta23.zeroMult ρ : ℝ) *
        ‖Zeta23.paperFT (compactCutoff N k) (Zeta23.gammaOf ρ)‖ ≤
        (Zeta23.zeroMult ρ : ℝ) *
          ((2 * cutoffVerticalBound k (1 / 2)) /
            (1 + Complex.normSq (Zeta23.gammaOf ρ))) :=
      mul_le_mul_of_nonneg_left (hFT.trans hratio) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The same majorant bounds the actual noncompact terms by pointwise
convergence; no separate spectral estimate is postulated. -/
theorem norm_actual_zero_term_le {k : ℝ → ℂ}
    (hk : SmoothSuperexponentialDecay k) (ρ : Zeta23.zetaZeroConfig.carrier) :
    ‖(Zeta23.zeroMult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)‖ ≤
      (2 * cutoffVerticalBound k (1 / 2)) *
        ((Zeta23.zeroMult ρ : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ))) := by
  have ht : Tendsto (fun N : ℕ => (Zeta23.zeroMult ρ : ℂ) *
      Zeta23.paperFT (compactCutoff N k) (Zeta23.gammaOf ρ)) atTop
      (𝓝 ((Zeta23.zeroMult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ))) :=
    tendsto_const_nhds.mul (tendsto_paperFT_gammaOf_compactCutoff hk ρ)
  exact le_of_tendsto ht.norm
    (Eventually.of_forall fun N => norm_actual_cutoff_zero_term_le hk N ρ)

/-- Absolute convergence of the actual noncompact zero sum. -/
theorem summable_norm_actual_zero_terms {k : ℝ → ℂ}
    (hk : SmoothSuperexponentialDecay k) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      ‖(Zeta23.zeroMult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)‖) := by
  apply (reciprocal_square_zero_sum_summable.mul_left
    (2 * cutoffVerticalBound k (1 / 2))).of_norm_bounded
  intro ρ
  simpa only [norm_norm] using norm_actual_zero_term_le hk ρ

theorem summable_actual_zero_terms {k : ℝ → ℂ}
    (hk : SmoothSuperexponentialDecay k) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zeroMult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)) :=
  (summable_norm_actual_zero_terms hk).of_norm

/-- Dominated convergence of the actual zero sum, with the summable
majorant supplied by the unconditional ζ zero-counting theorem. -/
theorem tendsto_actual_zero_sum_compactCutoff {k : ℝ → ℂ}
    (hk : SmoothSuperexponentialDecay k) :
    Tendsto (fun N : ℕ => ∑' ρ : Zeta23.zetaZeroConfig.carrier,
      (Zeta23.zeroMult ρ : ℂ) *
        Zeta23.paperFT (compactCutoff N k) (Zeta23.gammaOf ρ)) atTop
      (𝓝 (∑' ρ : Zeta23.zetaZeroConfig.carrier,
        (Zeta23.zeroMult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ))) := by
  apply tendsto_tsum_of_dominated_convergence
    (reciprocal_square_zero_sum_summable.mul_left (2 * cutoffVerticalBound k (1 / 2)))
  · intro ρ
    exact tendsto_const_nhds.mul (tendsto_paperFT_gammaOf_compactCutoff hk ρ)
  · exact Eventually.of_forall fun N ρ => norm_actual_cutoff_zero_term_le hk N ρ

/-- The complete arithmetic sides of the compact formulas converge to the
actual noncompact zero sum. This uses the proved compact EF, not an assumed
identification between a chosen arithmetic functional and the zeros. -/
theorem tendsto_literatureRHS_compactCutoff {k : ℝ → ℂ}
    (hk : SmoothSuperexponentialDecay k) :
    Tendsto (fun N : ℕ => Zeta23.EF.literatureRHS (compactCutoff N k)) atTop
      (𝓝 (∑' ρ : Zeta23.zetaZeroConfig.carrier,
        (Zeta23.zeroMult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ))) := by
  apply (tendsto_actual_zero_sum_compactCutoff hk).congr'
  apply Eventually.of_forall
  intro N
  exact (Zeta23.WeilEF.EF_lit_zetaZeroConfig (compactCutoff N k)
    ((compactCutoff_contDiff hk.1 N).of_le
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 2).le)
    (compactCutoff_hasCompactSupport N k)).2

end
end RiemannResearch.RH.WeilExplicitFormula
