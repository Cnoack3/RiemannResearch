import RiemannResearch.RH.WeilArithmeticAdapter
import RiemannResearch.RH.WeilPrimeCutoffConvergence
import RiemannResearch.RH.WeilZeroSumConvergence
import RiemannResearch.RH.WeilCutoffArchimedeanConvergence

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Full Weil explicit formula on the actual smooth superexponential class

The compact formula is the proved formula for the actual zeta zeros and
their analytic multiplicities. Smooth compact cutoffs converge on the
zero, pole, complete von Mangoldt, and gamma sides, with all dominating
functions and summable zero weights supplied by proved providers.
-/

open MeasureTheory Set Filter Complex
open scoped BigOperators Topology FourierTransform

namespace RiemannResearch.RH.SignedWeilCorrelation

open RiemannResearch.Analysis

/-- Every part of the literal arithmetic expression converges to its actual
noncompact value under the specified smooth compact cutoff. -/
theorem tendsto_literatureRHS_compactCutoff_arithmetic {k : ℝ → ℂ}
    (hk : SmoothSuperexponentialDecay k) :
    Tendsto (fun N : ℕ => Zeta23.EF.literatureRHS (compactCutoff N k)) atTop
      (𝓝 (Zeta23.EF.literatureRHS k)) := by
  have hp := WeilExplicitFormula.tendsto_paperFT_pole_pair_compactCutoff hk
  have hprime := tendsto_paired_primePower_sum_compactCutoff hk
  have hgamma := WeilExplicitFormula.tendsto_normalized_gamma_compactCutoff hk
  simpa only [Zeta23.EF.literatureRHS, primePowerWeight] using (hp.sub hprime).add hgamma

/-- The full literal Weil formula for actual noncompact smooth tests. It
has no assumed explicit formula, zero count, or limiting identity. -/
theorem actual_noncompact_literal_Weil_explicit_formula {k : ℝ → ℂ}
    (hk : SmoothSuperexponentialDecay k) :
    (∑' ρ : Zeta23.zetaZeroConfig.carrier, (Zeta23.zeroMult ρ : ℂ) *
      Zeta23.paperFT k (Zeta23.gammaOf ρ)) = Zeta23.EF.literatureRHS k := by
  exact tendsto_nhds_unique
    (WeilExplicitFormula.tendsto_literatureRHS_compactCutoff hk)
    (tendsto_literatureRHS_compactCutoff_arithmetic hk)

/-- The same noncompact formula in the project's actual spatial arithmetic
normalization; ordinary test-class providers remain explicit at this layer. -/
theorem actual_noncompact_Weil_explicit_formula
    {k : ℝ → ℂ} (hk : SmoothSuperexponentialDecay k)
    (hki : Integrable k) (hFk : Integrable (𝓕 k))
    (heven : ∀ t, (k (-t)).re = (k t).re)
    (hHc : Continuous (fun r : ℝ => Zeta23.paperFT k r))
    (A : ℝ) (hA : 0 ≤ A)
    (hdec : ∀ r : ℝ, ‖Zeta23.paperFT k r‖ ≤ A / (1 + r ^ 2))
    (K : ℝ) (hK : 0 ≤ K) (hLip : ∀ t, 0 < t → |(k t).re - (k 0).re| ≤ K * t) :
    (∑' ρ : Zeta23.zetaZeroConfig.carrier, (Zeta23.zeroMult ρ : ℂ) *
      Zeta23.paperFT k (Zeta23.gammaOf ρ)).re =
      infinitePrimePowerCorrelationValue
        (Real.eulerMascheroniConstant + Real.log (4 * Real.pi)) (fun t => (k t).re) := by
  exact (congrArg Complex.re (actual_noncompact_literal_Weil_explicit_formula hk)).trans
    (literatureRHS_re_eq_infinitePrimePowerCorrelationValue hk.decay hk.1.continuous
      hki hFk heven hHc A hA hdec K hK hLip)

theorem norm_paperFT_real_le_of_smoothSuperexponential {k : ℝ → ℂ}
    (hk : SmoothSuperexponentialDecay k) (r : ℝ) :
    ‖Zeta23.paperFT k r‖ ≤ cutoffVerticalBound k 0 / (1 + r ^ 2) := by
  apply le_of_tendsto (WeilExplicitFormula.tendsto_paperFT_compactCutoff hk r).norm
  exact Eventually.of_forall fun N =>
    WeilExplicitFormula.norm_paperFT_compactCutoff_real_le hk N r

theorem continuous_paperFT_real_of_smoothSuperexponential {k : ℝ → ℂ}
    (hk : SmoothSuperexponentialDecay k) :
    Continuous (fun r : ℝ => Zeta23.paperFT k r) := by
  simp_rw [WeilExplicitFormula.paperFT_eq_centeredTransform]
  exact (BilateralLaplace.differentiable_centeredTransform
    (hk.decay.hasExponentialMoments hk.1.continuous)).continuous.comp (by fun_prop)

theorem integrable_paperFT_real_of_smoothSuperexponential {k : ℝ → ℂ}
    (hk : SmoothSuperexponentialDecay k) :
    Integrable (fun r : ℝ => Zeta23.paperFT k r) := by
  have hi : Integrable (fun r : ℝ => cutoffVerticalBound k 0 / (1 + r ^ 2)) := by
    simpa only [div_eq_mul_inv] using
      integrable_inv_one_add_sq.const_mul (cutoffVerticalBound k 0)
  exact hi.mono'
    (continuous_paperFT_real_of_smoothSuperexponential hk).aestronglyMeasurable
    (Eventually.of_forall fun r => norm_paperFT_real_le_of_smoothSuperexponential hk r)

theorem integrable_fourier_of_smoothSuperexponential {k : ℝ → ℂ}
    (hk : SmoothSuperexponentialDecay k) : Integrable (𝓕 k) := by
  have hi := (integrable_paperFT_real_of_smoothSuperexponential hk).comp_mul_left'
    (show (-(2 * Real.pi) : ℝ) ≠ 0 from
      neg_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  apply hi.congr
  apply ae_of_all
  intro r
  change Zeta23.paperFT k ((-(2 * Real.pi) * r : ℝ) : ℂ) = 𝓕 k r
  rw [Zeta23.EF.paperFT_ofReal_eq_fourier]
  congr 1
  field_simp

/-- The final spatial identification needs only membership in the actual
smooth superexponential class and the real symmetry of an autocorrelation.
Every integrability, decay, and Lipschitz provider is discharged here. -/
theorem actual_noncompact_Weil_explicit_formula_of_smooth
    {k : ℝ → ℂ} (hk : SmoothSuperexponentialDecay k)
    (heven : ∀ t, (k (-t)).re = (k t).re) :
    (∑' ρ : Zeta23.zetaZeroConfig.carrier, (Zeta23.zeroMult ρ : ℂ) *
      Zeta23.paperFT k (Zeta23.gammaOf ρ)).re =
      infinitePrimePowerCorrelationValue
        (Real.eulerMascheroniConstant + Real.log (4 * Real.pi)) (fun t => (k t).re) := by
  have hki : Integrable k :=
    (hk.decay.integrable_norm hk.1.continuous).mono' hk.1.continuous.aestronglyMeasurable
      (Eventually.of_forall fun _ => le_rfl)
  have hd : Differentiable ℝ k := hk.1.differentiable (by simp)
  obtain ⟨K, hK, hderiv⟩ := hk.deriv.decay.exists_deriv_bound
  have hLip (t : ℝ) (ht : 0 < t) : |(k t).re - (k 0).re| ≤ K * t := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun x (_ : x ∈ (univ : Set ℝ)) => hd x)
      (fun x (_ : x ∈ (univ : Set ℝ)) => hderiv x)
      (convex_univ : Convex ℝ (univ : Set ℝ)) (mem_univ (0 : ℝ)) (mem_univ t)
    have hreal : |(k t).re - (k 0).re| ≤ ‖k t - k 0‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (k t - k 0)
    exact hreal.trans (by simpa [Real.norm_eq_abs, abs_of_pos ht] using h)
  exact actual_noncompact_Weil_explicit_formula hk hki
    (integrable_fourier_of_smoothSuperexponential hk) heven
    (continuous_paperFT_real_of_smoothSuperexponential hk)
    (cutoffVerticalBound k 0) (cutoffVerticalBound_nonneg k 0)
    (norm_paperFT_real_le_of_smoothSuperexponential hk) K hK.le hLip

end RiemannResearch.RH.SignedWeilCorrelation
