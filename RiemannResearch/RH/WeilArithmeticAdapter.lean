import RiemannResearch.RH.WeilGammaFourierAdapter
import RiemannResearch.RH.WeilExplicitFormula.WeilEF.Main

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Identification with the actual compact Weil explicit formula

The source theorem is the unconditional explicit formula for Mathlib's
`riemannZeta`, using its actual nontrivial-zero set and analytic multiplicities.
The pole, prime, and gamma terms are all transported to the existing spatial
arithmetic expression. No explicit-formula hypothesis is introduced.
-/

open MeasureTheory Set Filter Complex
open scoped BigOperators Topology FourierTransform

namespace RiemannResearch.RH.SignedWeilCorrelation

open RiemannResearch.Analysis

noncomputable section

theorem summable_paired_primePowerTerm {k : ℝ → ℂ}
    (hk : SuperexponentialDecay k) :
    Summable (fun n : ℕ => (primePowerWeight n : ℂ) *
      (k (Real.log n) + k (-Real.log n))) := by
  obtain ⟨A, _, hA⟩ := hk 3 (by norm_num)
  have hp := summable_primePowerTerm_of_exp_decay k A
    (fun t ht => by simpa only [abs_of_nonneg ht] using hA t)
  have hn := summable_primePowerTerm_of_exp_decay (fun t => k (-t)) A
    (fun t ht => by simpa only [abs_neg, abs_of_nonneg ht] using hA (-t))
  exact (hp.add hn).congr (fun n => by ring)

theorem re_paired_primePower_sum {k : ℝ → ℂ}
    (hk : SuperexponentialDecay k) (heven : ∀ t, (k (-t)).re = (k t).re) :
    (∑' n : ℕ, (primePowerWeight n : ℂ) *
      (k (Real.log n) + k (-Real.log n))).re =
      2 * ∑' n : ℕ, primePowerWeight n * (k (Real.log n)).re := by
  have h := Complex.reCLM.map_tsum (summable_paired_primePowerTerm hk)
  change (∑' n : ℕ, (primePowerWeight n : ℂ) *
      (k (Real.log n) + k (-Real.log n))).re =
    ∑' n : ℕ, ((primePowerWeight n : ℂ) *
      (k (Real.log n) + k (-Real.log n))).re at h
  rw [h]
  calc
    _ = ∑' n : ℕ, 2 * (primePowerWeight n * (k (Real.log n)).re) := by
      apply tsum_congr
      intro n
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, heven]
      ring
    _ = _ := tsum_mul_left

theorem integrable_pole_test {k : ℝ → ℂ} (hk : SuperexponentialDecay k)
    (hkc : Continuous k) (a : ℝ) (ha : |a| ≤ 1) :
    Integrable (fun u : ℝ => k u * (Real.exp (a * u) : ℂ)) := by
  have hi := hk.integrable_weighted_norm hkc (a := 1) (by norm_num)
  apply hi.mono'
  · have hc : Continuous (fun u : ℝ => k u * (Real.exp (a * u) : ℂ)) := by fun_prop
    exact hc.aestronglyMeasurable
  · apply ae_of_all
    intro u
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he : a * u ≤ |u| := by
      calc a * u ≤ |a * u| := le_abs_self _
        _ = |a| * |u| := abs_mul _ _
        _ ≤ 1 * |u| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
        _ = _ := one_mul _
    calc ‖k u‖ * Real.exp (a * u) ≤ ‖k u‖ * Real.exp |u| :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (norm_nonneg _)
      _ = Real.exp (1 * |u|) * ‖k u‖ := by ring

theorem re_paperFT_pole_pair {k : ℝ → ℂ} (hk : SuperexponentialDecay k)
    (hkc : Continuous k) (heven : ∀ t, (k (-t)).re = (k t).re) :
    (Zeta23.paperFT k (Complex.I / 2) + Zeta23.paperFT k (-Complex.I / 2)).re =
      2 * (∫ t, weilPoleKernel t * (k t).re ∂positiveMeasure) := by
  have hp := integrable_pole_test hk hkc (1 / 2) (by norm_num)
  have hn := integrable_pole_test hk hkc (-(1 / 2)) (by norm_num)
  have hpm : Integrable (fun u : ℝ => k u * (weilPoleKernel u : ℂ)) := by
    apply (hp.add hn).congr
    apply ae_of_all
    intro u
    dsimp only [Pi.add_apply]
    unfold weilPoleKernel
    push_cast
    rw [show (1 / 2 : ℂ) * (u : ℂ) = (u : ℂ) / 2 by ring,
      show (-(1 / 2) : ℂ) * (u : ℂ) = -(u : ℂ) / 2 by ring]
    ring
  have he1 (u : ℝ) : Complex.exp (Complex.I * (Complex.I / 2) * (u : ℂ)) =
      (Real.exp (-(1 / 2) * u) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have he2 (u : ℝ) : Complex.exp (Complex.I * (-Complex.I / 2) * (u : ℂ)) =
      (Real.exp ((1 / 2) * u) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hpoles : Zeta23.paperFT k (Complex.I / 2) + Zeta23.paperFT k (-Complex.I / 2) =
      ∫ u : ℝ, k u * (weilPoleKernel u : ℂ) := by
    unfold Zeta23.paperFT
    simp_rw [he1, he2]
    rw [← integral_add hn hp]
    apply integral_congr_ae
    apply ae_of_all
    intro u
    unfold weilPoleKernel
    push_cast
    rw [show (1 / 2 : ℂ) * (u : ℂ) = (u : ℂ) / 2 by ring,
      show (-(1 / 2) : ℂ) * (u : ℂ) = -(u : ℂ) / 2 by ring]
    ring
  have hR := Complex.reCLM.integral_comp_comm hpm
  change (∫ u, (k u * (weilPoleKernel u : ℂ)).re) =
    (∫ u, k u * (weilPoleKernel u : ℂ)).re at hR
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hR
  have hiR := Complex.reCLM.integrable_comp hpm
  change Integrable (fun u => (k u * (weilPoleKernel u : ℂ)).re) at hiR
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hiR
  have he (u : ℝ) : (k (-u)).re * weilPoleKernel (-u) = (k u).re * weilPoleKernel u := by
    rw [heven]
    unfold weilPoleKernel
    simp only [neg_neg]
    ring
  have hh := integral_eq_two_smul_Ioi_of_even _ hiR he
  simp only [smul_eq_mul] at hh
  rw [hpoles, ← hR, hh]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun t => mul_comm _ _)

/-- Exact equality of the source's literal arithmetic expression with the
project's actual full spatial arithmetic form. -/
theorem literatureRHS_re_eq_infinitePrimePowerCorrelationValue
    {k : ℝ → ℂ} (hk : SuperexponentialDecay k) (hkc : Continuous k)
    (hki : Integrable k) (hFk : Integrable (𝓕 k))
    (heven : ∀ t, (k (-t)).re = (k t).re)
    (hHc : Continuous (fun r : ℝ => Zeta23.paperFT k r))
    (A : ℝ) (hA : 0 ≤ A)
    (hdec : ∀ r : ℝ, ‖Zeta23.paperFT k r‖ ≤ A / (1 + r ^ 2))
    (K : ℝ) (hK : 0 ≤ K) (hLip : ∀ t, 0 < t → |(k t).re - (k 0).re| ≤ K * t) :
    (Zeta23.EF.literatureRHS k).re =
      infinitePrimePowerCorrelationValue
        (Real.eulerMascheroniConstant + Real.log (4 * Real.pi)) (fun t => (k t).re) := by
  change
    (Zeta23.paperFT k (Complex.I / 2) + Zeta23.paperFT k (-Complex.I / 2)).re -
      (∑' n : ℕ, (primePowerWeight n : ℂ) *
        (k (Real.log n) + k (-Real.log n))).re +
      ((1 / (2 * Real.pi) : ℂ) *
        (∫ r : ℝ, Zeta23.paperFT k r * (Zeta23.EF.gammaBracket r : ℂ))).re = _
  rw [re_paperFT_pole_pair hk hkc heven, re_paired_primePower_sum hk heven,
    re_integral_paperFT_gammaBracket_eq_regulated hkc hki hFk heven hHc A hA hdec K hK hLip]
  unfold infinitePrimePowerCorrelationValue
  ring

/-- The compact-test identification uses the proved unconditional explicit
formula for the actual nontrivial zeros and their actual analytic orders. -/
theorem actual_compact_Weil_explicit_formula
    {k : ℝ → ℂ} (hk : SuperexponentialDecay k) (hk2 : ContDiff ℝ 2 k)
    (hks : HasCompactSupport k) (hFk : Integrable (𝓕 k))
    (heven : ∀ t, (k (-t)).re = (k t).re)
    (hHc : Continuous (fun r : ℝ => Zeta23.paperFT k r))
    (A : ℝ) (hA : 0 ≤ A)
    (hdec : ∀ r : ℝ, ‖Zeta23.paperFT k r‖ ≤ A / (1 + r ^ 2))
    (K : ℝ) (hK : 0 ≤ K) (hLip : ∀ t, 0 < t → |(k t).re - (k 0).re| ≤ K * t) :
    (∑' ρ : Zeta23.zetaZeroConfig.carrier, (Zeta23.zetaZeroConfig.mult ρ : ℂ) *
      Zeta23.paperFT k (Zeta23.gammaOf ρ)).re =
      infinitePrimePowerCorrelationValue
        (Real.eulerMascheroniConstant + Real.log (4 * Real.pi)) (fun t => (k t).re) := by
  have h := (Zeta23.WeilEF.EF_lit_zetaZeroConfig k hk2 hks).2
  exact (congrArg Complex.re h).trans
    (literatureRHS_re_eq_infinitePrimePowerCorrelationValue hk hk2.continuous
      (hk2.continuous.integrable_of_hasCompactSupport hks) hFk heven hHc A hA hdec K hK hLip)

end
end RiemannResearch.RH.SignedWeilCorrelation
