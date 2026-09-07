import RiemannResearch.RH.WeilDigammaSeries
import RiemannResearch.RH.WeilExplicitFormula.WeilEF.FullLine

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Dominated convergence for the frequency and spatial gamma series

Both limits use the actual digamma and the actual regulated Weil kernel.
The frequency hypothesis is an ordinary absolute-integrability condition,
not a Fourier identity; the spatial domination is derived from the proved
Lipschitz gamma admissibility theorem.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.SignedWeilCorrelation

noncomputable section

def digammaIncrement (r : ℝ) : ℝ :=
  (Complex.digamma ((1 / 4 : ℂ) + Complex.I * (r / 2 : ℝ))).re -
    (Complex.digamma (1 / 4 : ℂ)).re

theorem digammaIncrement_eq_tsum (r : ℝ) :
    digammaIncrement r = ∑' n : ℕ, digammaIncrementTerm (1 / 4) (r / 2) n := by
  simpa only [digammaIncrement, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] using
    re_digamma_sub_eq_tsum (a := 1 / 4) (by norm_num) (by norm_num) (r / 2)

theorem digammaIncrement_nonneg (r : ℝ) : 0 ≤ digammaIncrement r := by
  rw [digammaIncrement_eq_tsum]
  exact tsum_nonneg (fun n => digammaIncrementTerm_nonneg (by norm_num) _ n)

/-- The domination required by the gamma series follows from ordinary
quadratic Fourier decay, using the proved growth of the actual Gamma factor. -/
theorem integrable_mul_digammaIncrement_of_decay
    (H : ℝ → ℂ) (hH : Continuous H) (hHi : Integrable H)
    (A : ℝ) (hA : 0 ≤ A) (hdec : ∀ r, ‖H r‖ ≤ A / (1 + r ^ 2)) :
    Integrable (fun r => H r * (digammaIncrement r : ℂ)) := by
  have hp : Integrable (fun r : ℝ =>
      H r * logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + r * Complex.I)) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      Zeta23.WeilEF.integrable_mul_logDeriv_Gammaℝ_of_decay hH hA hdec
        (σ := 1 / 2) (by norm_num) (by norm_num)
  have hn0 := Zeta23.WeilEF.integrable_mul_logDeriv_Gammaℝ_of_decay
    (hH.comp continuous_neg) hA
    (fun r => by simpa only [Function.comp_def, neg_sq] using hdec (-r))
    (σ := 1 / 2) (by norm_num) (by norm_num)
  have hn : Integrable (fun r : ℝ =>
      H r * logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) - r * Complex.I)) := by
    simpa only [Function.comp_def, neg_neg, Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hn0.comp_neg
  have hiΓ : Integrable (fun r : ℝ => H r *
      (((Complex.digamma ((1 / 4 : ℂ) + (r : ℂ) / 2 * Complex.I)).re -
        Real.log Real.pi : ℝ) : ℂ)) := by
    apply (hp.add hn).congr
    apply ae_of_all
    intro r
    dsimp only [Pi.add_apply]
    rw [← mul_add, Zeta23.WeilEF.gammaR_bracket]
  have hi := hiΓ.sub (hHi.mul_const
    (((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi : ℝ) : ℂ))
  have he (r : ℝ) :
      H r * (((Complex.digamma ((1 / 4 : ℂ) + (r : ℂ) / 2 * Complex.I)).re -
        Real.log Real.pi : ℝ) : ℂ) -
      H r * (((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi : ℝ) : ℂ) =
      H r * (digammaIncrement r : ℂ) := by
    have harg : (1 / 4 : ℂ) + (r : ℂ) / 2 * Complex.I =
        (1 / 4 : ℂ) + Complex.I * (r / 2 : ℝ) := by push_cast; ring
    rw [harg]
    unfold digammaIncrement
    push_cast
    ring
  apply hi.congr
  apply ae_of_all
  intro r
  dsimp only [Pi.sub_apply]
  exact he r

theorem integrable_norm_mul_digammaIncrement_of_decay
    (H : ℝ → ℂ) (hH : Continuous H) (hHi : Integrable H)
    (A : ℝ) (hA : 0 ≤ A) (hdec : ∀ r, ‖H r‖ ≤ A / (1 + r ^ 2)) :
    Integrable (fun r => ‖H r‖ * digammaIncrement r) := by
  apply (integrable_mul_digammaIncrement_of_decay H hH hHi A hA hdec).norm.congr
  apply ae_of_all
  intro r
  change ‖H r * (digammaIncrement r : ℂ)‖ = ‖H r‖ * digammaIncrement r
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (digammaIncrement_nonneg r)]

theorem tendsto_integral_digammaIncrement_partial_sums
    (H : ℝ → ℂ) (hH : Continuous H)
    (hi : Integrable (fun r => ‖H r‖ * digammaIncrement r)) :
    Tendsto (fun N : ℕ => ∫ r : ℝ, H r *
      ((∑ n ∈ Finset.range N, digammaIncrementTerm (1 / 4) (r / 2) n : ℝ) : ℂ))
      atTop (𝓝 (∫ r : ℝ, H r * (digammaIncrement r : ℂ))) := by
  apply tendsto_integral_of_dominated_convergence
    (bound := fun r => ‖H r‖ * digammaIncrement r)
  · intro N
    have hm : Measurable (fun r : ℝ =>
        ((∑ n ∈ Finset.range N, digammaIncrementTerm (1 / 4) (r / 2) n : ℝ) : ℂ)) := by
      unfold digammaIncrementTerm
      fun_prop
    exact hH.aestronglyMeasurable.mul hm.aestronglyMeasurable
  · exact hi
  · intro N
    apply ae_of_all
    intro r
    have hsum0 : 0 ≤ ∑ n ∈ Finset.range N,
        digammaIncrementTerm (1 / 4) (r / 2) n :=
      Finset.sum_nonneg (fun n _ => digammaIncrementTerm_nonneg (by norm_num) _ n)
    have hsum : (∑ n ∈ Finset.range N, digammaIncrementTerm (1 / 4) (r / 2) n) ≤
        digammaIncrement r := by
      rw [digammaIncrement_eq_tsum]
      exact (summable_digammaIncrementTerm (a := 1 / 4) (by norm_num) (by norm_num) _).sum_le_tsum
        _ (fun n _ => digammaIncrementTerm_nonneg (by norm_num) _ n)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsum0]
    exact mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
  · apply ae_of_all
    intro r
    have ht := (summable_digammaIncrementTerm (a := 1 / 4)
      (by norm_num) (by norm_num) (r / 2)).hasSum.tendsto_sum_nat
    rw [← digammaIncrement_eq_tsum] at ht
    exact ((Complex.continuous_ofReal.tendsto _).comp ht).const_mul (H r)

theorem tendsto_integral_weilGammaKernel_partial_sums
    (C : ℝ → ℝ) (hCc : Continuous C) (K : ℝ) (hK : 0 ≤ K)
    (hLip : ∀ t, 0 < t → |C t - C 0| ≤ K * t) :
    Tendsto (fun N : ℕ => ∫ t,
      (∑ n ∈ Finset.range N, Real.exp (-(2 * (n : ℝ) + 1 / 2) * t)) *
        (C 0 - C t) ∂positiveMeasure) atTop
      (𝓝 (∫ t, weilGammaKernel t * (C 0 - C t) ∂positiveMeasure)) := by
  have hi : Integrable (fun t => weilGammaKernel t * |C 0 - C t|) positiveMeasure := by
    apply (integrable_weilGammaKernel_sub_zero C hCc K hK hLip).norm.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (weilGammaKernel_nonneg ht), abs_sub_comm]
  apply tendsto_integral_of_dominated_convergence
    (bound := fun t => weilGammaKernel t * |C 0 - C t|)
  · intro N
    have hc : Continuous (fun t : ℝ =>
        (∑ n ∈ Finset.range N, Real.exp (-(2 * (n : ℝ) + 1 / 2) * t)) *
          (C 0 - C t)) := by fun_prop
    exact hc.aestronglyMeasurable
  · exact hi
  · intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hsum0 : 0 ≤ ∑ n ∈ Finset.range N, Real.exp (-(2 * (n : ℝ) + 1 / 2) * t) :=
      Finset.sum_nonneg (fun n _ => Real.exp_nonneg _)
    have hsum : (∑ n ∈ Finset.range N, Real.exp (-(2 * (n : ℝ) + 1 / 2) * t)) ≤
        weilGammaKernel t := by
      rw [← (hasSum_weilGammaKernel ht).tsum_eq]
      exact (hasSum_weilGammaKernel ht).summable.sum_le_tsum _
        (fun n _ => Real.exp_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsum0]
    exact mul_le_mul_of_nonneg_right hsum (abs_nonneg _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hasSum_weilGammaKernel ht).tendsto_sum_nat.mul_const (C 0 - C t)

theorem integrable_weilGammaKernel_summand_displacement
    (C : ℝ → ℝ) (hCc : Continuous C) (K : ℝ) (hK : 0 ≤ K)
    (hLip : ∀ t, 0 < t → |C t - C 0| ≤ K * t) (n : ℕ) :
    Integrable (fun t => Real.exp (-(2 * (n : ℝ) + 1 / 2) * t) *
      (C 0 - C t)) positiveMeasure := by
  have hi : Integrable (fun t => weilGammaKernel t * |C 0 - C t|) positiveMeasure := by
    apply (integrable_weilGammaKernel_sub_zero C hCc K hK hLip).norm.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (weilGammaKernel_nonneg ht), abs_sub_comm]
  apply hi.mono'
  · have hc : Continuous (fun t => Real.exp (-(2 * (n : ℝ) + 1 / 2) * t) *
        (C 0 - C t)) := by fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hs := hasSum_weilGammaKernel ht
    have hbound := hs.summable.sum_le_tsum ({n} : Finset ℕ)
      (fun j _ => Real.exp_nonneg (-(2 * (j : ℝ) + 1 / 2) * t))
    simp only [Finset.sum_singleton, hs.tsum_eq] at hbound
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right hbound (abs_nonneg _)

end
end RiemannResearch.RH.SignedWeilCorrelation
