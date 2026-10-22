import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Exponential moments determine measures and polynomial annihilators

Source: the classical analytic-moment proof of determinacy; this implementation
uses Mathlib's analytic moment-generating functions and characteristic-function
uniqueness. The final theorem supplies the analytic completeness step for the
ordinary Laguerre system in the RH Pareto Parseval application.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace MeasureTheory.Measure

/-- Finite measures with an exponential moment around zero are determined by
their ordinary moments. Both exponential-integrability hypotheses are explicit. -/
theorem eq_of_integral_pow_eq_of_exponential_moments
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : 0 ∈ interior (integrableExpSet id μ))
    (hν : 0 ∈ interior (integrableExpSet id ν))
    (hm : ∀ n : ℕ, (∫ x, x ^ n ∂μ) = ∫ x, x ^ n ∂ν) :
    μ = ν := by
  have hpμ := hasFPowerSeriesAt_mgf hμ
  have hpν := hasFPowerSeriesAt_mgf hν
  simp only [id_eq, zero_mul, Real.exp_zero, mul_one] at hpμ hpν
  simp_rw [hm] at hpμ
  have hgerm : mgf id μ =ᶠ[𝓝 0] mgf id ν := by
    filter_upwards [hpμ.eventually_hasSum_sub, hpν.eventually_hasSum_sub]
      with t htμ htν using htμ.unique htν
  let U : Set ℂ :=
    {z | z.re ∈ interior (integrableExpSet id μ) ∩
      interior (integrableExpSet id ν)}
  have haμ : AnalyticOnNhd ℂ (complexMGF id μ) U := by
    intro z hz
    exact analyticAt_complexMGF hz.1
  have haν : AnalyticOnNhd ℂ (complexMGF id ν) U := by
    intro z hz
    exact analyticAt_complexMGF hz.2
  have hc : IsPreconnected U :=
    ((convex_integrableExpSet (X := id) (μ := μ)).interior.inter
      (convex_integrableExpSet (X := id) (μ := ν)).interior).linear_preimage
        Complex.reLm |>.isPreconnected
  have h0 : (0 : ℂ) ∈ U := by simpa [U] using And.intro hμ hν
  have hfreqReal : ∃ᶠ t : ℝ in 𝓝[≠] 0,
      complexMGF id μ t = complexMGF id ν t := by
    apply Filter.Eventually.frequently
    filter_upwards [hgerm.filter_mono nhdsWithin_le_nhds] with t ht
    simpa only [complexMGF_ofReal] using congrArg Complex.ofReal ht
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] 0,
      complexMGF id μ z = complexMGF id ν z := by
    rw [frequently_iff_seq_forall] at hfreqReal ⊢
    obtain ⟨xs, hxs, heq⟩ := hfreqReal
    refine ⟨fun n ↦ (xs n : ℂ), ?_, heq⟩
    rw [tendsto_nhdsWithin_iff] at hxs ⊢
    constructor
    · simpa only [Function.comp_def, Complex.ofReal_zero] using
        (Complex.continuous_ofReal.tendsto 0).comp hxs.1
    · simpa using hxs.2
  have heq : EqOn (complexMGF id μ) (complexMGF id ν) U :=
    AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq haμ haν hc h0 hfreq
  apply Measure.ext_of_charFun
  funext t
  rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
  exact heq (by simpa [U] using And.intro hμ hν)

end MeasureTheory.Measure

namespace RiemannResearch.Analysis

/-- A square-integrable function orthogonal to every polynomial vanishes when
the measure has square-integrable exponentials on a neighborhood of zero. -/
theorem ae_eq_zero_of_polynomial_moments
    {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : MemLp f 2 μ)
    (hp : ∀ n : ℕ, MemLp (fun x : ℝ ↦ x ^ n) 2 μ)
    (he : ∀ s ∈ Ioo (-1 / 4 : ℝ) (1 / 4),
      MemLp (fun x : ℝ ↦ Real.exp (s * x)) 2 μ)
    (hm : ∀ n : ℕ, (∫ x, f x * x ^ n ∂μ) = 0) :
    f =ᵐ[μ] 0 := by
  let a : ℝ → ℝ := fun x ↦ ‖f x‖ + f x
  let b : ℝ → ℝ := fun x ↦ ‖f x‖
  have ha : MemLp a 2 μ := hf.norm.add hf
  have hb : MemLp b 2 μ := hf.norm
  have ha0 : ∀ x, 0 ≤ a x := by
    intro x
    change 0 ≤ |f x| + f x
    have := neg_abs_le (f x)
    linarith
  have hb0 : ∀ x, 0 ≤ b x := fun x ↦ norm_nonneg _
  have hai : Integrable a μ := ha.integrable (by norm_num)
  have hbi : Integrable b μ := hb.integrable (by norm_num)
  let μa := μ.withDensity (fun x ↦ ENNReal.ofReal (a x))
  let μb := μ.withDensity (fun x ↦ ENNReal.ofReal (b x))
  have hfa : (∫⁻ x, ENNReal.ofReal (a x) ∂μ) ≠ ∞ :=
    ((hasFiniteIntegral_iff_ofReal (ae_of_all _ ha0)).mp hai.2).ne
  have hfb : (∫⁻ x, ENNReal.ofReal (b x) ∂μ) ≠ ∞ :=
    ((hasFiniteIntegral_iff_ofReal (ae_of_all _ hb0)).mp hbi.2).ne
  let : IsFiniteMeasure μa := isFiniteMeasure_withDensity hfa
  let : IsFiniteMeasure μb := isFiniteMeasure_withDensity hfb
  have htransfer (w : ℝ → ℝ) (hw : MemLp w 2 μ)
      (hw0 : ∀ x, 0 ≤ w x) :
      0 ∈ interior (integrableExpSet id
        (μ.withDensity (fun x ↦ ENNReal.ofReal (w x)))) := by
    rw [mem_interior_iff_mem_nhds]
    apply Filter.mem_of_superset (Ioo_mem_nhds (by norm_num : (-1 / 4 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1 / 4))
    intro s hs
    change Integrable (fun x ↦ Real.exp (s * x)) _
    rw [integrable_withDensity_iff_integrable_smul₀'
      hw.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (ae_of_all _ (fun x ↦ ENNReal.ofReal_lt_top))]
    simpa only [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul, Pi.mul_def] using
      hw.integrable_mul (he s hs)
  have hmoment : ∀ n : ℕ, (∫ x, x ^ n ∂μa) = ∫ x, x ^ n ∂μb := by
    intro n
    change (∫ x, x ^ n ∂μ.withDensity (fun x ↦ ENNReal.ofReal (a x))) =
      ∫ x, x ^ n ∂μ.withDensity (fun x ↦ ENNReal.ofReal (b x))
    rw [integral_withDensity_eq_integral_toReal_smul₀
        ha.aestronglyMeasurable.aemeasurable.ennreal_ofReal
        (ae_of_all _ (fun x ↦ ENNReal.ofReal_lt_top)),
      integral_withDensity_eq_integral_toReal_smul₀
        hb.aestronglyMeasurable.aemeasurable.ennreal_ofReal
        (ae_of_all _ (fun x ↦ ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (ha0 _), ENNReal.toReal_ofReal (hb0 _),
      smul_eq_mul]
    simp only [a, b, add_mul]
    have hbn : Integrable (fun x ↦ ‖f x‖ * x ^ n) μ := by
      simpa only [Pi.mul_def, b] using hb.integrable_mul (hp n)
    have hfn : Integrable (fun x ↦ f x * x ^ n) μ := by
      simpa only [Pi.mul_def] using hf.integrable_mul (hp n)
    rw [integral_add hbn hfn, hm n, add_zero]
  have hab : μa = μb :=
    Measure.eq_of_integral_pow_eq_of_exponential_moments
      (htransfer a ha ha0) (htransfer b hb hb0) hmoment
  have hae := (withDensity_eq_iff
    ha.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    hb.aestronglyMeasurable.aemeasurable.ennreal_ofReal hfa).mp hab
  filter_upwards [hae] with x hx
  have hx' := congrArg ENNReal.toReal hx
  simp only [ENNReal.toReal_ofReal (ha0 x), ENNReal.toReal_ofReal (hb0 x)] at hx'
  dsimp [a, b] at hx'
  change f x = 0
  linarith

end RiemannResearch.Analysis
