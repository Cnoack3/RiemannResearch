import RiemannResearch.RH.CompactFrequencyMellinRigidity
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Fourier uniqueness for an integrable complex density

The proof reduces real signed densities to the characteristic-function
uniqueness theorem for finite positive measures in Mathlib, and obtains the
complex case by conjugation and real and imaginary parts. Compact support is
not required. Source: standard uniqueness of Fourier transforms of finite
measures; the positive-measure input is `Measure.ext_of_charFun`.
-/

noncomputable section
open MeasureTheory Filter Complex
open scoped ENNReal ComplexConjugate

namespace RiemannResearch.RH.Pareto.SpectralObstruction

private theorem integrable_mul_real_character (μ : Measure ℝ) (b : ℝ → ℂ)
    (hb : Integrable b μ) (x : ℝ) :
    Integrable (fun t => b t * exp ((x : ℂ) * (t : ℂ) * I)) μ := by
  refine hb.mul_bdd (c := 1) (by fun_prop) ?_
  filter_upwards [] with t
  simp [Complex.norm_exp]

private theorem charFun_withDensity_ofReal (μ : Measure ℝ) (f : ℝ → ℝ)
    (hf : Integrable f μ) (hf0 : ∀ t, 0 ≤ f t) (x : ℝ) :
    charFun (μ.withDensity (fun t => ENNReal.ofReal (f t))) x =
      ∫ t, (f t : ℂ) * exp ((x : ℂ) * (t : ℂ) * I) ∂μ := by
  rw [charFun_apply_real, integral_withDensity_eq_integral_toReal_smul₀
    hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards [] with t
  simp [ENNReal.toReal_ofReal (hf0 t), Complex.real_smul]

private theorem real_density_zero_of_character_integrals_zero
    (μ : Measure ℝ) (f : ℝ → ℝ) (hf : Integrable f μ)
    (hF : ∀ x : ℝ, ∫ t, (f t : ℂ) * exp ((x : ℂ) * (t : ℂ) * I) ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  let p : ℝ → ℝ := fun t => max (f t) 0
  let q : ℝ → ℝ := fun t => max (-f t) 0
  have hp : Integrable p μ := hf.pos_part
  have hq : Integrable q μ := hf.neg_part
  have hp0 : ∀ t, 0 ≤ p t := fun t => le_max_right _ _
  have hq0 : ∀ t, 0 ≤ q t := fun t => le_max_right _ _
  have hpf : ∫⁻ t, ENNReal.ofReal (p t) ∂μ ≠ ∞ :=
    ((hasFiniteIntegral_iff_ofReal (ae_of_all _ hp0)).mp hp.2).ne
  have hqf : ∫⁻ t, ENNReal.ofReal (q t) ∂μ ≠ ∞ :=
    ((hasFiniteIntegral_iff_ofReal (ae_of_all _ hq0)).mp hq.2).ne
  let νp := μ.withDensity (fun t => ENNReal.ofReal (p t))
  let νq := μ.withDensity (fun t => ENNReal.ofReal (q t))
  letI : IsFiniteMeasure νp := isFiniteMeasure_withDensity hpf
  letI : IsFiniteMeasure νq := isFiniteMeasure_withDensity hqf
  have hν : νp = νq := by
    apply Measure.ext_of_charFun
    funext x
    rw [show νp = μ.withDensity (fun t => ENNReal.ofReal (p t)) from rfl,
      show νq = μ.withDensity (fun t => ENNReal.ofReal (q t)) from rfl,
      charFun_withDensity_ofReal μ p hp hp0,
      charFun_withDensity_ofReal μ q hq hq0]
    apply sub_eq_zero.mp
    have hip : Integrable (fun t => (p t : ℂ) * exp ((x : ℂ) * (t : ℂ) * I)) μ :=
      integrable_mul_real_character μ (fun t => (p t : ℂ)) hp.ofReal x
    have hiq : Integrable (fun t => (q t : ℂ) * exp ((x : ℂ) * (t : ℂ) * I)) μ :=
      integrable_mul_real_character μ (fun t => (q t : ℂ)) hq.ofReal x
    calc
      _ = ∫ t, ((p t : ℂ) * exp ((x : ℂ) * (t : ℂ) * I) -
          (q t : ℂ) * exp ((x : ℂ) * (t : ℂ) * I)) ∂μ :=
        (integral_sub hip hiq).symm
      _ = ∫ t, (f t : ℂ) * exp ((x : ℂ) * (t : ℂ) * I) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [← sub_mul, ← Complex.ofReal_sub]
        congr 2
        exact max_zero_sub_max_neg_zero_eq_self (f t)
      _ = 0 := hF x
  have hpq : (fun t => ENNReal.ofReal (p t)) =ᵐ[μ]
      (fun t => ENNReal.ofReal (q t)) :=
    (withDensity_eq_iff hp.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      hq.aestronglyMeasurable.aemeasurable.ennreal_ofReal hpf).mp hν
  filter_upwards [hpq] with t ht
  have ht' : p t = q t := by
    simpa [ENNReal.toReal_ofReal (hp0 t), ENNReal.toReal_ofReal (hq0 t)]
      using congrArg ENNReal.toReal ht
  have hd : p t - q t = f t := max_zero_sub_max_neg_zero_eq_self (f t)
  simp_all

private theorem complex_density_re_zero_of_character_integrals_zero
    (μ : Measure ℝ) (b : ℝ → ℂ) (hb : Integrable b μ)
    (hF : ∀ x : ℝ, ∫ t, b t * exp ((x : ℂ) * (t : ℂ) * I) ∂μ = 0) :
    (fun t => (b t).re) =ᵐ[μ] 0 := by
  have hbc : Integrable (fun t => conj (b t)) μ :=
    (Complex.conjCLE.integrable_comp_iff).mpr hb
  have hcF : ∀ x : ℝ, ∫ t, conj (b t) * exp ((x : ℂ) * (t : ℂ) * I) ∂μ = 0 := by
    intro x
    calc
      _ = ∫ t, conj (b t * exp (((-x : ℝ) : ℂ) * (t : ℂ) * I)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with t
        simp [map_mul, ← Complex.exp_conj]
      _ = conj (∫ t, b t * exp (((-x : ℝ) : ℂ) * (t : ℂ) * I) ∂μ) :=
        integral_conj
      _ = 0 := by rw [hF]; simp
  apply real_density_zero_of_character_integrals_zero μ _ hb.re
  intro x
  calc
    _ = ∫ t, (b t * exp ((x : ℂ) * (t : ℂ) * I) +
        conj (b t) * exp ((x : ℂ) * (t : ℂ) * I)) / 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      change ((b t).re : ℂ) * exp ((x : ℂ) * (t : ℂ) * I) = _
      rw [Complex.re_eq_add_conj]
      ring
    _ = ((∫ t, b t * exp ((x : ℂ) * (t : ℂ) * I) ∂μ) +
        (∫ t, conj (b t) * exp ((x : ℂ) * (t : ℂ) * I) ∂μ)) / 2 := by
      rw [integral_div, integral_add (integrable_mul_real_character μ b hb x)
        (integrable_mul_real_character μ _ hbc x)]
    _ = 0 := by rw [hF, hcF]; simp

/-- Fourier uniqueness for every integrable complex density, without a compact
support or positivity assumption on that density. -/
theorem densityFourier_zero_implies_density_zero (μ : Measure ℝ) (b : ℝ → ℂ)
    (hb : Integrable b μ)
    (hF : ∀ x : ℝ, densityFourier μ b x = 0) : b =ᵐ[μ] 0 := by
  have hchar : ∀ x : ℝ, ∫ t, b t * exp ((x : ℂ) * (t : ℂ) * I) ∂μ = 0 := by
    intro x
    convert hF (-x) using 1
    unfold densityFourier
    apply integral_congr_ae
    filter_upwards [] with t
    congr 2
    push_cast
    ring
  have hre := complex_density_re_zero_of_character_integrals_zero μ b hb hchar
  have him := complex_density_re_zero_of_character_integrals_zero μ
    (fun t => -I * b t) (hb.const_mul (-I)) (by
      intro x
      calc
        _ = -I * (∫ t, b t * exp ((x : ℂ) * (t : ℂ) * I) ∂μ) := by
          simp only [mul_assoc, integral_const_mul]
        _ = 0 := by rw [hchar]; simp)
  filter_upwards [hre, him] with t ht_re ht_im
  apply Complex.ext
  · simpa using ht_re
  · simpa using ht_im

/-- The formerly open weighted-Fourier provider follows from integrability. -/
theorem weightedFourierUniqueness_of_integrable (σ : ℝ) (μ : Measure ℝ)
    (a : ℝ → ℂ) (hb : Integrable (zetaWeightedDensity σ a) μ) :
    WeightedFourierUniqueness σ μ a :=
  densityFourier_zero_implies_density_zero μ _ hb

end RiemannResearch.RH.Pareto.SpectralObstruction
