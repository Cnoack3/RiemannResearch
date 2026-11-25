import RiemannResearch.Analysis.MontgomeryResolventHeatEvaluation
import RiemannResearch.Analysis.MontgomeryResolventPrimeTerms

/-! # Absolute heat-time exchange for the two von Mangoldt series -/

noncomputable section
open MeasureTheory Complex Set Filter
open scoped ArithmeticFunction
namespace RiemannResearch.Analysis.MontgomeryResolventPrimeMixture
open MontgomeryResolventWeilTest MontgomeryResolventHeatFamily MontgomeryResolventHeatEvaluation
open MontgomeryResolventPrimeTerms MontgomeryPrimeCrossIntegral GaussianLaplaceBridge

def primeTerm (k : ℝ → ℂ) (n : ℕ) : ℂ :=
  ((Λ n / Real.sqrt n : ℝ) : ℂ)*(k (Real.log n)+k (-Real.log n))

private theorem primeTerm_heat_integrable (u t : ℝ) (n : ℕ) :
    IntegrableOn (fun v : ℝ => primeTerm (heatGaussian u t v) n) (Ioi 0) :=
  ((heatGaussian_spatial_integrable u t (Real.log n)).add
    (heatGaussian_spatial_integrable u t (-Real.log n))).const_mul _

private theorem primeTerm_heat_integral (u t : ℝ) (n : ℕ) :
    (∫ v : ℝ in Ioi 0, primeTerm (heatGaussian u t v) n) = primeTerm (cutoffTest u t) n := by
  simp only [primeTerm,integral_const_mul,integral_add
    (heatGaussian_spatial_integrable u t (Real.log n)) (heatGaussian_spatial_integrable u t (-Real.log n)),
    integral_heatGaussian]

private theorem primeTerm_heat_norm_le {u : ℝ} (hu : 0 ≤ u) (t : ℝ) (n : ℕ) :
    (∫ v : ℝ in Ioi 0, ‖primeTerm (heatGaussian u t v) n‖) ≤
      (Real.exp u+(Real.exp u)⁻¹)*mangoldtThreeHalves n := by
  let a := Λ n / Real.sqrt n
  have ha : 0 ≤ a := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have he : a*(Real.exp (-|Real.log n-u|)+Real.exp (-|-(Real.log n)-u|)) =
      primeWeight (Real.exp u) n + mangoldtThreeHalves n/Real.exp u := by
    apply Complex.ofReal_injective
    simpa only [a,cutoffTest,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_zero,
      neg_zero,zero_mul,Complex.exp_zero,mul_one,one_mul] using cutoffTest_prime_terms hu 0 n
  have hbound : ∀ v : ℝ, ‖primeTerm (heatGaussian u t v) n‖ ≤
      a*(‖heatGaussian u t v (Real.log n)‖+‖heatGaussian u t v (-Real.log n)‖) := by
    intro v
    change ‖(a:ℂ)*_‖ ≤ _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) ha
  calc
    _ ≤ ∫ v : ℝ in Ioi 0, a*(‖heatGaussian u t v (Real.log n)‖+‖heatGaussian u t v (-Real.log n)‖) :=
      integral_mono (primeTerm_heat_integrable u t n).norm
        (((heatGaussian_spatial_integrable u t _).norm.add (heatGaussian_spatial_integrable u t _).norm).const_mul a)
        hbound
    _ = primeWeight (Real.exp u) n + mangoldtThreeHalves n/Real.exp u := by
      rw [integral_const_mul,integral_add (heatGaussian_spatial_integrable u t _).norm
        (heatGaussian_spatial_integrable u t _).norm,integral_norm_heatGaussian,integral_norm_heatGaussian,he]
    _ ≤ _ := by
      linarith only [primeWeight_le_mangoldtThreeHalves (Real.exp_pos u) n,
        show mangoldtThreeHalves n/Real.exp u=(Real.exp u)⁻¹*mangoldtThreeHalves n by ring]

private theorem primeTerm_summable_heat_norm {u : ℝ} (hu : 0 ≤ u) (t : ℝ) :
    Summable (fun n : ℕ => ∫ v : ℝ in Ioi 0, ‖primeTerm (heatGaussian u t v) n‖) :=
  Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (primeTerm_heat_norm_le hu t) (summable_mangoldtThreeHalves.mul_left _)

theorem heat_prime_series_integrable {u : ℝ} (hu : 0 ≤ u) (t : ℝ) :
    IntegrableOn (fun v : ℝ => ∑' n : ℕ, primeTerm (heatGaussian u t v) n) (Ioi 0) :=
  complex_tsum_integrable_of_summable_integral_norm _ (primeTerm_heat_integrable u t)
    (primeTerm_summable_heat_norm hu t)

theorem integral_heat_prime_series {u : ℝ} (hu : 0 ≤ u) (t : ℝ) :
    (∫ v : ℝ in Ioi 0, ∑' n : ℕ, primeTerm (heatGaussian u t v) n) =
      ∑' n : ℕ, primeTerm (cutoffTest u t) n := by
  rw [← integral_tsum_of_summable_integral_norm (primeTerm_heat_integrable u t)
    (primeTerm_summable_heat_norm hu t)]
  exact tsum_congr (primeTerm_heat_integral u t)

end RiemannResearch.Analysis.MontgomeryResolventPrimeMixture

namespace RiemannResearch.Analysis.MontgomeryResolventPrimeMixture

/--
info: 'RiemannResearch.Analysis.MontgomeryResolventPrimeMixture.heat_prime_series_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms heat_prime_series_integrable

end RiemannResearch.Analysis.MontgomeryResolventPrimeMixture

namespace RiemannResearch.Analysis.MontgomeryResolventPrimeMixture

/--
info: 'RiemannResearch.Analysis.MontgomeryResolventPrimeMixture.integral_heat_prime_series' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms integral_heat_prime_series

end RiemannResearch.Analysis.MontgomeryResolventPrimeMixture
