import RiemannResearch.Analysis.ActualPrimeTorusFMZRate
import RiemannResearch.Analysis.PrimeTorusHomogeneous
import RiemannResearch.Analysis.PrimeTorusMoments

/-!
# Actual homogeneous prime-torus Gram sampling

FMZ (Ford--Meng--Zaharescu), https://arxiv.org/abs/1511.06814,
gives the prime-phase sampling framework. The proved rational mode estimates
and homogeneous Parseval cancellation give an unconditional fixed-family
Gram asymptotic. The one-logarithm quantitative refinement uses Selberg density.
-/
noncomputable section
open Filter Zeta23
open scoped Topology BigOperators ComplexConjugate
namespace RiemannResearch.Analysis.ActualPrimeTorusFMZ
open ActualZeroOrdinate PrimePhaseTorus PrimeTorusHaar

/-- Zero-total-degree modes have no arithmetic axis correction. -/
theorem tendsto_centered_degree_zero_polynomial_div {ι : Type*}
    (P : Finset ℕ) (s : Finset ι) (a : ι → ℂ) (k : ι → ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime) (hk : ∀ i ∈ s, ∑ p : P, k i p = 0) :
    Tendsto (fun T : ℝ =>
      (sampleFunctional P T (polynomial P s a k) -
        (Ncount 0 T : ℂ) * haarIntegral (polynomial P s a k)) / (T : ℂ))
      atTop (𝓝 0) := by
  have h := tendsto_centered_polynomial_div P s a k hP
  have hm : (∑ i ∈ s, a i *
      rationalFMZMain (primeNumerator P (k i)) (primeDenominator P (k i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [prime_rationalFMZMain_eq_axisMultiplier P (k i) hP,
      axisMultiplier_eq_zero_of_sum_eq_zero _ _ _ (hk i hi), mul_zero]
  rwa [hm] at h

/-- Every fixed homogeneous Gram family has vanishing T-normalized
centered error. Multiplicities and all off-diagonal coefficients are retained. -/
theorem tendsto_centered_homogeneous_gram_div {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ) (d : ℤ)
    (hP : ∀ p ∈ P, p.Prime) (hk : ∀ i, ∑ p : P, k i p = d) :
    Tendsto (fun T : ℝ =>
      (sampleFunctional P T
        (polynomial P Finset.univ (fun ij : ι × ι => a ij.1 * star (a ij.2))
          (fun ij p => k ij.1 p - k ij.2 p)) -
        (Ncount 0 T : ℂ) * haarIntegral
        (polynomial P Finset.univ (fun ij : ι × ι => a ij.1 * star (a ij.2))
          (fun ij p => k ij.1 p - k ij.2 p))) / (T : ℂ))
      atTop (𝓝 0) := by
  apply tendsto_centered_degree_zero_polynomial_div P _ _ _ hP
  intro ij hij
  rw [Finset.sum_sub_distrib, hk, hk, sub_self]

/-- The polynomial used above is exactly the sampled squared modulus. -/
theorem homogeneous_gram_polynomial_eq {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ) :
    polynomial P Finset.univ (fun ij : ι × ι => a ij.1 * star (a ij.2))
      (fun ij p => k ij.1 p - k ij.2 p) =
      polynomial P Finset.univ a k * star (polynomial P Finset.univ a k) := by
  simp only [polynomial, Fintype.sum_prod_type, star_sum, star_smul,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul,
    character_mul_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp [mul_comm]
  rfl

/-- Uniform quantitative cancellation on degree-zero blocks. For a fixed
family, division by the zero count gives O((log T)^(-2)), using RvM.
The explicit Selberg premise is retained. -/
theorem eventually_degree_zero_polynomial_bound {ι : Type*} [Fintype ι]
    (hD : UniformSelbergDensity (1 / 4)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (P : Finset ℕ) (a : ι → ℂ) (k : ι → ℕ → ℤ),
      (∀ p ∈ P, p.Prime) → (∀ i, ∑ p : P, k i p = 0) →
      ‖(sampleFunctional P T (polynomial P Finset.univ a k) -
        (Ncount 0 T : ℂ) * haarIntegral (polynomial P Finset.univ a k)) / (T : ℂ)‖ ≤
        (C / Real.log T) * ∑ i, ‖a i‖ * primeModeWeight P (k i)^2 := by
  obtain ⟨C, hC, hb⟩ := eventually_fourierSeries_remainder_bound (ι := ι) hD
  refine ⟨C, hC, hb.mono ?_⟩
  intro T hT P a k hP hk
  have hs : fourierSeries a (fun i => fun p : P => k i p) =
      polynomial P Finset.univ a k := by
    simp [fourierSeries, polynomial, tsum_fintype]
  have hz : haarIntegral (polynomial P Finset.univ a k * primeDensity P) = 0 := by
    simp only [polynomial, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
      smul_eq_mul, haarIntegral_character_primeDensity P _ hP]
    apply Finset.sum_eq_zero
    intro i hi
    rw [prime_rationalFMZMain_eq_axisMultiplier P (k i) hP,
      axisMultiplier_eq_zero_of_sum_eq_zero _ _ _ (hk i), mul_zero]
  have hh := hT P a k hP ((hasSum_fintype _).summable)
  rw [hs, hz, sub_zero] at hh
  simpa only [Fourier.weightedFourierMass, tsum_fintype] using hh

end RiemannResearch.Analysis.ActualPrimeTorusFMZ
