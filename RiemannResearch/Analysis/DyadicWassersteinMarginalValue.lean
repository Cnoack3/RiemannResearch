import RiemannResearch.Analysis.DyadicWassersteinMarginalOptimality
import RiemannResearch.Analysis.DyadicPrimeTentConstants
import RiemannResearch.Analysis.CircleFejerTent
import RiemannResearch.Analysis.PrimeTorusHaarSpecialization

/-! # Evaluation of the sharp one-prime signed marginal constant

This calculation pairs the uniformly convergent geometric Poisson series with
the periodic tent. The zero-mode cancellation is exact. Only odd positive
frequencies contribute and the positive and negative frequencies both occur.
-/

noncomputable section

open MeasureTheory
open scoped Topology ComplexConjugate BigOperators

namespace RiemannResearch.Analysis.DyadicZeroWasserstein
open PoissonHaar

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

private def weightedTent : CircleFunction :=
  ⟨fun z => (‖z‖ : ℂ), Complex.continuous_ofReal.comp continuous_norm⟩

private def tentPairing : CircleFunction →L[ℝ] ℝ :=
  Complex.reCLM.comp ((haarIntegralCLM.comp
    ((ContinuousLinearMap.mul ℂ CircleFunction) weightedTent)).restrictScalars ℝ)

private theorem tentPairing_apply (v : CircleFunction) :
    tentPairing v = ∫ z : CircleSpace, ‖z‖ * (v z).re ∂AddCircle.haarAddCircle := by
  have hi : Integrable (weightedTent * v) AddCircle.haarAddCircle :=
    (weightedTent * v).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ z : CircleSpace, (weightedTent * v) z ∂AddCircle.haarAddCircle).re = _
  calc
    _ = ∫ z : CircleSpace, ((weightedTent * v) z).re ∂AddCircle.haarAddCircle := (integral_re hi).symm
    _ = _ := by simp [weightedTent, Complex.mul_re]

/-- The power series identity in the space of continuous circle functions,
so evaluation by the bounded signed pairing can be interchanged with the sum. -/
private theorem poisson_centered_hasSum {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => poissonRatio r 1 ^ (n + 1) + poissonRatio r (-1) ^ (n + 1))
      (poissonKernel r - 1) := by
  have h (k : ℤ) := poissonRatio_summable r k hr hr1
  have hs (k : ℤ) : HasSum (fun n : ℕ => poissonRatio r k ^ (n + 1))
      ((∑' n : ℕ, poissonRatio r k ^ n) - 1) := by
    have htail := (summable_nat_add_iff 1).2 (h k)
    have hsplit := (h k).sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one, pow_zero] at hsplit
    rw [← hsplit, add_sub_cancel_left]
    exact htail.hasSum
  convert (hs 1).add (hs (-1)) using 1
  unfold poissonKernel
  abel

/-- Evaluation from the tent's positive Fourier cosine coefficients. -/
theorem tent_poisson_pairing_of_coefficients {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hcoeff : ∀ k : ℕ, 0 < k →
      (∫ z : CircleSpace, ‖z‖ * (fourier (k : ℤ) z).re ∂AddCircle.haarAddCircle) =
      ((-1 : ℝ)^k - 1) / (2 * Real.pi^2 * (k : ℝ)^2)) :
    (∫ z : CircleSpace, ‖z‖ * oneMinusPoisson r z ∂AddCircle.haarAddCircle) =
      (2 / Real.pi^2) * ∑' j : ℕ, r ^ (2*j+1) / ((2*j+1 : ℕ) : ℝ)^2 := by
  let term (n : ℕ) := tentPairing (poissonRatio r 1 ^ (n+1) + poissonRatio r (-1) ^ (n+1))
  have hs : HasSum term (tentPairing (poissonKernel r - 1)) :=
    tentPairing.hasSum (poisson_centered_hasSum hr hr1)
  have hterm (n : ℕ) :
      term n = 2 * r^(n+1) * (((-1:ℝ)^(n+1) - 1) /
        (2 * Real.pi^2 * ((n+1 : ℕ):ℝ)^2)) := by
    dsimp only [term]
    rw [tentPairing_apply, ← hcoeff (n+1) (by omega), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    simp only [poissonRatio_pow, mul_one, mul_neg_one, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, smul_eq_mul, fourier_neg, Complex.add_re]
    simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, zero_mul, sub_zero]
    ring
  have he : Summable (fun j : ℕ => term (2*j)) :=
    hs.summable.comp_injective (fun i j h => by omega)
  have ho : Summable (fun j : ℕ => term (2*j+1)) :=
    hs.summable.comp_injective (fun i j h => by omega)
  have hEven (j : ℕ) : term (2*j) =
      (-2 / Real.pi^2) * (r^(2*j+1) / ((2*j+1:ℕ):ℝ)^2) := by
    rw [hterm]
    have hz : (-1:ℝ)^(2*j+1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have hn : ((2*j+1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [hz]
    field_simp [Real.pi_ne_zero, hn]
    ring
  have hOdd (j : ℕ) : term (2*j+1) = 0 := by
    rw [hterm, show 2*j+1+1 = 2*(j+1) by omega]
    rw [pow_mul (-1 : ℝ)]
    norm_num
  have hv := (tsum_even_add_odd he ho).trans hs.tsum_eq
  simp_rw [hEven, hOdd] at hv
  rw [tsum_mul_left] at hv
  simp only [tsum_zero, add_zero] at hv
  have hneg : (∫ z : CircleSpace, ‖z‖ * oneMinusPoisson r z ∂AddCircle.haarAddCircle) =
      -tentPairing (poissonKernel r - 1) := by
    rw [tentPairing_apply, ← integral_neg]
    apply integral_congr_ae
    filter_upwards with z
    simp [oneMinusPoisson]
    ring
  rw [hneg, ← hv]
  ring

/-- The individual prime constant is the maximum over the entire 1-Lipschitz
unit ball of the signed marginal. The maximum is attained by distance to zero. -/
theorem isGreatest_prime_marginal_pairing {p : ℕ} (hp : p.Prime) :
    IsGreatest {a : ℝ | ∃ f : CircleSpace → ℝ, LipschitzWith 1 f ∧
      a = |Real.log p * ∫ z, f z * oneMinusPoisson (PrimeTorusHaar.primeRadius p) z
        ∂AddCircle.haarAddCircle|} (primeTentConstant p) := by
  let r := PrimeTorusHaar.primeRadius p
  have hr : 0 ≤ r := PrimeTorusHaar.primeRadius_nonneg p
  have hr1 : r < 1 := PrimeTorusHaar.primeRadius_lt_one hp
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hnorm : LipschitzWith 1 (fun z : CircleSpace => ‖z‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro z y
    simpa [Real.dist_eq, dist_eq_norm] using abs_norm_sub_norm_le z y
  have hval : Real.log p * (∫ z : CircleSpace, ‖z‖ * oneMinusPoisson r z
      ∂AddCircle.haarAddCircle) = primeTentConstant p := by
    rw [tent_poisson_pairing_of_coefficients hr hr1 (fun k hk => integral_tent_cosine hk)]
    unfold primeTentConstant
    dsimp [r, PrimeTorusHaar.primeRadius]
    ring
  have hn := abs_poisson_pairing_le_tent hr hr1 _ hnorm
  have hpos : 0 ≤ ∫ z : CircleSpace, ‖z‖ * oneMinusPoisson r z ∂AddCircle.haarAddCircle :=
    (abs_nonneg _).trans hn
  constructor
  · exact ⟨_, hnorm, by rw [abs_of_nonneg (mul_nonneg hl hpos), hval]⟩
  · rintro a ⟨f, hf, rfl⟩
    rw [abs_mul, abs_of_nonneg hl, ← hval]
    exact mul_le_mul_of_nonneg_left (abs_poisson_pairing_le_tent hr hr1 f hf) hl

end RiemannResearch.Analysis.DyadicZeroWasserstein
