import RiemannResearch.Analysis.ActualPrimeTorusFMZInterpolation
import RiemannResearch.Analysis.PrimeTorusMoments
import RiemannResearch.Analysis.ActualPrimeTorusFMZPoisson
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

/-!
# Mean-square Ford–Meng–Zaharescu discrepancies of translated prime-torus tests

The translations are integrated against product Haar measure. Orthogonality
gives a quadratic coefficient bound for the actual centered sampling error.
The one-mode estimates come from the repository's unconditional FMZ
interpolation. The prime-phase sampling framework is due to Ford, Meng
and Zaharescu (2017), https://doi.org/10.1112/blms.12001.
-/

noncomputable section
open Filter Zeta23
open scoped BigOperators ComplexConjugate Topology
namespace RiemannResearch.Analysis.ActualPrimeTorusFMZ
open ActualZeroOrdinate PrimePhaseTorus PrimeTorusHaar

/-- Height-normalized empirical sampling after Haar centering and subtraction
of the signed prime-density term. -/
def fmzErrorFunctional (P : Finset ℕ) (T : ℝ) :
    C(Torus P, ℂ) →ₗ[ℂ] ℂ where
  toFun f := (sampleFunctional P T f - (Ncount 0 T : ℂ) * haarIntegral f) / (T : ℂ) -
    haarIntegral (f * primeDensity P)
  map_add' f g := by simp only [map_add, mul_add, add_mul]; ring
  map_smul' z f := by simp only [map_smul, smul_mul_assoc, smul_eq_mul, RingHom.id_apply]; ring

/-- The discrepancy as a trigonometric polynomial in the translation variable. -/
def translatedFMZError {ι : Type*} [Fintype ι] (P : Finset ℕ) (T : ℝ)
    (a : ι → ℂ) (k : ι → ℕ → ℤ) : C(Torus P, ℂ) :=
  polynomial P Finset.univ
    (fun i => a i * fmzErrorFunctional P T (character (fun p : P => k i p))) k

theorem translatedFMZError_apply {ι : Type*} [Fintype ι] (P : Finset ℕ) (T : ℝ)
    (a : ι → ℂ) (k : ι → ℕ → ℤ) (z : Torus P) :
    translatedFMZError P T a k z = fmzErrorFunctional P T
      (polynomial P Finset.univ (fun i => a i * character (fun p : P => k i p) z) k) := by
  simp only [translatedFMZError, polynomial, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Parseval for the actual discrepancy; the distinctness is on the selected
prime coordinates. Equal characters can first have their coefficients added. -/
theorem translatedFMZError_parseval {ι : Type*} [Fintype ι] (P : Finset ℕ) (T : ℝ)
    (a : ι → ℂ) (k : ι → ℕ → ℤ)
    (hk : Function.Injective (fun i => fun p : P => k i p)) :
    (haarIntegral (translatedFMZError P T a k * star (translatedFMZError P T a k))).re =
      ∑ i, (‖a i‖ * ‖fmzErrorFunctional P T (character (fun p : P => k i p))‖)^2 := by
  classical
  unfold translatedFMZError polynomial
  rw [haarIntegral_finite_gram]
  simp only [hk.eq_iff, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mul, ← Complex.ofReal_sum,
    Complex.ofReal_re]

/-- Dimension-independent fractional estimates for the Haar mean square.
The coefficient square sum may change with the height and prime set. -/
theorem eventually_translatedFMZError_sq_le :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ 2 →
      ∀ (P : Finset ℕ) (ι : Type) [Fintype ι] (a : ι → ℂ) (k : ι → ℕ → ℤ),
      (∀ p ∈ P, p.Prime) → Function.Injective (fun i => fun p : P => k i p) →
      (haarIntegral (translatedFMZError P T a k * star (translatedFMZError P T a k))).re ≤
        (K * fmzWienerRate s T)^2 * ∑ i, (‖a i‖ * primeModeWeight P (k i)^s)^2 := by
  obtain ⟨K,hK,hb⟩ := eventually_centeredRationalOrdinate_fractional
  refine ⟨K,hK,hb.mono ?_⟩
  intro T hT s hs hs2 P ι _ a k hP hk
  rw [translatedFMZError_parseval P T a k hk, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  let n := primeNumerator P (k i)
  let m := primeDenominator P (k i)
  have hn : 1 ≤ n := primeProduct_pos _ _ hP
  have hm : 1 ≤ m := primeProduct_pos _ _ hP
  have hr : ‖fmzErrorFunctional P T (character (fun p : P => k i p))‖ ≤
      (K * fmzWienerRate s T) * primeModeWeight P (k i)^s := by
    change ‖(sampleFunctional P T _ - (Ncount 0 T : ℂ) * haarIntegral _) / (T : ℂ) -
      haarIntegral (character (fun p : P => k i p) * primeDensity P)‖ ≤ _
    rw [centered_character_eq_rational P (k i) hP, haarIntegral_character_primeDensity P (k i) hP]
    exact hT s hs hs2 n m hn hm
  have hh := mul_le_mul_of_nonneg_left hr (norm_nonneg (a i))
  calc
    _ ≤ (‖a i‖ * ((K * fmzWienerRate s T) * primeModeWeight P (k i)^s))^2 :=
      pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hh 2
    _ = _ := by ring

#print axioms eventually_translatedFMZError_sq_le
end RiemannResearch.Analysis.ActualPrimeTorusFMZ
