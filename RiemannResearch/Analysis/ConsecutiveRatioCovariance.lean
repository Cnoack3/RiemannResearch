import RiemannResearch.Analysis.ConsecutiveRatioOrbitLaw

/-! # Centered and gauged Parseval in the backward-ratio coordinates

A ratio word pulls back to a balanced word in the original prime phases.
Covariance subtracts the product of the two means. This removes the constant
mode, while unit phases preserve the squared coefficients. Modes are indexed
by their net integer exponents, so different presentations of one character
must be combined before applying the squared-coefficient formula.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped Topology BigOperators ComplexConjugate
namespace RiemannResearch.Analysis.ActualInfinitePrimeTorus
open CompactCharacter CompactGaugeOrbitLaw RatioChainHaar
open scoped RiemannResearch.Analysis.RatioChainHaar
local instance ratioCovarianceTorusMeasurable : MeasurableSpace PrimeTorus := borel PrimeTorus
local instance ratioCovarianceTorusBorel : BorelSpace PrimeTorus := ⟨rfl⟩
local instance ratioCovariancePairMeasurable : MeasurableSpace (PrimeTorus × PrimeTorus) := borel _
local instance ratioCovariancePairBorel : BorelSpace (PrimeTorus × PrimeTorus) := ⟨rfl⟩

abbrev RatioWord := List (ℕ × ℤ)

def pullRatioWord : RatioWord → PrimeWord
  | [] => []
  | (j,k)::w => (orderedPrime j,k)::(orderedPrime (j+1),-k)::pullRatioWord w

def ratioFrequency (s : RatioWord) : ℝ := wordFrequency (pullRatioWord s)

theorem character_primeRatios (s : RatioWord) (z : PrimeTorus) :
    character s (primeRatios z) = character (pullRatioWord s) z := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    rcases a with ⟨j,k⟩
    simp only [pullRatioWord, character, ContinuousMap.mul_apply, coordinatePower,
      ContinuousMap.coe_mk, primeRatios_apply, div_eq_mul_inv, mul_zpow, inv_zpow,
      zpow_neg, Circle.coe_mul, mul_assoc, ih]

theorem ratioWord_phase (s : RatioWord) (u : ℝ) :
    character s (primeRatios (phasePoint u)) = ZeroOrdinate.phase (ratioFrequency s) u := by
  rw [character_primeRatios, character_phasePoint]
  rfl

private theorem character_single_site (s : RatioWord) (i : ℕ) (z : Circle) :
    character s (fun j => if j = i then z else 1) = ((z ^ (wordExponents s i) : Circle) : ℂ) := by
  classical
  induction s with
  | nil => simp [wordExponents, character]
  | cons a s ih =>
    rcases a with ⟨j,k⟩
    by_cases h : j = i
    · subst j
      simp [character, coordinatePower, wordExponents, ih, zpow_add]
    · simp [character, coordinatePower, wordExponents, ih, h, Ne.symm h]

private theorem zpow_separates_zero (k : ℤ) (h : ∀ z : Circle, z^k = 1) : k = 0 := by
  by_contra hk
  have hR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have e := h (Circle.exp (Real.pi / (k:ℝ)))
  rw [← Circle.exp_intCast_mul, show (k:ℝ)*(Real.pi/(k:ℝ)) = Real.pi by field_simp] at e
  exact Circle.exp_pi_ne_one e

theorem exponents_eq_of_ratioFrequency_eq {s t : RatioWord}
    (h : ratioFrequency s = ratioFrequency t) : wordExponents s = wordExponents t := by
  have heq : (character s : Chain → ℂ) = (character t : Chain → ℂ) :=
    dense_primeRatio_orbit.equalizer (character s).continuous (character t).continuous
      (by funext u; change character s (primeRatios (phasePoint u)) =
            character t (primeRatios (phasePoint u)); rw [ratioWord_phase, ratioWord_phase, h])
  ext i
  apply sub_eq_zero.mp
  apply zpow_separates_zero
  intro z
  have he := congrFun heq (fun j => if j=i then z else 1)
  rw [character_single_site, character_single_site] at he
  have hz : z ^ (wordExponents s i) = z ^ (wordExponents t i) := Subtype.ext he
  rw [zpow_sub, hz]
  simp

theorem ratioFrequency_eq_iff_exponents (s t : RatioWord) :
    ratioFrequency s = ratioFrequency t ↔ wordExponents s = wordExponents t := by
  refine ⟨exponents_eq_of_ratioFrequency_eq, fun h => ?_⟩
  have he : character s = character t := by
    rw [← modeCharacter_wordExponents s, ← modeCharacter_wordExponents t, h]
  by_contra hd
  let u := Real.pi / (ratioFrequency s - ratioFrequency t)
  have hu : Circle.exp (ratioFrequency s * u) = Circle.exp (ratioFrequency t * u) := by
    apply Subtype.ext
    change ZeroOrdinate.phase (ratioFrequency s) u = ZeroOrdinate.phase (ratioFrequency t) u
    rw [← ratioWord_phase s u, ← ratioWord_phase t u, he]
  have hp : ratioFrequency s * u - ratioFrequency t * u = Real.pi := by
    rw [← sub_mul, mul_comm]; exact div_mul_cancel₀ _ (sub_ne_zero.mpr hd)
  apply Circle.exp_pi_ne_one
  rw [← hp, Circle.exp_sub, hu]
  simp

theorem ratio_word_covariance (s t : RatioWord) :
    (∫ z, pairWord (pullRatioWord s) ((pullRatioWord t).map fun a => (a.1,-a.2)) z ∂diagonalHaar) -
      (∫ z, pairWord (pullRatioWord s) [] z ∂diagonalHaar) *
      conj (∫ z, pairWord (pullRatioWord t) [] z ∂diagonalHaar) =
      (if ratioFrequency s = ratioFrequency t then (1:ℂ) else 0) -
      (if ratioFrequency s = 0 ∧ ratioFrequency t = 0 then 1 else 0) := by
  rw [diagonalHaar_pairWord, diagonalHaar_pairWord, diagonalHaar_pairWord, wordFrequency_neg]
  change (if ratioFrequency s + -ratioFrequency t = 0 then (1:ℂ) else 0) -
    (if ratioFrequency s + 0 = 0 then 1 else 0) *
      conj (if ratioFrequency t + 0 = 0 then 1 else 0) = _
  simp only [← sub_eq_add_neg, sub_eq_zero]
  by_cases hs : ratioFrequency s = 0 <;> by_cases ht : ratioFrequency t = 0 <;>
    simp [hs, ht]

/-- The constant coefficient has been subtracted; complex phases are arbitrary
of modulus one and the real normalization is retained explicitly. -/
theorem centered_ratio_gauge_parseval {ι : Type*} (w : ι → RatioWord)
    (hi : Function.Injective (fun i => wordExponents (w i)))
    (a η : ι → ℂ) (hη : ∀ i, ‖η i‖ = 1)
    (ha : Summable (fun i => ‖a i‖ ^ 2)) (c : ℝ) :
    let b := fun i => if ratioFrequency (w i) = 0 then (0:ℂ) else (c:ℂ)*η i*a i
    Summable (fun i => b i • pairWordL2 (pullRatioWord (w i)) []) ∧
    ‖∑' i, b i • pairWordL2 (pullRatioWord (w i)) []‖^2 =
      c^2 * ∑' i, if ratioFrequency (w i) = 0 then (0:ℝ) else ‖a i‖^2 := by
  intro b
  have he (i : ι) : ‖b i‖^2 =
      c^2 * (if ratioFrequency (w i) = 0 then (0:ℝ) else ‖a i‖^2) := by
    by_cases h : ratioFrequency (w i) = 0
    · simp [b,h]
    · simp [b,h,hη,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  have hm := ha.mul_left (c^2)
  have hb : Summable (fun i => ‖b i‖^2) := Summable.of_nonneg_of_le
    (fun i => sq_nonneg _) (fun i => by
      rw [he]
      split_ifs with h
      · exact mul_le_mul_of_nonneg_left (sq_nonneg _) (sq_nonneg _)
      · exact le_rfl) hm
  have hinj : Function.Injective (fun i => wordFrequency (pullRatioWord (w i) ++ [])) := by
    intro i j hij
    apply hi
    apply exponents_eq_of_ratioFrequency_eq
    simpa only [List.append_nil,ratioFrequency] using hij
  obtain ⟨hs, hnorm⟩ := diagonalHaar_parseval (fun i => pullRatioWord (w i)) (fun _ => []) hinj b hb
  refine ⟨hs, hnorm.trans ?_⟩
  simp_rw [he]
  exact tsum_mul_left ..

end RiemannResearch.Analysis.ActualInfinitePrimeTorus
