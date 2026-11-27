/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualInfinitePrimeTorus
import RiemannResearch.Analysis.ActualPrimeTorusFMZInterpolation
import RiemannResearch.Analysis.ActualSelbergTransitionWindow
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space

/-! # Countable FMZ Fourier sums in the diagonal prime Haar law

A word on each copy of the prime torus restricts to the concatenated word
on the diagonal. Orthogonality uses distinct frequencies after restriction.
The centered coefficients use actual positive-height zero occurrences.
[Ford, Meng and Zaharescu](https://arxiv.org/abs/1511.06814) establish the finite-dimensional
ordinate discrepancy. Here the repository's uniform rational multiplier bounds are applied to
square-summable modes using Mathlib's Hilbert-space Parseval synthesis.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace RiemannResearch.Analysis.ActualInfinitePrimeTorus
open ActualZeroOrdinate CompactCharacter CompactGaugeOrbitLaw

abbrev PrimeWord := List (Nat.Primes × ℤ)
local instance : MeasurableSpace PrimeTorus := borel PrimeTorus
local instance : BorelSpace PrimeTorus := ⟨rfl⟩
local instance : MeasurableSpace (PrimeTorus × PrimeTorus) := borel _
local instance : BorelSpace (PrimeTorus × PrimeTorus) := ⟨rfl⟩

/-- The unique one-point law with the finite product-Haar moments. -/
def primeHaar : ProbabilityMeasure PrimeTorus :=
  (existsUnique_actual_orbit_limit (0 : HilbertSpace)).exists.choose

theorem primeHaar_word (s : PrimeWord) : (∫ z, character s z ∂primeHaar) = haarMoment s :=
  (existsUnique_actual_orbit_limit (0 : HilbertSpace)).exists.choose_spec.1 s

theorem tendsto_primeHaar : Tendsto empiricalProbability atTop (𝓝 primeHaar) :=
  (existsUnique_actual_orbit_limit (0 : HilbertSpace)).exists.choose_spec.2.1

theorem wordFrequency_append (s t : PrimeWord) : wordFrequency (s++t) = wordFrequency s + wordFrequency t := by
  induction s with
  | nil => simp [wordFrequency]
  | cons a s ih => rcases a with ⟨p, k⟩; simp [wordFrequency, ih, add_assoc]

theorem wordFrequency_neg (s : PrimeWord) :
    wordFrequency (s.map fun a => (a.1, -a.2)) = -wordFrequency s := by
  induction s with
  | nil => simp [wordFrequency]
  | cons a s ih => rcases a with ⟨p, k⟩; simp [wordFrequency, ih]; ring

theorem haarMoment_frequency (s : PrimeWord) : haarMoment s = if wordFrequency s = 0 then 1 else 0 := by
  classical
  have hfreq : wordFrequency s = PrimePhaseTorus.primeFrequency (wordPrimes s) (wordMode s) :=
    wordFrequency_eq_sum s (wordPrimes s) (fun a ha => List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, ha, rfl⟩))
  have he := (ActualPrimeTorusFMZ.restrictedMode_eq_zero_iff (wordPrimes s) (wordMode s)).trans
    (PrimePhaseTorus.primeFrequency_eq_zero_iff _ _ (wordPrimes_prime s)).symm
  rw [haarMoment_eq, hfreq]
  by_cases h : PrimePhaseTorus.primeFrequency (wordPrimes s) (wordMode s) = 0
  · rw [if_pos (he.mpr h), if_pos h]
  · rw [if_neg (fun q => h (he.mp q)), if_neg h]


private theorem wordMode_outside (w : PrimeWord) (n : ℕ) (h : n ∉ wordPrimes w) :
    wordMode w n = 0 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨p, k⟩
    have hh : n ≠ ↑p ∧ n ∉ wordPrimes w := by simpa [wordPrimes] using h
    simp [wordMode, hh.1, ih hh.2]

private theorem wordExponents_apply (w : PrimeWord) (p : Nat.Primes) :
    wordExponents w p = wordMode w p := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨q, k⟩
    by_cases h : q = p
    · subst q; simp [wordMode, wordExponents, ih]
    · have h' : (p : ℕ) ≠ (q : ℕ) := fun e => h (Subtype.ext e.symm)
      simp [wordMode, wordExponents, Finsupp.single_apply, h, h', ih]

theorem character_one_of_frequency_zero (w : PrimeWord) (hw : wordFrequency w = 0) : character w = 1 := by
  have hfreq : wordFrequency w = PrimePhaseTorus.primeFrequency (wordPrimes w) (wordMode w) :=
    wordFrequency_eq_sum w _ (fun a ha => List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, ha, rfl⟩))
  rw [hfreq] at hw
  have hin := (PrimePhaseTorus.primeFrequency_eq_zero_iff _ _ (wordPrimes_prime w)).mp hw
  have hzero : wordExponents w = 0 := by
    ext p
    rw [wordExponents_apply]
    by_cases hp : (p : ℕ) ∈ wordPrimes w
    · exact hin _ hp
    · exact wordMode_outside w _ hp
  rw [← modeCharacter_wordExponents, hzero, modeCharacter_zero]

theorem character_mul_point (w : PrimeWord) (x y : PrimeTorus) :
    character w (x * y) = character w x * character w y := by
  induction w with
  | nil => simp [character]
  | cons a w ih =>
    rcases a with ⟨p, k⟩
    simp only [character, ContinuousMap.mul_apply, coordinatePower, ContinuousMap.coe_mk, Pi.mul_apply, mul_zpow,
      Circle.coe_mul, ih]
    ring

/-- The limiting probability is invariant under every prime-torus translation. -/
theorem primeHaar_translation (y : PrimeTorus) :
    primeHaar.map (continuous_const.mul continuous_id : Continuous (fun z : PrimeTorus => y * z)).measurable.aemeasurable =
      primeHaar := by
  apply ProbabilityMeasure.eq_of_dense_test_integrals character characters_dense
  intro w
  have hmeas : AEMeasurable (fun z : PrimeTorus => y * z) (primeHaar : Measure PrimeTorus) :=
    (continuous_const.mul continuous_id : Continuous (fun z : PrimeTorus => y * z)).measurable.aemeasurable
  rw [show (∫ z, character w z ∂primeHaar.map hmeas) = ∫ z, character w (y * z) ∂primeHaar from
    integral_map hmeas (character w).continuous.aestronglyMeasurable]
  simp_rw [character_mul_point]
  rw [integral_const_mul, primeHaar_word, haarMoment_frequency]
  by_cases hu : wordFrequency w = 0
  · simp [hu, character_one_of_frequency_zero w hu]
  · simp [hu]

def diagonalHaar : ProbabilityMeasure (PrimeTorus × PrimeTorus) :=
  primeHaar.map (continuous_id.prodMk continuous_id).measurable.aemeasurable

theorem diagonalHaar_integral (f : C(PrimeTorus × PrimeTorus, ℂ)) :
    (∫ x, f x ∂diagonalHaar) = ∫ z, f (z, z) ∂primeHaar :=
  integral_map (continuous_id.prodMk continuous_id).measurable.aemeasurable f.continuous.aestronglyMeasurable

def pairWord (s t : PrimeWord) : C(PrimeTorus × PrimeTorus, ℂ) :=
  ⟨fun x => character s x.1 * character t x.2,
    ((character s).continuous.comp continuous_fst).mul ((character t).continuous.comp continuous_snd)⟩

theorem pairWord_diagonal (s t : PrimeWord) (z : PrimeTorus) :
    pairWord s t (z, z) = character (s++t) z := by simp [pairWord]

theorem diagonalHaar_pairWord (s t : PrimeWord) :
    (∫ x, pairWord s t x ∂diagonalHaar) = if wordFrequency s + wordFrequency t = 0 then 1 else 0 := by
  rw [diagonalHaar_integral]
  simp_rw [pairWord_diagonal]
  rw [primeHaar_word, haarMoment_frequency, wordFrequency_append]

def pairWordL2 (s t : PrimeWord) : Lp ℂ 2 (diagonalHaar : Measure (PrimeTorus × PrimeTorus)) :=
  ContinuousMap.toLp 2 _ ℂ (pairWord s t)

/-- Distinct restricted prime frequencies are an orthonormal family on the diagonal. -/
theorem pairWordL2_orthonormal {ι : Type*} (s t : ι → PrimeWord)
    (hinj : Function.Injective (fun i => wordFrequency (s i ++ t i))) :
    Orthonormal ℂ (fun i => pairWordL2 (s i) (t i)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  let F := pairWord (s j) (t j) * star (pairWord (s i) (t i))
  change inner ℂ (ContinuousMap.toLp 2 _ ℂ _) (ContinuousMap.toLp 2 _ ℂ _) = _
  rw [ContinuousMap.inner_toLp]
  change (∫ x, F x ∂diagonalHaar) = _
  rw [diagonalHaar_integral]
  let wi := s i ++ t i
  let wj := s j ++ t j
  let w := wj ++ wi.map fun a => (a.1, -a.2)
  have hprod (z : PrimeTorus) : F (z, z) = character w z := by
    dsimp only [F, ContinuousMap.mul_apply, ContinuousMap.star_apply]
    rw [pairWord_diagonal, pairWord_diagonal]
    rw [show character w = character wj * star (character wi) by rw [star_character]; exact character_append _ _]
    rfl
  simp_rw [hprod]
  rw [primeHaar_word, haarMoment_frequency]
  have hw : wordFrequency w = wordFrequency wj - wordFrequency wi := by
    rw [show w = wj ++ wi.map (fun a => (a.1, -a.2)) by rfl, wordFrequency_append, wordFrequency_neg, sub_eq_add_neg]
  rw [hw]
  by_cases hij : i = j
  · subst j; simp [wi, wj]
  · rw [if_neg (fun h => hij (hinj (sub_eq_zero.mp h)).symm), if_neg hij]

/-- Countable Parseval synthesis. The series is unconditional in the L² norm. -/
theorem diagonalHaar_parseval {ι : Type*} (s t : ι → PrimeWord)
    (hinj : Function.Injective (fun i => wordFrequency (s i ++ t i))) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖ ^ 2)) :
    Summable (fun i => c i • pairWordL2 (s i) (t i)) ∧
      ‖∑' i, c i • pairWordL2 (s i) (t i)‖ ^ 2 = ∑' i, ‖c i‖ ^ 2 := by
  let h := (pairWordL2_orthonormal s t hinj).orthogonalFamily
  let x : lp (fun _ : ι => ℂ) 2 := ⟨c, (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2 (by simpa using hc)⟩
  constructor
  · exact h.summable_of_lp x
  · change ‖h.linearIsometry x‖ ^ 2 = _
    rw [LinearIsometry.norm_map]
    simpa [x] using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x

def wordNumerator (w : PrimeWord) := PrimePhaseTorus.primeNumerator (wordPrimes w) (wordMode w)
def wordDenominator (w : PrimeWord) := PrimePhaseTorus.primeDenominator (wordPrimes w) (wordMode w)
def wordWeight (w : PrimeWord) := rationalModeWeight (wordNumerator w) (wordDenominator w)
def wordRemainder (T : ℝ) (w : PrimeWord) :=
  centeredRationalOrdinate T (wordNumerator w) (wordDenominator w) / (T : ℂ) -
    rationalFMZMain (wordNumerator w) (wordDenominator w)

theorem wordNumerator_one_le (w : PrimeWord) : 1 ≤ wordNumerator w :=
  PrimePhaseTorus.primeProduct_pos _ _ (wordPrimes_prime w)
theorem wordDenominator_one_le (w : PrimeWord) : 1 ≤ wordDenominator w :=
  PrimePhaseTorus.primeProduct_pos _ _ (wordPrimes_prime w)

/-- The coefficient before subtracting the FMZ main term is the literal
centered, order - height - normalized zero sample on the diagonal. -/
theorem diagonal_centered_sample (s t : PrimeWord) (T : ℝ) :
    sum T (fun ρ => pairWord s t (phasePoint ρ.im, phasePoint ρ.im)) -
      (Ncount 0 T : ℂ) * (∫ x, pairWord s t x ∂diagonalHaar) =
      centeredRationalOrdinate T (wordNumerator (s++t)) (wordDenominator (s++t)) := by
  rw [diagonalHaar_integral]
  simp_rw [pairWord_diagonal]
  rw [primeHaar_word]
  simp_rw [character_phasePoint_eq_finite]
  exact ActualPrimeTorusFMZ.centered_character_eq_rational _ _ (wordPrimes_prime _) T

theorem tendsto_wordRemainder (w : PrimeWord) : Tendsto (fun T => wordRemainder T w) atTop (𝓝 0) := by
  simpa [wordRemainder] using
    (tendsto_centeredRationalOrdinate_div (wordNumerator_one_le w) (wordDenominator_one_le w)).sub_const
      (rationalFMZMain (wordNumerator w) (wordDenominator w))


/-- A coefficient envelope passes to the square-summed error, also when the
Fourier coefficients and their prime supports depend on the height. -/
theorem diagonal_fmz_sq_le_of_envelope {ι : Type*} (T : ℝ) (s t : ι → PrimeWord)
    (hinj : Function.Injective (fun i => wordFrequency (s i ++ t i))) (a : ι → ℂ)
    (W : ι → ℝ) (B : ℝ) (ha : Summable (fun i => (‖a i‖ * W i) ^ 2))
    (henv : ∀ i, ‖wordRemainder T (s i ++ t i)‖ ≤ B * W i) :
    Summable (fun i => (a i * wordRemainder T (s i ++ t i)) • pairWordL2 (s i) (t i)) ∧
    ‖∑' i, (a i * wordRemainder T (s i ++ t i)) • pairWordL2 (s i) (t i)‖ ^ 2 ≤
      B ^ 2 * ∑' i, (‖a i‖ * W i) ^ 2 := by
  let c := fun i => a i * wordRemainder T (s i ++ t i)
  have hbound (i : ι) : ‖c i‖ ^ 2 ≤ B ^ 2 * (‖a i‖ * W i) ^ 2 := by
    have hi : ‖c i‖ ≤ ‖a i‖ * (B * W i) := by
      rw [show c i = a i * wordRemainder T (s i ++ t i) by rfl, norm_mul]
      exact mul_le_mul_of_nonneg_left (henv i) (norm_nonneg _)
    exact (pow_le_pow_left₀ (norm_nonneg _) hi 2).trans_eq (by ring)
  have hmajor := ha.mul_left (B ^ 2)
  have hc := Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hbound hmajor
  obtain ⟨hs, he⟩ := diagonalHaar_parseval s t hinj c hc
  refine ⟨hs, he.trans_le ?_⟩
  exact (hc.tsum_le_tsum hbound hmajor).trans_eq (tsum_mul_left ..)

/-- All fractional FMZ rates transfer to countable series on the diagonal.
One constant and height threshold work across prime supports and tests. -/
theorem eventually_diagonal_fmz_fractional {ι : Type*} :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ 2 →
      ∀ s t : ι → PrimeWord, Function.Injective (fun i => wordFrequency (s i ++ t i)) →
      ∀ a : ι → ℂ, Summable (fun i => (‖a i‖ * wordWeight (s i ++ t i) ^ u) ^ 2) →
      ‖∑' i, (a i * wordRemainder T (s i ++ t i)) • pairWordL2 (s i) (t i)‖ ^ 2 ≤
        (K * fmzWienerRate u T) ^ 2 * ∑' i, (‖a i‖ * wordWeight (s i ++ t i) ^ u) ^ 2 := by
  obtain ⟨K, hK, h⟩ := eventually_centeredRationalOrdinate_fractional
  refine ⟨K, hK, ?_⟩
  filter_upwards [h] with T hT
  intro u hu hu2 s t hinj a ha
  exact (diagonal_fmz_sq_le_of_envelope T s t hinj a _ (K * fmzWienerRate u T) ha
    (fun i => hT u hu hu2 _ _ (wordNumerator_one_le _) (wordDenominator_one_le _))).2

/-- An eventually uniform multiplier envelope gives strong L² convergence of fixed tests. -/
private theorem tendsto_diagonal_fmz_L2_of_weight {ι : Type*}
    (W : PrimeWord → ℝ) (hW : ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ w, ‖wordRemainder T w‖ ≤ K * W w) (s t : ι → PrimeWord)
    (hinj : Function.Injective (fun i => wordFrequency (s i ++ t i))) (a : ι → ℂ)
    (ha : Summable (fun i => (‖a i‖ * W (s i ++ t i)) ^ 2)) :
    (∀ᶠ T : ℝ in atTop, Summable (fun i => (a i * wordRemainder T (s i ++ t i)) • pairWordL2 (s i) (t i))) ∧
    Tendsto (fun T : ℝ => ∑' i, (a i * wordRemainder T (s i ++ t i)) • pairWordL2 (s i) (t i))
      atTop (𝓝 0) := by
  obtain ⟨K, hK, h⟩ := hW
  let c := fun T i => a i * wordRemainder T (s i ++ t i)
  let g := fun i => K ^ 2 * (‖a i‖ * W (s i ++ t i)) ^ 2
  have hg : Summable g := ha.mul_left _
  have he : ∀ᶠ T : ℝ in atTop, ∀ i, ‖c T i‖ ^ 2 ≤ g i := by
    filter_upwards [h] with T hT i
    let w := s i ++ t i
    have hi := hT w
    have hu : ‖c T i‖ ≤ ‖a i‖ * (K * W w) := by
      rw [show c T i = a i * wordRemainder T w by rfl, norm_mul]
      exact mul_le_mul_of_nonneg_left hi (norm_nonneg _)
    exact (pow_le_pow_left₀ (norm_nonneg _) hu 2).trans_eq (by dsimp [g, w]; ring)
  have hs := he.mono (fun T ht => Summable.of_nonneg_of_le (fun _ => sq_nonneg _) ht hg)
  constructor
  · exact hs.mono fun T hT => (diagonalHaar_parseval s t hinj (c T) hT).1
  · have hz : Tendsto (fun T : ℝ => ∑' i, ‖c T i‖ ^ 2) atTop (𝓝 (∑' _ : ι, (0 : ℝ))) := by
      apply tendsto_tsum_of_dominated_convergence hg
      · intro i
        simpa [c] using (((tendsto_wordRemainder (s i ++ t i)).const_mul (a i)).norm.pow 2)
      · exact he.mono fun T hT i => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖c T i‖)]
          exact hT i
    simp only [tsum_zero] at hz
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hsq : Tendsto (fun T : ℝ => ‖∑' i, c T i • pairWordL2 (s i) (t i)‖ ^ 2) atTop (𝓝 0) :=
      hz.congr' (hs.mono fun T hT => (diagonalHaar_parseval s t hinj (c T) hT).2.symm)
    have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero, c] using hr

/-- A fixed, logarithmically weighted square-summable Fourier test has
vanishing translated FMZ error in L² of the infinite diagonal Haar law. -/
theorem tendsto_diagonal_fmz_L2 {ι : Type*} (s t : ι → PrimeWord)
    (hinj : Function.Injective (fun i => wordFrequency (s i ++ t i))) (a : ι → ℂ)
    (ha : Summable (fun i => (‖a i‖ * fmzLogWeight (wordWeight (s i ++ t i))) ^ 2)) :
    (∀ᶠ T : ℝ in atTop, Summable (fun i => (a i * wordRemainder T (s i ++ t i)) • pairWordL2 (s i) (t i))) ∧
    Tendsto (fun T : ℝ => ∑' i, (a i * wordRemainder T (s i ++ t i)) • pairWordL2 (s i) (t i))
      atTop (𝓝 0) := by
  apply tendsto_diagonal_fmz_L2_of_weight (fun w => fmzLogWeight (wordWeight w)) _ s t hinj a ha
  obtain ⟨K, hK, h⟩ := eventually_centeredRationalOrdinate_logWeight
  exact ⟨K, hK, h.mono fun T hT w => hT _ _ (wordNumerator_one_le w) (wordDenominator_one_le w)⟩

/-- A one-logarithm density bound at slope 1/4 removes the logarithm from
the Fourier weight. This hypothesis is implied by the published open
Conrey–Baluyot slope range and by the site's dyadic one - log estimate. -/
theorem tendsto_diagonal_fmz_L2_of_one_log {ι : Type*} (hD : UniformSelbergDensity (1 / 4))
    (s t : ι → PrimeWord) (hinj : Function.Injective (fun i => wordFrequency (s i ++ t i)))
    (a : ι → ℂ) (ha : Summable (fun i => (‖a i‖ * wordWeight (s i ++ t i)) ^ 2)) :
    (∀ᶠ T : ℝ in atTop, Summable (fun i => (a i * wordRemainder T (s i ++ t i)) • pairWordL2 (s i) (t i))) ∧
    Tendsto (fun T : ℝ => ∑' i, (a i * wordRemainder T (s i ++ t i)) • pairWordL2 (s i) (t i))
      atTop (𝓝 0) := by
  apply tendsto_diagonal_fmz_L2_of_weight wordWeight _ s t hinj a ha
  obtain ⟨A, hA, hraw⟩ := eventually_centeredRationalOrdinate_fractional
  obtain ⟨B, hB, hquad⟩ := eventually_centeredRationalOrdinate_remainder_rate hD
  refine ⟨max A B, hA.trans_le (le_max_left _ _), ?_⟩
  filter_upwards [hraw, hquad, eventually_gt_atTop (1 : ℝ)] with T hr hq ht w
  let W := wordWeight w
  let L := Real.log T
  have hL : 0 < L := Real.log_pos ht
  have hW : 0 ≤ W := by dsimp [W, wordWeight, rationalModeWeight]; positivity
  by_cases hw : W ≤ L
  · have hb := hq _ _ (wordNumerator_one_le w) (wordDenominator_one_le w)
    change ‖wordRemainder T w‖ ≤ B / L * W ^ 2 at hb
    apply hb.trans
    calc
      B / L * W ^ 2 = (B * W) * (W / L) := by ring
      _ ≤ (B * W) * 1 := mul_le_mul_of_nonneg_left ((div_le_one hL).mpr hw) (mul_nonneg hB.le hW)
      _ ≤ _ := by rw [mul_one]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hW
  · have hh := hr 0 le_rfl (by norm_num) _ _ (wordNumerator_one_le w) (wordDenominator_one_le w)
    have hneg : (Real.log T) ^ (-1 : ℝ) = (Real.log T)⁻¹ := by
      rw [Real.rpow_neg (Real.log_pos ht).le, Real.rpow_one]
    have hh' : ‖wordRemainder T w‖ ≤ A * L := by simpa [wordRemainder, fmzWienerRate, L, hneg] using hh
    exact hh'.trans ((mul_le_mul_of_nonneg_left (le_of_not_ge hw) hA.le).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hW))

/-- The arithmetic input on the dyadic detector route suffices for the pure
linear Fourier weight on the infinite diagonal. -/
theorem tendsto_diagonal_fmz_L2_of_dyadic {ι : Type*} (hD : DyadicInghamOneLog)
    (s t : ι → PrimeWord) (hinj : Function.Injective (fun i => wordFrequency (s i ++ t i)))
    (a : ι → ℂ) (ha : Summable (fun i => (‖a i‖ * wordWeight (s i ++ t i)) ^ 2)) :
    (∀ᶠ T : ℝ in atTop, Summable (fun i => (a i * wordRemainder T (s i ++ t i)) • pairWordL2 (s i) (t i))) ∧
    Tendsto (fun T : ℝ => ∑' i, (a i * wordRemainder T (s i ++ t i)) • pairWordL2 (s i) (t i))
      atTop (𝓝 0) := by
  apply tendsto_diagonal_fmz_L2_of_one_log _ s t hinj a ha
  exact uniformSelbergDensity_mono (by norm_num) (uniformSelbergDensity_four_thirds_of_dyadic_ingham_one_log hD)

/--
info: 'RiemannResearch.Analysis.ActualInfinitePrimeTorus.tendsto_diagonal_fmz_L2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_diagonal_fmz_L2

/--
info: 'RiemannResearch.Analysis.ActualInfinitePrimeTorus.tendsto_diagonal_fmz_L2_of_dyadic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_diagonal_fmz_L2_of_dyadic

end RiemannResearch.Analysis.ActualInfinitePrimeTorus
