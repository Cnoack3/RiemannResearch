/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualThreePrimeAdjacentGaps
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Function.Floor

/-! # Haar Parseval for three-prime tests of two neighboring zero gaps

A common translation of three ordinates cancels from the resonant character.
Translation of the two gap angles yields orthogonal modes indexed by integer
pairs, even though the two prime ratios share the middle prime. The
microscopic reconstruction estimate therefore transfers to a Hilbert norm.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualInfinitePrimeTorus
open ActualZeroOrdinate CompactCharacter CompactGaugeOrbitLaw

local instance : MeasurableSpace PrimeTorus := borel PrimeTorus
local instance : BorelSpace PrimeTorus := ⟨rfl⟩
local instance : MeasurableSpace (PrimeTorus × PrimeTorus) := borel _
local instance : BorelSpace (PrimeTorus × PrimeTorus) := ⟨rfl⟩

/-- Uniqueness of the two prime-ratio frequencies. Their exponents at the
outer primes determine both integer orders. -/
theorem two_prime_steps_injective {p q r : Nat.Primes} (hpq : (p : ℕ) < q) (hqr : (q : ℕ) < r) :
    Function.Injective (fun m : ℤ × ℤ => wordFrequency (ratioWord p q m.1 ++ ratioWord q r m.2)) := by
  rintro ⟨k, l⟩ ⟨k', l'⟩ he
  let w := ratioWord p q (k - k') ++ ratioWord q r (l - l')
  have hw : wordFrequency w = 0 := by
    simp only [w, wordFrequency_append, ratioWord_frequency, Int.cast_sub]
    simp only [wordFrequency_append, ratioWord_frequency] at he
    linarith only [he]
  have hf : wordFrequency w = PrimePhaseTorus.primeFrequency (wordPrimes w) (wordMode w) :=
    wordFrequency_eq_sum w _ (fun a ha => List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, ha, rfl⟩))
  have hz := (PrimePhaseTorus.primeFrequency_eq_zero_iff _ _ (wordPrimes_prime w)).mp (hf.symm.trans hw)
  have h1 := hz (p : ℕ) (by simp [w, ratioWord, wordPrimes])
  have h2 := hz (r : ℕ) (by simp [w, ratioWord, wordPrimes])
  simp [w, ratioWord, wordMode, ne_of_lt hpq, ne_of_lt (hpq.trans hqr)] at h1
  simp [w, ratioWord, wordMode, (ne_of_lt hqr).symm, (ne_of_lt (hpq.trans hqr)).symm] at h2
  exact Prod.ext (by omega) (by omega)

/-- These are precisely the Fourier moments of two independent uniform circle angles. -/
theorem prime_ratio_pair_haar_moment {p q r : Nat.Primes}
    (hpq : (p : ℕ) < q) (hqr : (q : ℕ) < r) (k l : ℤ) :
    (∫ z, character (ratioWord p q k) z * character (ratioWord q r l) z ∂primeHaar) =
      if k = 0 ∧ l = 0 then 1 else 0 := by
  have hi := two_prime_steps_injective hpq hqr
  have hh : wordFrequency (ratioWord p q 0 ++ ratioWord q r 0) = 0 := by
    simp [wordFrequency_append, ratioWord_frequency]
  change (∫ z, (character (ratioWord p q k) * character (ratioWord q r l)) z ∂primeHaar) = _
  rw [← character_append, primeHaar_word, haarMoment_frequency]
  by_cases hz : k = 0 ∧ l = 0
  · obtain ⟨rfl, rfl⟩ := hz
    simp [hh]
  · rw [if_neg (fun h => hz (by
      have he : (k, l) = ((0, 0) : ℤ × ℤ) := hi (h.trans hh.symm)
      exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩)), if_neg hz]

/-- Every resonant three-ordinate mode is identically one on the common diagonal. -/
theorem resonant_common_diagonal (p q r : Nat.Primes) (k l : ℤ) (z : PrimeTorus) :
    character (ratioWord p q (-k)) z * character (ratioWord p q k ++ ratioWord q r (-l)) z *
      character (ratioWord q r l) z = 1 := by
  let s := ratioWord p q (-k)
  let t := ratioWord p q k ++ ratioWord q r (-l)
  let w := ratioWord q r l
  have hf : wordFrequency ((s ++ t) ++ w) = 0 := by
    simp only [s, t, w, wordFrequency_append, ratioWord_frequency, Int.cast_neg, neg_mul]
    ring
  have h := congrArg (fun f : C(PrimeTorus, ℂ) => f z) (character_one_of_frequency_zero _ hf)
  simpa only [character_append, ContinuousMap.mul_apply, ContinuousMap.one_apply, s, t, w] using h

/-- Exact countable Parseval for translations of the two gap angles. -/
theorem threePrime_gap_parseval {ι : Type*} {p q r : Nat.Primes} (hpq : (p : ℕ) < q) (hqr : (q : ℕ) < r)
    (k l : ι → ℤ) (hinj : Function.Injective (fun i => (k i, l i))) (b : ι → ℂ)
    (hb : Summable (fun i => ‖b i‖ ^ 2)) :
    Summable (fun i => b i • pairWordL2 (ratioWord p q (k i)) (ratioWord q r (l i))) ∧
      ‖∑' i, b i • pairWordL2 (ratioWord p q (k i)) (ratioWord q r (l i))‖ ^ 2 = ∑' i, ‖b i‖ ^ 2 :=
  diagonalHaar_parseval _ _ ((two_prime_steps_injective hpq hqr).comp hinj) b hb

/-- Haar mean-square reconstruction error for a countable translated
microscopic test. Distinctness concerns the actual rounded order pairs. -/
theorem threePrime_gap_reconstruction_L2 {ι : Type*} {T : ℝ} (hT : 0 ≤ T)
    {p q r : Nat.Primes} (hpq : NextPrime p q) (hqr : NextPrime q r)
    (ξ η : ι → ℝ) (a : ι → ℂ) (ha : Summable (fun i => ‖a i‖ ^ 2)) :
    let k := fun i => roundedOrder (logPrimeStep p q) (ξ i * (Real.log T / (2 * Real.pi)))
    let l := fun i => roundedOrder (logPrimeStep q r) (η i * (Real.log T / (2 * Real.pi)))
    let E := fun i => roundedThreePrimeSample T p q r (ξ i) (η i) -
      unfoldedAdjacentGapTransform T (ξ i) (η i)
    Function.Injective (fun i => (k i, l i)) →
      Summable (fun i => (a i * E i) • pairWordL2 (ratioWord p q (k i)) (ratioWord q r (l i))) ∧
      ‖∑' i, (a i * E i) • pairWordL2 (ratioWord p q (k i)) (ratioWord q r (l i))‖ ^ 2 ≤
        (Real.log 2 * (T / (Ncount 0 T : ℝ))) ^ 2 * ∑' i, ‖a i‖ ^ 2 := by
  intro k l E hinj
  let B := Real.log 2 * (T / (Ncount 0 T : ℝ))
  have hb (i : ι) : ‖a i * E i‖ ^ 2 ≤ B ^ 2 * ‖a i‖ ^ 2 := by
    have h := roundedThreePrimeSample_error_consecutive hT hpq hqr (ξ i) (η i)
    rw [norm_mul]
    exact (pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left h (norm_nonneg (a i))) 2).trans_eq (by dsimp only [B]; ring)
  have hmaj := ha.mul_left (B ^ 2)
  have hs := Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hb hmaj
  obtain ⟨hseries, hparseval⟩ := threePrime_gap_parseval hpq.1 hqr.1 k l hinj (fun i => a i * E i) hs
  refine ⟨hseries, hparseval.trans_le ?_⟩
  exact (hs.tsum_le_tsum hb hmaj).trans_eq (tsum_mul_left ..)

/-- The empirical two-gap transforms have a Lipschitz constant tending to one
in the sum of the absolute frequency displacements. -/
theorem unfoldedAdjacentGapTransform_lipschitz {T : ℝ} (hT : 1 ≤ T) (ξ η ξ' η' : ℝ) :
    ‖unfoldedAdjacentGapTransform T ξ η - unfoldedAdjacentGapTransform T ξ' η'‖ ≤
      (|ξ - ξ'| + |η - η'|) * ((Real.log T / (2 * Real.pi)) * (T / (Ncount 0 T : ℝ))) := by
  let a := Real.log T / (2 * Real.pi)
  have ha : 0 ≤ a := div_nonneg (Real.log_nonneg hT) (by positivity)
  have h := markedAdjacentGapMean_lipschitz (zero_le_one.trans hT) 0 (ξ * a) (η * a) (ξ' * a) (η' * a)
  simpa only [unfoldedAdjacentGapTransform, ← sub_mul, abs_mul, abs_of_nonneg ha, ← add_mul,
    mul_assoc] using h

/-- The rounding operation is Borel and the actual finite gap transform
is measurable in both real test frequencies. -/
theorem measurable_gap_reconstruction_error {X : Type*} [MeasurableSpace X]
    (T : ℝ) (p q r : Nat.Primes) {ξ η : X → ℝ} (hξ : Measurable ξ) (hη : Measurable η) :
    Measurable fun x => roundedThreePrimeSample T p q r (ξ x) (η x) -
      unfoldedAdjacentGapTransform T (ξ x) (η x) := by
  apply Measurable.sub
  · let g : ℤ × ℤ → ℂ := fun m => resonantThreePrimeSample T p q r m.1 m.2
    have hg : Measurable g := measurable_of_countable g
    let k := fun x => roundedOrder (logPrimeStep p q) (ξ x * (Real.log T / (2 * Real.pi)))
    let l := fun x => roundedOrder (logPrimeStep q r) (η x * (Real.log T / (2 * Real.pi)))
    have hk : Measurable k := by
      dsimp only [k, roundedOrder]
      fun_prop
    have hl : Measurable l := by
      dsimp only [l, roundedOrder]
      fun_prop
    change Measurable (g ∘ (fun x => (k x, l x)))
    exact hg.comp (hk.prodMk hl)
  · unfold unfoldedAdjacentGapTransform markedAdjacentGapMean ZeroOrdinate.phase
    fun_prop

/-- Euclidean Plancherel transfers the uniform two-gap Fourier error to
physical space for every square-integrable smoothing function. The output
has the specified Fourier transform almost everywhere. -/
theorem threePrime_gap_physical_plancherel {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {T : ℝ} (hT : 0 ≤ T) {p q r : Nat.Primes} (hpq : NextPrime p q) (hqr : NextPrime q r)
    {ξ η : E → ℝ} (hξ : Measurable ξ) (hη : Measurable η) (f : Lp (α := E) ℂ 2) :
    ∃ e : Lp (α := E) ℂ 2,
      (∀ᵐ t, (Lp.fourierTransformₗᵢ E ℂ e) t = (Lp.fourierTransformₗᵢ E ℂ f) t *
        (roundedThreePrimeSample T p q r (ξ t) (η t) - unfoldedAdjacentGapTransform T (ξ t) (η t))) ∧
      ‖e‖ ≤ (Real.log 2 * (T / (Ncount 0 T : ℝ))) * ‖f‖ := by
  let F := Lp.fourierTransformₗᵢ E ℂ
  let D := fun t => roundedThreePrimeSample T p q r (ξ t) (η t) -
    unfoldedAdjacentGapTransform T (ξ t) (η t)
  let g := fun t => F f t * D t
  let B := Real.log 2 * (T / (Ncount 0 T : ℝ))
  have hD : Measurable D := measurable_gap_reconstruction_error T p q r hξ hη
  have hbound (t : E) : ‖g t‖ ≤ B * ‖F f t‖ := by
    dsimp only [g]
    rw [norm_mul, mul_comm B]
    exact mul_le_mul_of_nonneg_left (roundedThreePrimeSample_error_consecutive hT hpq hqr _ _)
      (norm_nonneg _)
  have hg : MemLp g 2 volume :=
    MemLp.of_le_mul (Lp.memLp (F f)) ((Lp.aestronglyMeasurable (F f)).mul hD.aestronglyMeasurable)
      (Filter.Eventually.of_forall hbound)
  refine ⟨F.symm (hg.toLp g), ?_, ?_⟩
  · change ∀ᵐ t, F (F.symm (hg.toLp g)) t = g t
    rw [F.apply_symm_apply]
    exact hg.coeFn_toLp
  · change ‖F.symm (hg.toLp g)‖ ≤ B * ‖f‖
    rw [F.symm.norm_map, ← F.norm_map f]
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hg.coeFn_toLp] with t ht
    simpa only [ht] using hbound t

/--
info: 'RiemannResearch.Analysis.ActualInfinitePrimeTorus.prime_ratio_pair_haar_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prime_ratio_pair_haar_moment

/--
info: 'RiemannResearch.Analysis.ActualInfinitePrimeTorus.resonant_common_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms resonant_common_diagonal

/--
info: 'RiemannResearch.Analysis.ActualInfinitePrimeTorus.threePrime_gap_reconstruction_L2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms threePrime_gap_reconstruction_L2

/--
info: 'RiemannResearch.Analysis.ActualInfinitePrimeTorus.threePrime_gap_physical_plancherel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms threePrime_gap_physical_plancherel

end RiemannResearch.Analysis.ActualInfinitePrimeTorus
