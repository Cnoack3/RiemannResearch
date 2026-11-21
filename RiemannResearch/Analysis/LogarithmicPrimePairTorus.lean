import RiemannResearch.Analysis.LogarithmicPrimePairFMZ
import RiemannResearch.Analysis.ActualPrimeTorusFMZ

/-!
# The moving prime-pair polynomial on its finite prime torus

The prime coordinates run through the upper shifted endpoint. Each character has
exponent vector given by the difference of the two prime factorizations.
-/

noncomputable section
open Filter Finset
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.LogarithmicPrimePairs
open PrimeTorusHaar PrimePhaseTorus ActualPrimeTorusFMZ ActualZeroOrdinate

private def primesThrough (M : ℕ) : Finset ℕ := (range (M + 1)).filter Nat.Prime

private theorem primesThrough_prime {M p : ℕ} (hp : p ∈ primesThrough M) : p.Prime :=
  (mem_filter.mp hp).2

private theorem recover_integer {m M : ℕ} (hm : 0 < m) (hle : m ≤ M) :
    primeProduct (primesThrough M) m.factorization = m := by
  apply Nat.eq_of_factorization_eq
    (primeProduct_ne_zero _ _ (fun _ hp => primesThrough_prime hp)) hm.ne'
  intro p
  rw [primeProduct_factorization _ _ (fun _ hp => primesThrough_prime hp)]
  split_ifs with hp
  · rfl
  · symm
    by_cases hpr : p.Prime
    · apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      exact hp (mem_filter.mpr ⟨mem_range.mpr (by have := Nat.le_of_dvd hm hd; omega), hpr⟩)
    · exact Nat.factorization_eq_zero_of_not_prime _ hpr

def pairExponents (m n p : ℕ) : ℤ := (m.factorization p : ℤ) - n.factorization p

private theorem pair_prime_frequency {m n M : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmM : m ≤ M) (hnM : n ≤ M) :
    primeFrequency (primesThrough M) (pairExponents m n) = Real.log ((m : ℝ) / n) := by
  have hlog (j : ℕ) :=
    primeProduct_log (primesThrough M) j.factorization (fun _ hp => primesThrough_prime hp)
  rw [Real.log_div (by exact_mod_cast hm.ne') (by exact_mod_cast hn.ne')]
  have h1 := hlog m
  have h2 := hlog n
  rw [recover_integer hm hmM] at h1
  rw [recover_integer hn hnM] at h2
  rw [h1, h2, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  simp only [pairExponents, Int.cast_sub, Int.cast_natCast, sub_mul]

def pairPrimes (B u X : ℝ) : Finset ℕ := primesThrough (⌊B * X⌋₊ + shiftWidth u X)

def pairTorusPolynomial (A B u X : ℝ) : C(Torus (pairPrimes B u X), ℂ) :=
  ∑ h ∈ Ioc 0 (shiftWidth u X), ∑ n ∈ Ioc ⌊A * X⌋₊ ⌊B * X⌋₊,
    (pairCoefficient u X n h : ℂ) •
      character (fun p : pairPrimes B u X => pairExponents (n + h) n p)

theorem pairTorusPolynomial_at_zero (A B u X : ℝ) :
    pairTorusPolynomial A B u X 0 = (trianglePairAverage A B u X : ℂ) := by
  rw [← pairModeTest_at_identity]
  simp [pairTorusPolynomial, pairModeTest, ContinuousMap.sum_apply, character_apply]

private theorem frequency_on_window {A B u X : ℝ} {n h : ℕ}
    (hn : n ∈ Ioc ⌊A * X⌋₊ ⌊B * X⌋₊) (hh : h ∈ Ioc 0 (shiftWidth u X)) :
    primeFrequency (pairPrimes B u X) (pairExponents (n + h) n) =
      Real.log ((↑(n + h) : ℝ) / n) := by
  obtain ⟨hn0, hn1⟩ := mem_Ioc.mp hn
  obtain ⟨hh0, hh1⟩ := mem_Ioc.mp hh
  exact pair_prime_frequency (by omega) (by omega) (by omega) (by omega)

/-- All the nonzero shifts have nontrivial characters, before taking any limit. -/
theorem pairTorusPolynomial_haar (A B u X : ℝ) :
    haarIntegral (pairTorusPolynomial A B u X) = 0 := by
  simp only [pairTorusPolynomial, map_sum, map_smul, smul_eq_mul, haarIntegral_character_eq]
  apply sum_eq_zero
  intro h hh
  apply sum_eq_zero
  intro n hn
  have hne : (fun p : pairPrimes B u X => pairExponents (n + h) n p) ≠ 0 := by
    intro he
    have hf := (primeFrequency_eq_zero_iff _ _ (fun _ hp => primesThrough_prime hp)).2
      ((restrictedMode_eq_zero_iff _ _).1 he)
    have hzero := (frequency_on_window hn hh).symm.trans hf
    have hpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_le _).trans_lt (mem_Ioc.mp hn).1
    have hm : (n : ℝ) < (↑(n + h) : ℝ) := by
      exact_mod_cast (show n < n + h by have := (mem_Ioc.mp hh).1; omega)
    exact (Real.log_pos ((one_lt_div hpos).mpr hm)).ne' hzero
  rw [if_neg hne, mul_zero]

/-- Evaluating the actual zero functional on the polynomial agrees exactly with its
rational-mode representation, for every height and both cutoffs. -/
theorem pairTorusPolynomial_sample (A B u X T : ℝ) :
    sampleFunctional (pairPrimes B u X) T (pairTorusPolynomial A B u X) / (T : ℂ) =
      pairModeTest A B u X (fun m n => ordinateSum T (Real.log ((m : ℝ) / n)) / (T : ℂ)) := by
  simp only [pairTorusPolynomial, pairModeTest, map_sum, map_smul, smul_eq_mul,
    sampleFunctional_character, sum_div]
  apply sum_congr rfl
  intro h hh
  apply sum_congr rfl
  intro n hn
  rw [frequency_on_window hn hh, mul_div_assoc]

end RiemannResearch.Analysis.LogarithmicPrimePairs
