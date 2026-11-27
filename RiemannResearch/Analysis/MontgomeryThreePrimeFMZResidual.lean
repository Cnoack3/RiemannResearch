/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.MontgomeryFixedRationalPairSeries
import RiemannResearch.Analysis.ThreePrimeFrequencyMesh

/-! # Exact actual-zero FMZ remainder on a three-prime Fourier mesh

Every noncentral integer multiple of a nonzero two-ratio frequency is a mixed
prime mode. Its actual ordinate sum equals height times the FMZ remainder.
The central cell retains the entire zero count. Subtracting the measured
equal-ordinate collision atom gives the signed strictly positive pair test.
-/

noncomputable section
open Zeta23
namespace RiemannResearch.Analysis.ActualInfinitePrimeTorus
open ActualZeroOrdinate ActualZeroCollisionCertificate
open MontgomeryAllPairWordRounding

/-- All noncentral mesh amplitudes are pure FMZ remainders. The integer
orders of the base step and the index of its multiple may depend on height. -/
theorem threePrimeMesh_ordinateSum_eq_remainder {p q r : Nat.Primes}
    (hpq : (p : ℕ) < q) (hqr : (q : ℕ) < r) {a b : ℤ}
    (hh : wordFrequency (ratioWord p q a ++ ratioWord q r b) ≠ 0)
    {T : ℝ} (hT : T ≠ 0) :
    ∀ k : ℤ, k ≠ 0 →
      ordinateSum T ((k : ℝ) * wordFrequency (ratioWord p q a ++ ratioWord q r b)) =
        (T : ℂ) * wordRemainder T (ratioWord p q (k*a) ++ ratioWord q r (k*b)) := by
  intro k hk
  let w := ratioWord p q (k*a) ++ ratioWord q r (k*b)
  have hf := threePrimeWordFrequency_mul p q r k a b
  have hfreq : wordFrequency w ≠ 0 :=
    hf ▸ mul_ne_zero (Int.cast_ne_zero.mpr hk) hh
  have hw : k*a ≠ 0 ∨ k*b ≠ 0 := by
    by_contra! h
    apply hfreq
    simp only [w, wordFrequency_append, ratioWord_frequency, h.1, h.2, Int.cast_zero,
      zero_mul, add_zero]
  have hlog : Real.log ((wordNumerator w : ℝ) / wordDenominator w) = wordFrequency w := by
    apply (PrimePhaseTorus.prime_log_ratio_eq_frequency _ _ (wordPrimes_prime w)).trans
    exact (wordFrequency_eq_sum w _ (fun z hz =>
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨z, hz, rfl⟩))).symm
  have hne : wordNumerator w ≠ wordDenominator w := by
    intro he
    have hd : (wordDenominator w : ℝ) ≠ 0 := by
      exact_mod_cast (show 0 < wordDenominator w from wordDenominator_one_le w).ne'
    exact hfreq (by simpa only [he, div_self hd, Real.log_one] using hlog.symm)
  change ordinateSum T _ = (T : ℂ) * wordRemainder T w
  rw [wordRemainder, two_ratio_word_FMZ_zero hpq hqr hw, sub_zero, centeredRationalOrdinate,
    if_neg hne, sub_zero, hlog, threePrimeWordFrequency_mul]
  field_simp [Complex.ofReal_ne_zero.mpr hT]

/-- Squared actual amplitudes on every mesh cell, including the central
cell whose squared amplitude is the square of the full occurrence count. -/
theorem threePrimeMesh_ordinateSum_norm_sq {p q r : Nat.Primes}
    (hpq : (p : ℕ) < q) (hqr : (q : ℕ) < r) {a b : ℤ}
    (hh : wordFrequency (ratioWord p q a ++ ratioWord q r b) ≠ 0)
    {T : ℝ} (hT : T ≠ 0) (k : ℤ) :
    ‖ordinateSum T ((k : ℝ) * wordFrequency (ratioWord p q a ++ ratioWord q r b))‖^2 =
      if k = 0 then (Ncount 0 T : ℝ)^2
      else T^2 * ‖wordRemainder T (ratioWord p q (k*a) ++ ratioWord q r (k*b))‖^2 := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [if_neg hk, threePrimeMesh_ordinateSum_eq_remainder hpq hqr hh hT k hk, norm_mul,
      mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The collision subtraction is identical in the central cell and every
noncentral cell. This equality holds before integration or taking limits. -/
theorem threePrimeMesh_positivePairCosine {p q r : Nat.Primes}
    (hpq : (p : ℕ) < q) (hqr : (q : ℕ) < r) {a b : ℤ}
    (hh : wordFrequency (ratioWord p q a ++ ratioWord q r b) ≠ 0)
    {T : ℝ} (hT : T ≠ 0) (k : ℤ) :
    positivePairCosine T ((k : ℝ) * wordFrequency (ratioWord p q a ++ ratioWord q r b)) =
      (if k = 0 then (Ncount 0 T : ℝ)^2 else
        T^2 * ‖wordRemainder T (ratioWord p q (k*a) ++ ratioWord q r (k*b))‖^2) -
      (actualCollision T : ℝ) := by
  rw [positivePairCosine_eq_square_sub_collision, threePrimeMesh_ordinateSum_norm_sq hpq hqr hh hT]

end RiemannResearch.Analysis.ActualInfinitePrimeTorus
