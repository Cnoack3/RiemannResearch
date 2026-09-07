import RiemannResearch.RH.PrimeCompensationLimits
import RiemannResearch.RH.PrimeSquarePartialSummation
import RiemannResearch.RH.WeilExtension
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.Prime.Int

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Exact prime, square, and higher-power partition of the Weil arithmetic sum

The indices are the actual natural von Mangoldt indices. Unique prime-power
representation and absolute summability justify every rearrangement. No
prime-square compensation or explicit-formula identity is assumed here.
-/

open scoped BigOperators
namespace RiemannResearch.RH.PrimeCompensationLimits

private theorem primePowerIndex_injective (k : ℕ) (hk : 0 < k) :
    Function.Injective (fun pj : Nat.Primes × ℕ => (pj.1 : ℕ) ^ (pj.2 + k)) := by
  rintro ⟨p, i⟩ ⟨q, j⟩ h
  have hh := p.property.pow_inj' q.property (by omega : i + k ≠ 0)
    (by omega : j + k ≠ 0) h
  have hpq : p = q := Subtype.ext hh.1
  have hij : i = j := by omega
  exact Prod.ext hpq hij

private theorem summable_primePowerRestriction {f : ℕ → ℝ} (hf : Summable f)
    (k : ℕ) (hk : 0 < k) :
    Summable (fun pj : Nat.Primes × ℕ => f ((pj.1 : ℕ) ^ (pj.2 + k))) := by
  exact hf.comp_injective (primePowerIndex_injective k hk)

/-- The third-and-higher powers are separated after the actual prime and
square terms, with every infinite rearrangement justified. -/
theorem tsum_primePowers_split_three {f : ℕ → ℝ} (hf : Summable f)
    (hs : Function.support f ⊆ {n | IsPrimePow n}) :
    (∑' n : ℕ, f n) =
      (∑' p : Nat.Primes, f p) + (∑' p : Nat.Primes, f ((p : ℕ) ^ 2)) +
        ∑' pj : Nat.Primes × ℕ, f ((pj.1 : ℕ) ^ (pj.2 + 3)) := by
  have h2 := summable_primePowerRestriction hf 2 (by omega)
  have h3 := summable_primePowerRestriction hf 3 (by omega)
  have hsq : Summable (fun p : Nat.Primes => f ((p : ℕ) ^ 2)) := by
    have h := h2.comp_injective
      (show Function.Injective (fun p : Nat.Primes => (p, (0 : ℕ))) by
        intro p q h; exact congrArg Prod.fst h)
    change Summable (fun p : Nat.Primes => f ((p : ℕ) ^ (0 + 2))) at h
    exact h
  rw [tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers hf hs]
  have he : (∑' p : Nat.Primes, ∑' j : ℕ, f ((p : ℕ) ^ (j + 2))) =
      (∑' p : Nat.Primes, f ((p : ℕ) ^ 2)) +
        ∑' p : Nat.Primes, ∑' j : ℕ, f ((p : ℕ) ^ (j + 3)) := by
    calc
      _ = ∑' p : Nat.Primes,
          (f ((p : ℕ) ^ 2) + ∑' j : ℕ, f ((p : ℕ) ^ (j + 3))) := by
        apply tsum_congr
        intro p
        simpa only [zero_add, Nat.add_assoc] using (h2.prod_factor p).tsum_eq_zero_add
      _ = _ := hsq.tsum_add h3.prod
  rw [he, ← h3.tsum_prod]
  exact (add_assoc _ _ _).symm

/-- The exact prime-power support of the arithmetic summand. -/
theorem support_primePowerCorrelationTerm (C : ℝ → ℝ) :
    Function.support (fun n : ℕ => primePowerWeight n * C (Real.log n)) ⊆
      {n | IsPrimePow n} := by
  intro n hn
  by_contra h
  change ¬ IsPrimePow n at h
  apply hn
  simp [primePowerWeight, ArithmeticFunction.vonMangoldt_apply, h]

theorem primePowerTerm_prime (C : ℝ → ℝ) {p : ℕ} (hp : p.Prime) :
    primePowerWeight p * C (Real.log p) =
      Real.log p / Real.sqrt p * C (Real.log p) := by
  rw [primePowerWeight, ArithmeticFunction.vonMangoldt_apply_prime hp]

theorem primePowerTerm_square (C : ℝ → ℝ) {p : ℕ} (hp : p.Prime) :
    primePowerWeight (p ^ 2) * C (Real.log (p ^ 2 : ℕ)) =
      primeSquareWeight p * C (2 * Real.log p) := by
  rw [primePowerWeight, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  simp only [Nat.cast_pow, Real.log_pow, primeSquareWeight, if_pos hp,
    Real.sqrt_sq (Nat.cast_nonneg p), Nat.cast_ofNat]

theorem primePowerTerm_higher (C : ℝ → ℝ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    primePowerWeight (p ^ (j + 3)) * C (Real.log (p ^ (j + 3) : ℕ)) =
      higherPrimePowerWeight p j * C (higherPrimePowerDisplacement p j) := by
  rw [primePowerWeight, ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime hp, higherPrimePowerWeight_eq, if_pos hp]
  have hs : Real.sqrt ((p ^ (j + 3) : ℕ) : ℝ) =
      (p : ℝ) ^ (((j : ℝ) + 3) / 2) := by
    rw [Nat.cast_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul (Nat.cast_nonneg p)]
    congr 1
    push_cast
    ring
  rw [hs]
  congr 2
  simp only [higherPrimePowerDisplacement, Nat.cast_pow, Real.log_pow, Nat.cast_add,
    Nat.cast_ofNat]

private theorem primePairInclusion_injective :
    Function.Injective (fun pj : Nat.Primes × ℕ => ((pj.1 : ℕ), pj.2)) := by
  rintro ⟨p, i⟩ ⟨q, j⟩ h
  change ((p : ℕ), i) = ((q : ℕ), j) at h
  exact Prod.ext (Subtype.ext (congrArg (fun z : ℕ × ℕ => z.1) h))
    (congrArg (fun z : ℕ × ℕ => z.2) h)

private theorem higherTerm_support (C : ℝ → ℝ) :
    Function.support (fun pj : ℕ × ℕ =>
      higherPrimePowerWeight pj.1 pj.2 * C (higherPrimePowerDisplacement pj.1 pj.2)) ⊆
        Set.range (fun pj : Nat.Primes × ℕ => ((pj.1 : ℕ), pj.2)) := by
  rintro ⟨p, j⟩ h
  have hp : p.Prime := by
    by_contra hn
    exact h (by simp [higherPrimePowerWeight, hn])
  exact ⟨(⟨p, hp⟩, j), rfl⟩

private theorem tsum_primes_eq_of_zero_nonprime (f : ℕ → ℝ)
    (hf : ∀ p : ℕ, ¬p.Prime → f p = 0) :
    (∑' p : Nat.Primes, f p) = ∑' p : ℕ, f p := by
  have hi : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := by
    intro p q h
    exact Subtype.ext h
  have hs : Function.support f ⊆ Set.range (fun p : Nat.Primes => (p : ℕ)) := by
    intro p hp
    have hp' : p.Prime := by
      by_contra h
      exact hp (hf p h)
    exact ⟨⟨p, hp'⟩, rfl⟩
  exact hi.tsum_eq hs

/-- Summability of the exact higher-power remainder follows directly from
summability of the original natural arithmetic series. -/
theorem summable_higherPrimePowerTerm_of_summable (C : ℝ → ℝ)
    (hC : Summable (fun n : ℕ => primePowerWeight n * C (Real.log n))) :
    Summable (fun pj : ℕ × ℕ =>
      higherPrimePowerWeight pj.1 pj.2 * C (higherPrimePowerDisplacement pj.1 pj.2)) := by
  have hzero : ∀ pj : ℕ × ℕ,
      pj ∉ Set.range (fun qj : Nat.Primes × ℕ => ((qj.1 : ℕ), qj.2)) →
      higherPrimePowerWeight pj.1 pj.2 * C (higherPrimePowerDisplacement pj.1 pj.2) = 0 := by
    intro pj hpj
    by_contra hne
    exact hpj (higherTerm_support C hne)
  apply (primePairInclusion_injective.summable_iff hzero).mp
  have h := summable_primePowerRestriction hC 3 (by omega)
  apply h.congr
  intro pj
  exact primePowerTerm_higher C pj.1.property pj.2

/-- Exact partition of the actual Weil von Mangoldt series into prime,
prime-square, and all higher-prime-power terms. The hypothesis is solely
absolute convergence of the original arithmetic series. -/
theorem primePowerSeries_eq_prime_add_square_add_higher (C : ℝ → ℝ)
    (hC : Summable (fun n : ℕ => primePowerWeight n * C (Real.log n))) :
    (∑' n : ℕ, primePowerWeight n * C (Real.log n)) =
      (∑' p : ℕ, if p.Prime then Real.log p / Real.sqrt p * C (Real.log p) else 0) +
      (∑' p : ℕ, primeSquareWeight p * C (2 * Real.log p)) +
      ∑' pj : ℕ × ℕ,
        higherPrimePowerWeight pj.1 pj.2 * C (higherPrimePowerDisplacement pj.1 pj.2) := by
  rw [tsum_primePowers_split_three hC (support_primePowerCorrelationTerm C)]
  have hprime : (∑' p : Nat.Primes, primePowerWeight p * C (Real.log p)) =
      ∑' p : ℕ, if p.Prime then Real.log p / Real.sqrt p * C (Real.log p) else 0 := by
    calc
      _ = ∑' p : Nat.Primes, Real.log p / Real.sqrt p * C (Real.log p) := by
        apply tsum_congr
        intro p
        exact primePowerTerm_prime C p.property
      _ = _ := by
        calc
          _ = ∑' p : Nat.Primes,
              (if (p : ℕ).Prime then Real.log p / Real.sqrt p * C (Real.log p) else 0) := by
            apply tsum_congr
            intro p
            exact (if_pos p.property).symm
          _ = _ := tsum_primes_eq_of_zero_nonprime
            (fun p : ℕ => if p.Prime then Real.log p / Real.sqrt p * C (Real.log p) else 0)
            (fun p hp => if_neg hp)
  have hsquare : (∑' p : Nat.Primes,
      primePowerWeight ((p : ℕ) ^ 2) * C (Real.log ((p : ℕ) ^ 2 : ℕ))) =
      ∑' p : ℕ, primeSquareWeight p * C (2 * Real.log p) := by
    calc
      _ = ∑' p : Nat.Primes, primeSquareWeight p * C (2 * Real.log p) := by
        apply tsum_congr
        intro p
        exact primePowerTerm_square C p.property
      _ = _ := by
        exact tsum_primes_eq_of_zero_nonprime
          (fun p : ℕ => primeSquareWeight p * C (2 * Real.log p))
          (fun p hp => by simp [primeSquareWeight, hp])
  have hhigher : (∑' pj : Nat.Primes × ℕ,
      primePowerWeight ((pj.1 : ℕ) ^ (pj.2 + 3)) *
        C (Real.log ((pj.1 : ℕ) ^ (pj.2 + 3) : ℕ))) =
      ∑' pj : ℕ × ℕ,
        higherPrimePowerWeight pj.1 pj.2 * C (higherPrimePowerDisplacement pj.1 pj.2) := by
    calc
      _ = ∑' pj : Nat.Primes × ℕ, higherPrimePowerWeight pj.1 pj.2 *
          C (higherPrimePowerDisplacement pj.1 pj.2) := by
        apply tsum_congr
        intro pj
        exact primePowerTerm_higher C pj.1.property pj.2
      _ = _ := primePairInclusion_injective.tsum_eq (higherTerm_support C)
  rw [hprime, hsquare, hhigher]

/-- A concrete decay hypothesis discharges the natural-series summability
before its exact decomposition. -/
theorem primePowerSeries_eq_prime_add_square_add_higher_of_exp_decay
    (C : ℝ → ℝ) (A : ℝ)
    (hC : ∀ t : ℝ, 0 ≤ t → |C t| ≤ A * Real.exp (-3 * t)) :
    (∑' n : ℕ, primePowerWeight n * C (Real.log n)) =
      (∑' p : ℕ, if p.Prime then Real.log p / Real.sqrt p * C (Real.log p) else 0) +
      (∑' p : ℕ, primeSquareWeight p * C (2 * Real.log p)) +
      ∑' pj : ℕ × ℕ,
        higherPrimePowerWeight pj.1 pj.2 * C (higherPrimePowerDisplacement pj.1 pj.2) := by
  exact primePowerSeries_eq_prime_add_square_add_higher C
    (SignedWeilCorrelation.summable_real_primePowerTerm_of_exp_decay C A hC)

end RiemannResearch.RH.PrimeCompensationLimits
