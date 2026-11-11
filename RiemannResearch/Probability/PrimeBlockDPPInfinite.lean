import RiemannResearch.Probability.PrimeBlockDPP
import RiemannResearch.Probability.DeterminantalMoments
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Infinitely many arithmetic DPP particles and holes

Source: the finite fair-coin patterns of `PrimeBlockDPP` and the elementary
vanishing-tail argument for independent fair Bernoulli coordinates. The proof
uses geometric finite-event probabilities, not an infinite-mean inference.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace RiemannResearch.Probability.DPP.PrimeBlock

/-- Every finite window has mean density one half. -/
theorem expected_window_count {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → Site) :
    (∫ z, windowCount (fun z : Site → Bool => {i | z i = true}) e z ∂law) =
      (Fintype.card ι : ℝ)/2 := by
  rw [law_isDPP.expected_windowCount]
  simp [div_eq_mul_inv]

/-- Arithmetic correlations subtract an explicit square sum from fair-coin variance. -/
theorem variance_window_count {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ↪ Site) :
    ProbabilityTheory.variance
      (windowCount (fun z : Site → Bool => {i | z i = true}) e) law =
      (Fintype.card ι : ℝ)/4 -
        (∑ i, ∑ j, (signedEntry (e i) (e j))^2) / (4*normalization^2) := by
  have hprod (i j : ι) :
      shiftedKernel 1 (e i) (e j) * shiftedKernel 1 (e j) (e i) =
        (if i = j then (1/4 : ℝ) else 0) +
          (signedEntry (e i) (e j))^2 / (4*normalization^2) := by
    by_cases hij : i = j
    · subst j
      simp
      <;> ring
    · simp only [shiftedKernel, e.injective.eq_iff, if_neg hij, if_neg (Ne.symm hij),
        zero_add, one_mul, signedEntry_symmetric (e j) (e i)]
      ring
  rw [law_isDPP.variance_windowCount]
  simp_rw [shiftedKernel_diagonal, hprod, Finset.sum_add_distrib, Finset.sum_div]
  simp [div_eq_mul_inv]
  <;> ring

private def tailEmbedding (e : ℕ → Site)
    (hp : Function.Injective (fun n => (e n).1)) (m n : ℕ) : Fin n ↪ Site :=
  ⟨fun i => e (m+i.1), by
    intro i j hij
    apply Fin.ext
    exact Nat.add_left_cancel (hp (congrArg Prod.fst hij))⟩

private theorem tailEmbedding_apply (e : ℕ → Site)
    (hp : Function.Injective (fun n => (e n).1)) (m n : ℕ) (i : Fin n) :
    tailEmbedding e hp m n i = e (m+i.1) := rfl

private theorem tailEmbedding_prime_injective (e : ℕ → Site)
    (hp : Function.Injective (fun n => (e n).1)) (m n : ℕ) :
    Function.Injective (fun i => ((tailEmbedding e hp m n) i).1) := by
  intro i j hij
  apply Fin.ext
  exact Nat.add_left_cancel (hp hij)

private theorem constant_tail_mass_zero (e : ℕ → Site)
    (hp : Function.Injective (fun n => (e n).1)) (m : ℕ) (b : Bool) :
    law {z | ∀ n, m ≤ n → z (e n) = b} = 0 := by
  have hbound (n : ℕ) : law.real {z | ∀ k, m ≤ k → z (e k) = b} ≤ (1/2 : ℝ)^n := by
    have hevent : law.real {z | ∀ i : Fin n, z (e (m+i.1)) = b} = (1/2 : ℝ)^n := by
      cases b
      · simpa [tailEmbedding_apply] using
          distinct_prime_configuration (tailEmbedding e hp m n)
            (tailEmbedding_prime_injective e hp m n) ∅
      · simpa [tailEmbedding_apply] using
          distinct_prime_configuration (tailEmbedding e hp m n)
            (tailEmbedding_prime_injective e hp m n) Finset.univ
    rw [← hevent]
    refine measureReal_mono ?_ (measure_ne_top law _)
    intro z hz i
    exact hz (m+i.1) (Nat.le_add_right _ _)
  have hz : law.real {z | ∀ n, m ≤ n → z (e n) = b} ≤ 0 :=
    ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1)) hbound
  exact (measureReal_eq_zero_iff (measure_ne_top law _)).mp (le_antisymm hz measureReal_nonneg)

private theorem infinite_of_no_constant_tail (z : ℕ → Bool) (b : Bool)
    (h : ∀ m, ¬ ∀ n, m ≤ n → z n = !b) : Set.Infinite {n | z n = b} := by
  intro hf
  obtain ⟨M, hM⟩ := hf.bddAbove
  apply h (M+1)
  intro n hn
  have hne : z n ≠ b := by
    intro he
    have := hM he
    omega
  cases b <;> cases he : z n <;> simp_all

/-- Along any sequence of distinct primes, there are almost surely infinitely
many occupied sites and infinitely many vacant sites. -/
theorem infinitely_many_along_distinct_primes (e : ℕ → Site)
    (hp : Function.Injective (fun n => (e n).1)) :
    ∀ᵐ z ∂law, Set.Infinite {n | z (e n) = true} ∧ Set.Infinite {n | z (e n) = false} := by
  have ht (m : ℕ) : ∀ᵐ z ∂law, ¬ ∀ n, m ≤ n → z (e n) = true :=
    ae_iff.mpr (by simpa only [not_not] using constant_tail_mass_zero e hp m true)
  have hf (m : ℕ) : ∀ᵐ z ∂law, ¬ ∀ n, m ≤ n → z (e n) = false :=
    ae_iff.mpr (by simpa only [not_not] using constant_tail_mass_zero e hp m false)
  filter_upwards [ae_all_iff.mpr ht, ae_all_iff.mpr hf] with z hzt hzf
  constructor
  · exact infinite_of_no_constant_tail (fun n => z (e n)) true hzf
  · exact infinite_of_no_constant_tail (fun n => z (e n)) false hzt

private def nextPrime (p : Prime) : Prime :=
  ⟨Classical.choose (Nat.exists_infinite_primes (p.1+1)),
    (Classical.choose_spec (Nat.exists_infinite_primes (p.1+1))).2⟩

private def primeSequence : ℕ → Prime
  | 0 => ⟨2, Nat.prime_two⟩
  | n+1 => nextPrime (primeSequence n)

private theorem primeSequence_strictMono : StrictMono (fun n => (primeSequence n).1) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
    (Classical.choose_spec (Nat.exists_infinite_primes ((primeSequence n).1+1))).1

/-- The constructed arithmetic law has infinitely many particles and holes
almost surely, proved from independent finite patterns along distinct primes. -/
theorem infinite_particles_and_holes_ae :
    ∀ᵐ z ∂law, Set.Infinite {i | z i = true} ∧ Set.Infinite {i | z i = false} := by
  let e : ℕ → Site := fun n => (primeSequence n, 0)
  have hp : Function.Injective (fun n => (e n).1) := by
    intro i j hij
    exact primeSequence_strictMono.injective (congrArg Subtype.val hij)
  have he : Function.Injective e := fun i j hij => hp (congrArg Prod.fst hij)
  filter_upwards [infinitely_many_along_distinct_primes e hp] with z hz
  have htrue : Set.Infinite (e '' {n | z (e n) = true}) := by
    exact hz.1.image he.injOn
  have hfalse : Set.Infinite (e '' {n | z (e n) = false}) := by
    exact hz.2.image he.injOn
  constructor
  · apply htrue.mono
    rintro i ⟨n, hn, rfl⟩
    exact hn
  · apply hfalse.mono
    rintro i ⟨n, hn, rfl⟩
    exact hn

end RiemannResearch.Probability.DPP.PrimeBlock
