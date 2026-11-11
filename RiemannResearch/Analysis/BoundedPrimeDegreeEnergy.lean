import RiemannResearch.Analysis.PrimeMomentDiagonal
import Mathlib.Data.Multiset.Powerset
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Tactic.Ring

/-!
Finite multiplicative-energy bounds for integers with bounded prime-factor degree.
The counting argument pads the prime-factor multiset with ones and injects each
ordered factorization into its d-element submultisets. Repeated prime factors do
not require squarefreeness. This formalizes and strengthens FRZ, Section 4.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.Fourier

/-- Number of prime factors with multiplicity, including degree zero at 0 and 1.
All multiplicative lemmas below explicitly exclude zero. -/
def primeDegree (n : ℕ) : ℕ := n.primeFactorsList.length

theorem primeDegree_mul {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    primeDegree (n * m) = primeDegree n + primeDegree m := by
  simpa [primeDegree] using (Nat.perm_primeFactorsList_mul hn hm).length_eq

theorem eq_of_dvd_of_primeDegree_eq {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (hdiv : n ∣ m) (hdeg : primeDegree n = primeDegree m) : n = m := by
  have heq : n.primeFactorsList = m.primeFactorsList :=
    (Nat.primeFactorsList_sublist_of_dvd hdiv hm).eq_of_length (by simpa [primeDegree] using hdeg)
  simpa [Nat.prod_primeFactorsList hn, Nat.prod_primeFactorsList hm] using
    congrArg List.prod heq

/-- Prime occurrences padded with units to have the indicated total degree. -/
def paddedPrimeFactors (d n : ℕ) : Multiset ℕ :=
  (n.primeFactorsList : Multiset ℕ) + Multiset.replicate (d - primeDegree n) 1

theorem paddedPrimeFactors_card {d n : ℕ} (h : primeDegree n ≤ d) :
    (paddedPrimeFactors d n).card = d := by
  simp [paddedPrimeFactors, primeDegree] at h ⊢
  omega

theorem paddedPrimeFactors_prod (d : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (paddedPrimeFactors d n).prod = n := by
  simp [paddedPrimeFactors, Nat.prod_primeFactorsList hn]

theorem paddedPrimeFactors_add {d n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (hnd : primeDegree n ≤ d) (hmd : primeDegree m ≤ d) :
    paddedPrimeFactors d n + paddedPrimeFactors d m =
      paddedPrimeFactors (2 * d) (n * m) := by
  have hp : ((n * m).primeFactorsList : Multiset ℕ) =
      (n.primeFactorsList : Multiset ℕ) + (m.primeFactorsList : Multiset ℕ) := by
    exact Multiset.coe_eq_coe.mpr (Nat.perm_primeFactorsList_mul hn hm)
  have hd : (d - primeDegree n) + (d - primeDegree m) =
      2 * d - primeDegree (n * m) := by
    rw [primeDegree_mul hn hm]
    omega
  simp only [paddedPrimeFactors, hp]
  calc
    _ = ((n.primeFactorsList : Multiset ℕ) + (m.primeFactorsList : Multiset ℕ)) +
        (Multiset.replicate (d - primeDegree n) 1 +
         Multiset.replicate (d - primeDegree m) 1) := by ac_rfl
    _ = _ := by rw [← Multiset.replicate_add, hd]

/-- A central-binomial count valid for Ω(n) ≤ d, not just homogeneous support. -/
theorem boundedPrimeDegree_product_fiber_card_le
    (s : Finset ℕ) (d k : ℕ) (hs0 : ∀ n ∈ s, n ≠ 0)
    (hsd : ∀ n ∈ s, primeDegree n ≤ d) :
    ((s ×ˢ s).filter (fun p => p.1 * p.2 = k)).card ≤ (2 * d).choose d := by
  classical
  let F := (s ×ˢ s).filter (fun p => p.1 * p.2 = k)
  change F.card ≤ _
  by_cases hF : F.Nonempty
  · obtain ⟨p, hp⟩ := hF
    have hp' := Finset.mem_filter.mp hp
    have hp1 := (Finset.mem_product.mp hp'.1).1
    have hp2 := (Finset.mem_product.mp hp'.1).2
    have hk : primeDegree k ≤ 2 * d := by
      rw [← hp'.2, primeDegree_mul (hs0 _ hp1) (hs0 _ hp2)]
      have := hsd _ hp1
      have := hsd _ hp2
      omega
    let P := paddedPrimeFactors (2 * d) k
    have hmap : Set.MapsTo (fun q : ℕ × ℕ => paddedPrimeFactors d q.1)
        (↑F : Set (ℕ × ℕ)) (↑(P.powersetCard d).toFinset : Set (Multiset ℕ)) := by
      intro q hq
      have hq' := Finset.mem_filter.mp hq
      have hq1 := (Finset.mem_product.mp hq'.1).1
      have hq2 := (Finset.mem_product.mp hq'.1).2
      apply Multiset.mem_toFinset.mpr
      apply Multiset.mem_powersetCard.mpr
      constructor
      · have heq := paddedPrimeFactors_add (hs0 _ hq1) (hs0 _ hq2) (hsd _ hq1) (hsd _ hq2)
        rw [hq'.2] at heq
        change paddedPrimeFactors d q.1 ≤ paddedPrimeFactors (2 * d) k
        rw [← heq]
        exact le_add_right le_rfl
      · exact paddedPrimeFactors_card (hsd _ hq1)
    have hinj : Set.InjOn (fun q : ℕ × ℕ => paddedPrimeFactors d q.1) (↑F : Set (ℕ × ℕ)) := by
      intro q hq r hr heq
      have hq' := Finset.mem_filter.mp hq
      have hr' := Finset.mem_filter.mp hr
      have hq1 := (Finset.mem_product.mp hq'.1).1
      have hr1 := (Finset.mem_product.mp hr'.1).1
      have hfirst : q.1 = r.1 := by
        simpa [paddedPrimeFactors_prod d (hs0 _ hq1),
          paddedPrimeFactors_prod d (hs0 _ hr1)] using congrArg Multiset.prod heq
      have hsecond : q.2 = r.2 := by
        apply mul_left_cancel₀ (hs0 _ hq1)
        rw [hq'.2, hfirst, hr'.2]
      exact Prod.ext hfirst hsecond
    calc
      F.card ≤ (P.powersetCard d).toFinset.card :=
        Finset.card_le_card_of_injOn _ hmap hinj
      _ ≤ (P.powersetCard d).card := Multiset.toFinset_card_le _
      _ = (2 * d).choose d := by
        rw [Multiset.card_powersetCard, paddedPrimeFactors_card hk]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hF]

/-- Coefficient of an integer frequency in the square of a Dirichlet polynomial. -/
def productCoefficient (s : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 * p.2 = k), a p.1 * a p.2

theorem boundedPrimeDegree_productCoefficient_sq_le
    (s : Finset ℕ) (a : ℕ → ℂ) (d k : ℕ) (hs0 : ∀ n ∈ s, n ≠ 0)
    (hsd : ∀ n ∈ s, primeDegree n ≤ d) :
    ‖productCoefficient s a k‖ ^ 2 ≤ ((2 * d).choose d : ℝ) *
      ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 * p.2 = k), ‖a p.1 * a p.2‖ ^ 2 := by
  refine (RiemannResearch.Analysis.PrimeMoment.norm_sum_sq_le_card_mul_sum_norm_sq _ _).trans ?_
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast boundedPrimeDegree_product_fiber_card_le s d k hs0 hsd
  · exact Finset.sum_nonneg fun p hp => sq_nonneg _

theorem boundedPrimeDegree_sum_productCoefficient_sq_le
    (s : Finset ℕ) (a : ℕ → ℂ) (d : ℕ) (K : Finset ℕ)
    (hs0 : ∀ n ∈ s, n ≠ 0) (hsd : ∀ n ∈ s, primeDegree n ≤ d) :
    ∑ k ∈ K, ‖productCoefficient s a k‖ ^ 2 ≤
      ((2 * d).choose d : ℝ) * (∑ n ∈ s, ‖a n‖ ^ 2) ^ 2 := by
  have hfiber : (∑ k ∈ K, ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 * p.2 = k),
      ‖a p.1 * a p.2‖ ^ 2) ≤ ∑ p ∈ s ×ˢ s, ‖a p.1 * a p.2‖ ^ 2 := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro p hp
    by_cases h : p.1 * p.2 ∈ K
    · simp [eq_comm, h]
    · simpa [eq_comm, h] using sq_nonneg (‖a p.1 * a p.2‖)
  have henergy : (∑ p ∈ s ×ˢ s, ‖a p.1 * a p.2‖ ^ 2) =
      (∑ n ∈ s, ‖a n‖ ^ 2) ^ 2 := by
    simp_rw [Finset.sum_product, norm_mul, mul_pow]
    rw [← Finset.sum_mul_sum, pow_two]
  calc
    ∑ k ∈ K, ‖productCoefficient s a k‖ ^ 2 ≤
        ∑ k ∈ K, ((2 * d).choose d : ℝ) *
          ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 * p.2 = k), ‖a p.1 * a p.2‖ ^ 2 :=
      Finset.sum_le_sum fun k hk => boundedPrimeDegree_productCoefficient_sq_le s a d k hs0 hsd
    _ = ((2 * d).choose d : ℝ) * (∑ k ∈ K,
          ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 * p.2 = k), ‖a p.1 * a p.2‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ ((2 * d).choose d : ℝ) * ∑ p ∈ s ×ˢ s, ‖a p.1 * a p.2‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hfiber (Nat.cast_nonneg _)
    _ = _ := by rw [henergy]

end RiemannResearch.Fourier
