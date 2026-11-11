import RiemannResearch.Analysis.BoundedPrimeDegreeEnergy

/-!
Bilinear multiplicative-energy bounds with separate prime-factor degrees.
This is the graded extension of the FRZ central-binomial estimate.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.Fourier

theorem paddedPrimeFactors_add_two_bounds {r s n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (hnd : primeDegree n ≤ r) (hmd : primeDegree m ≤ s) :
    paddedPrimeFactors r n + paddedPrimeFactors s m =
      paddedPrimeFactors (r + s) (n * m) := by
  have hp : ((n * m).primeFactorsList : Multiset ℕ) =
      (n.primeFactorsList : Multiset ℕ) + (m.primeFactorsList : Multiset ℕ) := by
    exact Multiset.coe_eq_coe.mpr (Nat.perm_primeFactorsList_mul hn hm)
  have hd : (r - primeDegree n) + (s - primeDegree m) =
      r + s - primeDegree (n * m) := by
    rw [primeDegree_mul hn hm]
    omega
  simp only [paddedPrimeFactors, hp]
  calc
    _ = ((n.primeFactorsList : Multiset ℕ) + (m.primeFactorsList : Multiset ℕ)) +
        (Multiset.replicate (r - primeDegree n) 1 +
         Multiset.replicate (s - primeDegree m) 1) := by ac_rfl
    _ = _ := by rw [← Multiset.replicate_add, hd]

theorem mixedPrimeDegree_product_fiber_card_le
    (s t : Finset ℕ) (d e k : ℕ)
    (hs0 : ∀ n ∈ s, n ≠ 0) (ht0 : ∀ n ∈ t, n ≠ 0)
    (hsd : ∀ n ∈ s, primeDegree n ≤ d) (htd : ∀ n ∈ t, primeDegree n ≤ e) :
    ((s ×ˢ t).filter (fun p => p.1 * p.2 = k)).card ≤ (d + e).choose d := by
  classical
  let F := (s ×ˢ t).filter (fun p => p.1 * p.2 = k)
  change F.card ≤ _
  by_cases hF : F.Nonempty
  · obtain ⟨p, hp⟩ := hF
    have hp' := Finset.mem_filter.mp hp
    have hp1 := (Finset.mem_product.mp hp'.1).1
    have hp2 := (Finset.mem_product.mp hp'.1).2
    have hk : primeDegree k ≤ d + e := by
      rw [← hp'.2, primeDegree_mul (hs0 _ hp1) (ht0 _ hp2)]
      have := hsd _ hp1
      have := htd _ hp2
      omega
    let P := paddedPrimeFactors (d + e) k
    have hmap : Set.MapsTo (fun q : ℕ × ℕ => paddedPrimeFactors d q.1)
        (↑F : Set (ℕ × ℕ)) (↑(P.powersetCard d).toFinset : Set (Multiset ℕ)) := by
      intro q hq
      have hq' := Finset.mem_filter.mp hq
      have hq1 := (Finset.mem_product.mp hq'.1).1
      have hq2 := (Finset.mem_product.mp hq'.1).2
      apply Multiset.mem_toFinset.mpr
      apply Multiset.mem_powersetCard.mpr
      constructor
      · have heq := paddedPrimeFactors_add_two_bounds (hs0 _ hq1) (ht0 _ hq2) (hsd _ hq1) (htd _ hq2)
        rw [hq'.2] at heq
        change paddedPrimeFactors d q.1 ≤ paddedPrimeFactors (d + e) k
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
      _ = (d + e).choose d := by
        rw [Multiset.card_powersetCard, paddedPrimeFactors_card hk]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hF]


/-- Coefficient of an integer frequency in a product of two Dirichlet polynomials. -/
def mixedProductCoefficient (s t : Finset ℕ) (a b : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ p ∈ (s ×ˢ t).filter (fun p => p.1 * p.2 = k), a p.1 * b p.2

theorem mixedPrimeDegree_mixedProductCoefficient_sq_le
    (s t : Finset ℕ) (a b : ℕ → ℂ) (d e k : ℕ) (hs0 : ∀ n ∈ s, n ≠ 0) (ht0 : ∀ n ∈ t, n ≠ 0)
    (hsd : ∀ n ∈ s, primeDegree n ≤ d) (htd : ∀ n ∈ t, primeDegree n ≤ e) :
    ‖mixedProductCoefficient s t a b k‖ ^ 2 ≤ ((d + e).choose d : ℝ) *
      ∑ p ∈ (s ×ˢ t).filter (fun p => p.1 * p.2 = k), ‖a p.1 * b p.2‖ ^ 2 := by
  refine (RiemannResearch.Analysis.PrimeMoment.norm_sum_sq_le_card_mul_sum_norm_sq _ _).trans ?_
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast mixedPrimeDegree_product_fiber_card_le s t d e k hs0 ht0 hsd htd
  · exact Finset.sum_nonneg fun p hp => sq_nonneg _

theorem mixedPrimeDegree_sum_mixedProductCoefficient_sq_le
    (s t : Finset ℕ) (a b : ℕ → ℂ) (d e : ℕ) (K : Finset ℕ)
    (hs0 : ∀ n ∈ s, n ≠ 0) (ht0 : ∀ n ∈ t, n ≠ 0)
    (hsd : ∀ n ∈ s, primeDegree n ≤ d) (htd : ∀ n ∈ t, primeDegree n ≤ e) :
    ∑ k ∈ K, ‖mixedProductCoefficient s t a b k‖ ^ 2 ≤
      ((d + e).choose d : ℝ) * ((∑ n ∈ s, ‖a n‖ ^ 2) * (∑ n ∈ t, ‖b n‖ ^ 2)) := by
  have hfiber : (∑ k ∈ K, ∑ p ∈ (s ×ˢ t).filter (fun p => p.1 * p.2 = k),
      ‖a p.1 * b p.2‖ ^ 2) ≤ ∑ p ∈ s ×ˢ t, ‖a p.1 * b p.2‖ ^ 2 := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro p hp
    by_cases h : p.1 * p.2 ∈ K
    · simp [eq_comm, h]
    · simpa [eq_comm, h] using sq_nonneg (‖a p.1 * b p.2‖)
  have henergy : (∑ p ∈ s ×ˢ t, ‖a p.1 * b p.2‖ ^ 2) =
      ((∑ n ∈ s, ‖a n‖ ^ 2) * (∑ n ∈ t, ‖b n‖ ^ 2)) := by
    simp_rw [Finset.sum_product, norm_mul, mul_pow]
    rw [← Finset.sum_mul_sum]
  calc
    ∑ k ∈ K, ‖mixedProductCoefficient s t a b k‖ ^ 2 ≤
        ∑ k ∈ K, ((d + e).choose d : ℝ) *
          ∑ p ∈ (s ×ˢ t).filter (fun p => p.1 * p.2 = k), ‖a p.1 * b p.2‖ ^ 2 :=
      Finset.sum_le_sum fun k hk => mixedPrimeDegree_mixedProductCoefficient_sq_le s t a b d e k hs0 ht0 hsd htd
    _ = ((d + e).choose d : ℝ) * (∑ k ∈ K,
          ∑ p ∈ (s ×ˢ t).filter (fun p => p.1 * p.2 = k), ‖a p.1 * b p.2‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ ((d + e).choose d : ℝ) * ∑ p ∈ s ×ˢ t, ‖a p.1 * b p.2‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hfiber (Nat.cast_nonneg _)
    _ = _ := by rw [henergy]


/-- Different total degrees have disjoint product-frequency supports. -/
theorem mixedProductCoefficient_eq_zero_of_primeDegree_ne
    (s t : Finset ℕ) (a b : ℕ → ℂ) (d e k : ℕ)
    (hs0 : ∀ n ∈ s, n ≠ 0) (ht0 : ∀ n ∈ t, n ≠ 0)
    (hsd : ∀ n ∈ s, primeDegree n = d) (htd : ∀ n ∈ t, primeDegree n = e)
    (hk : primeDegree k ≠ d + e) : mixedProductCoefficient s t a b k = 0 := by
  unfold mixedProductCoefficient
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hp1 := (Finset.mem_product.mp hp'.1).1
  have hp2 := (Finset.mem_product.mp hp'.1).2
  exfalso
  apply hk
  rw [← hp'.2, primeDegree_mul (hs0 _ hp1) (ht0 _ hp2), hsd _ hp1, htd _ hp2]

end RiemannResearch.Fourier
