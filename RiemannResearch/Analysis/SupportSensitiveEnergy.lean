import RiemannResearch.Analysis.RationalAutocorrelationEnergy

/-!
Multiplicity-sensitive finite energy budgets without any prime-degree restriction.
These retain support geometry and therefore apply beyond bounded-degree blocks.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.Fourier

/-- The exact diagonal subtraction for every finite nonzero integer support. -/
theorem rationalAutocorrelation_offDiagonal_energy_eq
    (s : Finset ℕ) (a : ℕ → ℂ) (hs0 : ∀ n ∈ s, n ≠ 0) :
    (∑ q ∈ (rationalFrequencySupport s).erase 1, ‖rationalAutocorrelation s a q‖ ^ 2) =
      (∑ k ∈ productFrequencySupport s, ‖productCoefficient s a k‖ ^ 2) -
        (∑ n ∈ s, ‖a n‖ ^ 2) ^ 2 := by
  classical
  by_cases he : s = ∅
  · simp [he, rationalFrequencySupport, productFrequencySupport]
  · obtain ⟨n, hn⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hq : (1 : ℚ) ∈ rationalFrequencySupport s := by
      apply Finset.mem_image.mpr
      refine ⟨(n, n), Finset.mem_product.mpr ⟨hn, hn⟩, ?_⟩
      exact div_self (Nat.cast_ne_zero.mpr (hs0 n hn))
    have hsplit := Finset.sum_erase_add (rationalFrequencySupport s)
      (fun q => ‖rationalAutocorrelation s a q‖ ^ 2) hq
    have hE : 0 ≤ ∑ n ∈ s, ‖a n‖ ^ 2 := Finset.sum_nonneg fun n hn => sq_nonneg _
    rw [rationalAutocorrelation_one s a hs0] at hsplit
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE] at hsplit
    rw [rationalAutocorrelation_energy_eq_product_energy s a hs0] at hsplit
    linarith only [hsplit]

/-- Actual product-fiber multiplicities replace the worst-case degree constant. -/
theorem sum_productCoefficient_sq_le_fiberWeightedEnergy
    (s : Finset ℕ) (a : ℕ → ℂ) :
    (∑ k ∈ productFrequencySupport s, ‖productCoefficient s a k‖ ^ 2) ≤
      ∑ p ∈ s ×ˢ s,
        (((s ×ˢ s).filter (fun q => q.1 * q.2 = p.1 * p.2)).card : ℝ) *
          ‖a p.1 * a p.2‖ ^ 2 := by
  classical
  calc
    _ ≤ ∑ k ∈ productFrequencySupport s,
        (((s ×ˢ s).filter (fun p => p.1 * p.2 = k)).card : ℝ) *
          ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 * p.2 = k), ‖a p.1 * a p.2‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      exact RiemannResearch.Analysis.PrimeMoment.norm_sum_sq_le_card_mul_sum_norm_sq _ _
    _ = ∑ k ∈ productFrequencySupport s,
        ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 * p.2 = k),
          (((s ×ˢ s).filter (fun q => q.1 * q.2 = p.1 * p.2)).card : ℝ) *
            ‖a p.1 * a p.2‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩) _

/-- Actual multiplicative energy controls the quartic cost for unrestricted support. -/
theorem rationalAutocorrelation_fourth_le_actualProductEnergy
    (s : Finset ℕ) (a : ℕ → ℂ) (L U : ℝ)
    (hs0 : ∀ n ∈ s, n ≠ 0)
    (hu : ∀ n ∈ s, L ≤ Real.log n ∧ Real.log n ≤ U) :
    (∑ q ∈ (rationalFrequencySupport s).erase 1,
      ‖rationalAutocorrelation s a q‖ ^ 2 * Real.log (q : ℝ) ^ 4) ≤
      (U - L) ^ 4 *
        ((∑ k ∈ productFrequencySupport s, ‖productCoefficient s a k‖ ^ 2) -
          (∑ n ∈ s, ‖a n‖ ^ 2) ^ 2) := by
  calc
    _ ≤ ∑ q ∈ (rationalFrequencySupport s).erase 1,
        ‖rationalAutocorrelation s a q‖ ^ 2 * (U - L) ^ 4 := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left
        (rationalFrequency_log_fourth_le s L U hs0 hu (Finset.mem_of_mem_erase hq))
        (sq_nonneg _)
    _ = (U - L) ^ 4 * ∑ q ∈ (rationalFrequencySupport s).erase 1,
        ‖rationalAutocorrelation s a q‖ ^ 2 := by rw [← Finset.sum_mul]; ring
    _ = _ := by rw [rationalAutocorrelation_offDiagonal_energy_eq s a hs0]

end RiemannResearch.Fourier
