import RiemannResearch.Analysis.RationalAutocorrelationEnergy

/-! Exact second-moment dispersion for aggregated prime autocorrelations. -/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.Fourier

/-- Exact quadratic rational-frequency energy on prime supports. -/
theorem prime_rationalAutocorrelation_second_moment
    (s : Finset ℕ) (a : ℕ → ℂ) (hs : ∀ n ∈ s, Nat.Prime n) :
    (∑ q ∈ rationalFrequencySupport s,
      ‖rationalAutocorrelation s a q‖ ^ 2 * Real.log (q : ℝ) ^ 2) =
      weightedFrequencySpread s (fun n => ‖a n‖ ^ 2) (fun n => Real.log n) := by
  classical
  have hinj : ∀ p ∈ s ×ˢ s, ∀ q ∈ s ×ˢ s,
      (p.1 : ℚ) / (p.2 : ℚ) = (q.1 : ℚ) / (q.2 : ℚ) →
      Real.log (((p.1 : ℚ) / (p.2 : ℚ) : ℚ) : ℝ) ^ 2 ≠ 0 → p = q := by
    intro p hp q hq heq hw
    have hp' := Finset.mem_product.mp hp
    have hq' := Finset.mem_product.mp hq
    have hne : p.1 ≠ p.2 := by
      intro h
      apply hw
      simp [h, (hs p.2 hp'.2).ne_zero]
    obtain ⟨h1, h2⟩ := prime_ratio_unique (hs _ hp'.1) (hs _ hp'.2)
      (hs _ hq'.1) (hs _ hq'.2) hne heq
    exact Prod.ext h1 h2
  have h := sum_groupedFrequencyCoefficient_norm_sq_mul_eq (s ×ˢ s)
    (fun p => (p.1 : ℚ) / (p.2 : ℚ)) (fun p => a p.1 * starRingEnd ℂ (a p.2))
    (rationalFrequencySupport s) (fun q => Real.log (q : ℝ) ^ 2)
    (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩) hinj
  change (∑ q ∈ rationalFrequencySupport s,
    ‖groupedFrequencyCoefficient (s ×ˢ s) (fun p => (p.1 : ℚ) / (p.2 : ℚ))
      (fun p => a p.1 * starRingEnd ℂ (a p.2)) q‖ ^ 2 * Real.log (q : ℝ) ^ 2) = _
  rw [h]
  simp only [weightedFrequencySpread, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hs n hn).ne_zero
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hs m hm).ne_zero
  simp [Rat.cast_div, Real.log_div hn0 hm0, mul_pow]

/-- Centering eliminates the first moment and gives J₂ = 2 E V. -/
theorem prime_rationalAutocorrelation_second_eq_centered
    (s : Finset ℕ) (a : ℕ → ℂ) (hs : ∀ n ∈ s, Nat.Prime n)
    (c : ℝ) (hc : (∑ n ∈ s, ‖a n‖ ^ 2 * (Real.log n - c)) = 0) :
    (∑ q ∈ rationalFrequencySupport s,
      ‖rationalAutocorrelation s a q‖ ^ 2 * Real.log (q : ℝ) ^ 2) =
      2 * (∑ n ∈ s, ‖a n‖ ^ 2) * (∑ n ∈ s, ‖a n‖ ^ 2 * (Real.log n - c) ^ 2) := by
  rw [prime_rationalAutocorrelation_second_moment s a hs,
    weightedFrequencySpread_eq_centered s _ _ c, hc]
  ring

end RiemannResearch.Fourier
