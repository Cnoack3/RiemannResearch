import RiemannResearch.Analysis.RationalAutocorrelationEnergy

/-!
Partial multiplicative shifts are contractions on finite coefficient supports.
Their correlations are exactly the integer-ratio autocorrelation coefficients.
Signed prime-power biases are retained as Hermitian sums before taking norms.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.Fourier

/-- Correlation along the partially defined multiplication-by-k shift. -/
def multiplicativeShiftCorrelation (s : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ n ∈ s.filter (fun n => k * n ∈ s), a (k * n) * starRingEnd ℂ (a n)

theorem rational_ratio_eq_nat_iff {n m k : ℕ} (hm : m ≠ 0) :
    ((n : ℚ) / (m : ℚ) = (k : ℚ)) ↔ n = k * m := by
  rw [div_eq_iff (Nat.cast_ne_zero.mpr hm)]
  norm_cast

/-- Inverting a rational frequency conjugates its exact autocorrelation. -/
theorem rationalAutocorrelation_inv_eq_conj
    (s : Finset ℕ) (a : ℕ → ℂ) (q : ℚ) :
    rationalAutocorrelation s a q⁻¹ = starRingEnd ℂ (rationalAutocorrelation s a q) := by
  classical
  unfold rationalAutocorrelation groupedFrequencyCoefficient
  rw [map_sum]
  apply Finset.sum_bij (fun p hp => (p.2, p.1))
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hmem := Finset.mem_product.mp hp'.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hmem.2, hmem.1⟩, ?_⟩
    change (p.2 : ℚ) / (p.1 : ℚ) = q
    have hratio : (p.1 : ℚ) / (p.2 : ℚ) = q⁻¹ := hp'.2
    rw [← inv_div, hratio, inv_inv]
  · intro p hp r hr heq
    exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hmem := Finset.mem_product.mp hp'.1
    refine ⟨(p.2, p.1), ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hmem.2, hmem.1⟩, ?_⟩
    change (p.2 : ℚ) / (p.1 : ℚ) = q⁻¹
    have hratio : (p.1 : ℚ) / (p.2 : ℚ) = q := hp'.2
    rw [← inv_div, hratio]
  · intro p hp
    simp only [map_mul, starRingEnd_self_apply]
    ring

/-- Exact identification of the aggregated integer-ratio Fourier coefficient. -/
theorem rationalAutocorrelation_nat_eq_shift (s : Finset ℕ) (a : ℕ → ℂ)
    (hs0 : ∀ n ∈ s, n ≠ 0) (k : ℕ) :
    rationalAutocorrelation s a (k : ℚ) = multiplicativeShiftCorrelation s a k := by
  classical
  unfold rationalAutocorrelation groupedFrequencyCoefficient multiplicativeShiftCorrelation
  apply Finset.sum_bij (fun p hp => p.2)
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hmem := Finset.mem_product.mp hp'.1
    have heq := (rational_ratio_eq_nat_iff (hs0 p.2 hmem.2)).mp hp'.2
    exact Finset.mem_filter.mpr ⟨hmem.2, heq ▸ hmem.1⟩
  · intro p hp q hq heq
    have hp' := Finset.mem_filter.mp hp
    have hq' := Finset.mem_filter.mp hq
    have hpn := (rational_ratio_eq_nat_iff (hs0 p.2 (Finset.mem_product.mp hp'.1).2)).mp hp'.2
    have hqn := (rational_ratio_eq_nat_iff (hs0 q.2 (Finset.mem_product.mp hq'.1).2)).mp hq'.2
    exact Prod.ext (by rw [hpn, hqn, heq]) heq
  · intro n hn
    have hn' := Finset.mem_filter.mp hn
    refine ⟨(k * n, n), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hn'.2, hn'.1⟩,
      (rational_ratio_eq_nat_iff (hs0 n hn'.1)).mpr rfl⟩
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have heq := (rational_ratio_eq_nat_iff (hs0 p.2 (Finset.mem_product.mp hp'.1).2)).mp hp'.2
    rw [heq]

/-- A partial injective shift has correlation at most the original energy. -/
theorem multiplicativeShiftCorrelation_norm_le_energy
    (s : Finset ℕ) (a : ℕ → ℂ) {k : ℕ} (hk : k ≠ 0) :
    ‖multiplicativeShiftCorrelation s a k‖ ≤ ∑ n ∈ s, ‖a n‖ ^ 2 := by
  classical
  let T := s.filter (fun n => k * n ∈ s)
  have hfirst : (∑ n ∈ T, ‖a n‖ ^ 2) ≤ ∑ n ∈ s, ‖a n‖ ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n hn hnt => sq_nonneg _)
  have hsub : T.image (fun n => k * n) ⊆ s := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    exact (Finset.mem_filter.mp hn).2
  have hsecond : (∑ n ∈ T, ‖a (k * n)‖ ^ 2) ≤ ∑ n ∈ s, ‖a n‖ ^ 2 := by
    calc
      _ = ∑ m ∈ T.image (fun n => k * n), ‖a m‖ ^ 2 := by
        rw [Finset.sum_image]
        intro n hn m hm hnm
        exact mul_left_cancel₀ hk hnm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn hnt => sq_nonneg _)
  calc
    ‖multiplicativeShiftCorrelation s a k‖ ≤
        ∑ n ∈ T, ‖a (k * n) * starRingEnd ℂ (a n)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ T, (‖a (k * n)‖ ^ 2 + ‖a n‖ ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro n hn
      simp only [norm_mul, Complex.norm_conj]
      nlinarith [sq_nonneg (‖a (k * n)‖ - ‖a n‖)]
    _ = ((∑ n ∈ T, ‖a (k * n)‖ ^ 2) + (∑ n ∈ T, ‖a n‖ ^ 2)) / 2 := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib]
    _ ≤ _ := by linarith only [hfirst, hsecond]

theorem rationalAutocorrelation_nat_norm_le_energy
    (s : Finset ℕ) (a : ℕ → ℂ) (hs0 : ∀ n ∈ s, n ≠ 0) {k : ℕ} (hk : k ≠ 0) :
    ‖rationalAutocorrelation s a (k : ℚ)‖ ≤ ∑ n ∈ s, ‖a n‖ ^ 2 := by
  rw [rationalAutocorrelation_nat_eq_shift s a hs0 k]
  exact multiplicativeShiftCorrelation_norm_le_energy s a hk

/-- A finite signed Hermitian arithmetic bias, with no absolute values in its definition. -/
def multiplicativeShiftBias (s : Finset ℕ) (a : ℕ → ℂ) (K : Finset ℕ)
    (α : ℕ → ℝ) : ℂ :=
  ∑ k ∈ K, (α k : ℂ) * (multiplicativeShiftCorrelation s a k +
    starRingEnd ℂ (multiplicativeShiftCorrelation s a k))

/-- Exact identification with the positive and reciprocal rational frequencies. -/
theorem multiplicativeShiftBias_eq_rationalAutocorrelations
    (s : Finset ℕ) (a : ℕ → ℂ) (K : Finset ℕ) (α : ℕ → ℝ)
    (hs0 : ∀ n ∈ s, n ≠ 0) :
    multiplicativeShiftBias s a K α =
      ∑ k ∈ K, (α k : ℂ) * (rationalAutocorrelation s a (k : ℚ) +
        rationalAutocorrelation s a (k : ℚ)⁻¹) := by
  unfold multiplicativeShiftBias
  apply Finset.sum_congr rfl
  intro k hk
  rw [rationalAutocorrelation_inv_eq_conj, rationalAutocorrelation_nat_eq_shift s a hs0 k]

/-- The signed bias is exactly twice the real part of the weighted correlations. -/
theorem multiplicativeShiftBias_eq_real
    (s : Finset ℕ) (a : ℕ → ℂ) (K : Finset ℕ) (α : ℕ → ℝ) :
    multiplicativeShiftBias s a K α =
      ((2 * ∑ k ∈ K, α k * (multiplicativeShiftCorrelation s a k).re : ℝ) : ℂ) := by
  unfold multiplicativeShiftBias
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Complex.ext <;> simp <;> ring

/-- Width-dependent finite bias control through the actual partial shifts. -/
theorem multiplicativeShiftBias_norm_le
    (s : Finset ℕ) (a : ℕ → ℂ) (K : Finset ℕ) (α : ℕ → ℝ)
    (hK : ∀ k ∈ K, k ≠ 0) :
    ‖multiplicativeShiftBias s a K α‖ ≤
      2 * (∑ k ∈ K, |α k|) * (∑ n ∈ s, ‖a n‖ ^ 2) := by
  unfold multiplicativeShiftBias
  calc
    _ ≤ ∑ k ∈ K, ‖(α k : ℂ) * (multiplicativeShiftCorrelation s a k +
        starRingEnd ℂ (multiplicativeShiftCorrelation s a k))‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ K, |α k| * (2 * ∑ n ∈ s, ‖a n‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have h := norm_add_le (multiplicativeShiftCorrelation s a k)
        (starRingEnd ℂ (multiplicativeShiftCorrelation s a k))
      simp only [Complex.norm_conj] at h
      have hc := multiplicativeShiftCorrelation_norm_le_energy s a (hK k hk)
      linarith only [h, hc]
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- A logarithmic band has no shift correlation beyond its own width. -/
theorem multiplicativeShiftCorrelation_eq_zero_of_log_gt
    (s : Finset ℕ) (a : ℕ → ℂ) (L U : ℝ) (hs0 : ∀ n ∈ s, n ≠ 0)
    (hu : ∀ n ∈ s, L ≤ Real.log n ∧ Real.log n ≤ U)
    {k : ℕ} (hk : k ≠ 0) (hwide : U - L < Real.log k) :
    multiplicativeShiftCorrelation s a k = 0 := by
  unfold multiplicativeShiftCorrelation
  apply Finset.sum_eq_zero
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  have hlog : Real.log (k * n : ℕ) = Real.log k + Real.log n := by
    rw [Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hk)
      (Nat.cast_ne_zero.mpr (hs0 n hn'.1))]
  exfalso
  linarith [(hu n hn'.1).1, (hu (k * n) hn'.2).2]

/-- Exact width truncation of the signed bias. -/
theorem multiplicativeShiftBias_eq_width_filtered
    (s : Finset ℕ) (a : ℕ → ℂ) (K : Finset ℕ) (α : ℕ → ℝ)
    (L U : ℝ) (hs0 : ∀ n ∈ s, n ≠ 0)
    (hu : ∀ n ∈ s, L ≤ Real.log n ∧ Real.log n ≤ U)
    (hK : ∀ k ∈ K, k ≠ 0) :
    multiplicativeShiftBias s a K α =
      multiplicativeShiftBias s a (K.filter (fun k : ℕ => Real.log k ≤ U - L)) α := by
  unfold multiplicativeShiftBias
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : Real.log k ≤ U - L
  · simp only [if_pos h]
  · rw [multiplicativeShiftCorrelation_eq_zero_of_log_gt s a L U hs0 hu (hK k hk)
      (lt_of_not_ge h)]
    simp

/-- The covariance budget depends on band width, not the largest support integer. -/
theorem multiplicativeShiftBias_norm_le_width_filtered
    (s : Finset ℕ) (a : ℕ → ℂ) (K : Finset ℕ) (α : ℕ → ℝ)
    (L U : ℝ) (hs0 : ∀ n ∈ s, n ≠ 0)
    (hu : ∀ n ∈ s, L ≤ Real.log n ∧ Real.log n ≤ U)
    (hK : ∀ k ∈ K, k ≠ 0) :
    ‖multiplicativeShiftBias s a K α‖ ≤
      2 * (∑ k ∈ K.filter (fun k : ℕ => Real.log k ≤ U - L), |α k|) *
        (∑ n ∈ s, ‖a n‖ ^ 2) := by
  rw [multiplicativeShiftBias_eq_width_filtered s a K α L U hs0 hu hK]
  exact multiplicativeShiftBias_norm_le s a _ α
    (fun k hk => hK k (Finset.mem_filter.mp hk).1)

end RiemannResearch.Fourier
