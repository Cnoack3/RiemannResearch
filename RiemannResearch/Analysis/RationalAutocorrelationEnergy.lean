import RiemannResearch.Analysis.BoundedPrimeDegreeEnergy
import RiemannResearch.Analysis.QuarticFrequencySpread
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
Exact signed aggregation of rational frequencies, followed by multiplicative
energy estimates. The autocorrelation coefficients are combined before norms.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.Fourier

/-- A coefficient after combining all occurrences of the same frequency. -/
def groupedFrequencyCoefficient {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) (a : α → ℂ) (b : β) : ℂ :=
  ∑ i ∈ s.filter (fun i => f i = b), a i

/-- Exact regrouping of a finite Fourier polynomial. -/
theorem sum_groupedFrequencyCoefficient_mul {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) (a : α → ℂ) (F : Finset β)
    (hF : ∀ i ∈ s, f i ∈ F) (χ : β → ℂ) :
    (∑ b ∈ F, groupedFrequencyCoefficient s f a b * χ b) =
      ∑ i ∈ s, a i * χ (f i) := by
  classical
  simp_rw [groupedFrequencyCoefficient, Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp [eq_comm, hF i hi]

/-- Exact collision expansion. No absolute values are inserted in the inner sum. -/
theorem sum_groupedFrequencyCoefficient_mul_conj {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) (a : α → ℂ) (F : Finset β)
    (hF : ∀ i ∈ s, f i ∈ F) :
    (∑ b ∈ F, groupedFrequencyCoefficient s f a b *
      starRingEnd ℂ (groupedFrequencyCoefficient s f a b)) =
    ∑ i ∈ s, ∑ j ∈ s, if f i = f j then a i * starRingEnd ℂ (a j) else 0 := by
  classical
  calc
    _ = ∑ b ∈ F, ∑ i ∈ s.filter (fun i => f i = b),
        a i * starRingEnd ℂ (groupedFrequencyCoefficient s f a (f i)) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [groupedFrequencyCoefficient, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
      rfl
    _ = ∑ i ∈ s, a i * starRingEnd ℂ (groupedFrequencyCoefficient s f a (f i)) :=
      Finset.sum_fiberwise_of_maps_to hF _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [groupedFrequencyCoefficient, map_sum, Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : f i = f j
      · simp only [if_pos h, if_pos h.symm]
      · simp only [if_neg h, if_neg (Ne.symm h), map_zero, mul_zero]

/-- Rational autocorrelation, including the diagonal coefficient at ratio 1. -/
def rationalAutocorrelation (s : Finset ℕ) (a : ℕ → ℂ) (q : ℚ) : ℂ :=
  groupedFrequencyCoefficient (s ×ˢ s) (fun p => (p.1 : ℚ) / (p.2 : ℚ))
    (fun p => a p.1 * starRingEnd ℂ (a p.2)) q

/-- Finite set of all rational frequencies actually present in a support. -/
def rationalFrequencySupport (s : Finset ℕ) : Finset ℚ :=
  (s ×ˢ s).image (fun p => (p.1 : ℚ) / (p.2 : ℚ))

/-- Finite set of all product frequencies of a support. -/
def productFrequencySupport (s : Finset ℕ) : Finset ℕ :=
  (s ×ˢ s).image (fun p => p.1 * p.2)

theorem rational_ratio_eq_iff_cross_mul {n m r t : ℕ} (hm : m ≠ 0) (ht : t ≠ 0) :
    ((n : ℚ) / (m : ℚ) = (r : ℚ) / (t : ℚ)) ↔ n * t = r * m := by
  rw [div_eq_div_iff (Nat.cast_ne_zero.mpr hm) (Nat.cast_ne_zero.mpr ht)]
  norm_cast

/-- The exact equality of rational autocorrelation energy and product energy. -/
theorem rationalAutocorrelation_energy_eq_product_energy
    (s : Finset ℕ) (a : ℕ → ℂ) (hs0 : ∀ n ∈ s, n ≠ 0) :
    (∑ q ∈ rationalFrequencySupport s, ‖rationalAutocorrelation s a q‖ ^ 2) =
      ∑ k ∈ productFrequencySupport s, ‖productCoefficient s a k‖ ^ 2 := by
  classical
  have hratio := sum_groupedFrequencyCoefficient_mul_conj (s ×ˢ s)
    (fun p => (p.1 : ℚ) / (p.2 : ℚ)) (fun p => a p.1 * starRingEnd ℂ (a p.2))
    (rationalFrequencySupport s) (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  have hprod := sum_groupedFrequencyCoefficient_mul_conj (s ×ˢ s)
    (fun p => p.1 * p.2) (fun p => a p.1 * a p.2)
    (productFrequencySupport s) (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  have hcollision :
      (∑ p ∈ s ×ˢ s, ∑ q ∈ s ×ˢ s,
        if (p.1 : ℚ) / (p.2 : ℚ) = (q.1 : ℚ) / (q.2 : ℚ)
        then (a p.1 * starRingEnd ℂ (a p.2)) *
          starRingEnd ℂ (a q.1 * starRingEnd ℂ (a q.2)) else 0) =
      ∑ p ∈ s ×ˢ s, ∑ q ∈ s ×ˢ s,
        if p.1 * p.2 = q.1 * q.2 then (a p.1 * a p.2) *
          starRingEnd ℂ (a q.1 * a q.2) else 0 := by
    simp only [Finset.sum_product]
    calc
      _ = ∑ n ∈ s, ∑ r ∈ s, ∑ m ∈ s, ∑ t ∈ s,
          if (n : ℚ) / (m : ℚ) = (r : ℚ) / (t : ℚ)
          then (a n * starRingEnd ℂ (a m)) *
            starRingEnd ℂ (a r * starRingEnd ℂ (a t)) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        exact Finset.sum_comm
      _ = ∑ n ∈ s, ∑ r ∈ s, ∑ t ∈ s, ∑ m ∈ s,
          if (n : ℚ) / (m : ℚ) = (r : ℚ) / (t : ℚ)
          then (a n * starRingEnd ℂ (a m)) *
            starRingEnd ℂ (a r * starRingEnd ℂ (a t)) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        apply Finset.sum_congr rfl
        intro r hr
        exact Finset.sum_comm
      _ = ∑ n ∈ s, ∑ t ∈ s, ∑ r ∈ s, ∑ m ∈ s,
          if (n : ℚ) / (m : ℚ) = (r : ℚ) / (t : ℚ)
          then (a n * starRingEnd ℂ (a m)) *
            starRingEnd ℂ (a r * starRingEnd ℂ (a t)) else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        apply Finset.sum_congr rfl
        intro t ht
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro m hm
        simp only [rational_ratio_eq_iff_cross_mul (hs0 m hm) (hs0 t ht)]
        split_ifs
        · simp only [map_mul, starRingEnd_self_apply]
          ring
        · rfl
  have heq := hratio.trans (hcollision.trans hprod.symm)
  apply Complex.ofReal_injective
  push_cast
  simpa only [Complex.mul_conj', rationalAutocorrelation, groupedFrequencyCoefficient,
    productCoefficient] using heq

/-- Weighted energy can be ungrouped exactly wherever frequency collisions
are absent; collisions at a zero weight are harmless. -/
theorem sum_groupedFrequencyCoefficient_norm_sq_mul_eq {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) (a : α → ℂ) (F : Finset β) (w : β → ℝ)
    (hF : ∀ i ∈ s, f i ∈ F)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, f i = f j → w (f i) ≠ 0 → i = j) :
    (∑ b ∈ F, ‖groupedFrequencyCoefficient s f a b‖ ^ 2 * w b) =
      ∑ i ∈ s, ‖a i‖ ^ 2 * w (f i) := by
  classical
  have hfiber (b : β) : ‖groupedFrequencyCoefficient s f a b‖ ^ 2 * w b =
      ∑ i ∈ s.filter (fun i => f i = b), ‖a i‖ ^ 2 * w (f i) := by
    by_cases hw : w b = 0
    · rw [hw, mul_zero]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      rw [(Finset.mem_filter.mp hi).2, hw, mul_zero]
    · by_cases hne : (s.filter (fun i => f i = b)).Nonempty
      · obtain ⟨i, hi⟩ := hne
        have hs : s.filter (fun j => f j = b) = {i} := by
          apply Finset.eq_singleton_iff_unique_mem.mpr
          refine ⟨hi, ?_⟩
          intro j hj
          apply hinj j (Finset.mem_filter.mp hj).1 i (Finset.mem_filter.mp hi).1
          · exact (Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp hi).2.symm
          · simpa only [(Finset.mem_filter.mp hj).2] using hw
        simp only [groupedFrequencyCoefficient, hs, Finset.sum_singleton]
        rw [(Finset.mem_filter.mp hi).2]
      · simp [groupedFrequencyCoefficient, Finset.not_nonempty_iff_eq_empty.mp hne]
  simp_rw [hfiber]
  exact Finset.sum_fiberwise_of_maps_to hF _

/-- Ordered ratios of distinct primes have unique numerator and denominator. -/
theorem prime_ratio_unique {n m r t : ℕ}
    (hn : Nat.Prime n) (hm : Nat.Prime m) (hr : Nat.Prime r) (ht : Nat.Prime t)
    (hnm : n ≠ m) (heq : (n : ℚ) / (m : ℚ) = (r : ℚ) / (t : ℚ)) :
    n = r ∧ m = t := by
  have hcross := (rational_ratio_eq_iff_cross_mul hm.ne_zero ht.ne_zero).mp heq
  have hd : n ∣ r * m := ⟨t, hcross.symm⟩
  rcases hn.dvd_mul.mp hd with hnr | hnm'
  · have hfirst : n = r := (Nat.dvd_prime_two_le hr hn.two_le).mp hnr
    refine ⟨hfirst, ?_⟩
    have hx : n * t = n * m := by simpa [← hfirst] using hcross
    exact (mul_left_cancel₀ hn.ne_zero hx).symm
  · exact False.elim (hnm ((Nat.dvd_prime_two_le hm hn.two_le).mp hnm'))

/-- Exact quartic rational-frequency energy on prime supports. -/
theorem prime_rationalAutocorrelation_fourth_moment
    (s : Finset ℕ) (a : ℕ → ℂ) (hs : ∀ n ∈ s, Nat.Prime n) :
    (∑ q ∈ rationalFrequencySupport s,
      ‖rationalAutocorrelation s a q‖ ^ 2 * Real.log (q : ℝ) ^ 4) =
      weightedFourthFrequencySpread s (fun n => ‖a n‖ ^ 2) (fun n => Real.log n) := by
  classical
  have hinj : ∀ p ∈ s ×ˢ s, ∀ q ∈ s ×ˢ s,
      (p.1 : ℚ) / (p.2 : ℚ) = (q.1 : ℚ) / (q.2 : ℚ) →
      Real.log (((p.1 : ℚ) / (p.2 : ℚ) : ℚ) : ℝ) ^ 4 ≠ 0 → p = q := by
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
    (rationalFrequencySupport s) (fun q => Real.log (q : ℝ) ^ 4)
    (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩) hinj
  change (∑ q ∈ rationalFrequencySupport s,
    ‖groupedFrequencyCoefficient (s ×ˢ s) (fun p => (p.1 : ℚ) / (p.2 : ℚ))
      (fun p => a p.1 * starRingEnd ℂ (a p.2)) q‖ ^ 2 * Real.log (q : ℝ) ^ 4) = _
  rw [h]
  simp only [weightedFourthFrequencySpread, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hs n hn).ne_zero
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hs m hm).ne_zero
  simp [Rat.cast_div, Real.log_div hn0 hm0, mul_pow]

/-- The exact centered fourth-moment identity for aggregated prime frequencies. -/
theorem prime_rationalAutocorrelation_fourth_eq_centered
    (s : Finset ℕ) (a : ℕ → ℂ) (hs : ∀ n ∈ s, Nat.Prime n)
    (c : ℝ) (hc : (∑ n ∈ s, ‖a n‖ ^ 2 * (Real.log n - c)) = 0) :
    (∑ q ∈ rationalFrequencySupport s,
      ‖rationalAutocorrelation s a q‖ ^ 2 * Real.log (q : ℝ) ^ 4) =
      2 * (∑ n ∈ s, ‖a n‖ ^ 2) * (∑ n ∈ s, ‖a n‖ ^ 2 * (Real.log n - c) ^ 4) +
      6 * (∑ n ∈ s, ‖a n‖ ^ 2 * (Real.log n - c) ^ 2) ^ 2 := by
  rw [prime_rationalAutocorrelation_fourth_moment s a hs]
  exact weightedFourthFrequencySpread_eq_centered s _ _ c hc

/-- A factor-two improvement over the original FRZ prime quartic budget. -/
theorem prime_rationalAutocorrelation_fourth_le_half_diameter
    (s : Finset ℕ) (a : ℕ → ℂ) (hs : ∀ n ∈ s, Nat.Prime n) (L U : ℝ)
    (hu : ∀ n ∈ s, L ≤ Real.log n ∧ Real.log n ≤ U) :
    (∑ q ∈ rationalFrequencySupport s,
      ‖rationalAutocorrelation s a q‖ ^ 2 * Real.log (q : ℝ) ^ 4) ≤
      (U - L) ^ 4 * (∑ n ∈ s, ‖a n‖ ^ 2) ^ 2 / 2 := by
  rw [prime_rationalAutocorrelation_fourth_moment s a hs]
  exact weightedFourthFrequencySpread_le_half_diameter s _ _ L U
    (fun n hn => sq_nonneg _) hu

/-- The ratio-one coefficient is precisely the original coefficient energy. -/
theorem rationalAutocorrelation_one (s : Finset ℕ) (a : ℕ → ℂ)
    (hs0 : ∀ n ∈ s, n ≠ 0) :
    rationalAutocorrelation s a 1 = ((∑ n ∈ s, ‖a n‖ ^ 2 : ℝ) : ℂ) := by
  unfold rationalAutocorrelation groupedFrequencyCoefficient
  simp only [Finset.sum_filter, Finset.sum_product, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    _ = ∑ m ∈ s, if n = m then a n * starRingEnd ℂ (a m) else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      have hiff : ((n : ℚ) / (m : ℚ) = 1) ↔ n = m := by
        rw [div_eq_iff (Nat.cast_ne_zero.mpr (hs0 m hm)), one_mul]
        exact Nat.cast_inj
      simp only [hiff]
    _ = a n * starRingEnd ℂ (a n) := by simp [eq_comm, hn]
    _ = _ := by simpa only [Complex.ofReal_pow] using Complex.mul_conj' (a n)

/-- Rational-frequency energy is controlled by the proved bounded-degree count. -/
theorem boundedPrimeDegree_rationalAutocorrelation_energy_le
    (s : Finset ℕ) (a : ℕ → ℂ) (d : ℕ)
    (hs0 : ∀ n ∈ s, n ≠ 0) (hsd : ∀ n ∈ s, primeDegree n ≤ d) :
    (∑ q ∈ rationalFrequencySupport s, ‖rationalAutocorrelation s a q‖ ^ 2) ≤
      ((2 * d).choose d : ℝ) * (∑ n ∈ s, ‖a n‖ ^ 2) ^ 2 := by
  rw [rationalAutocorrelation_energy_eq_product_energy s a hs0]
  exact boundedPrimeDegree_sum_productCoefficient_sq_le s a d _ hs0 hsd

/-- Removing the diagonal saves one full E², including for degree-zero support. -/
theorem boundedPrimeDegree_rationalAutocorrelation_offDiagonal_energy_le
    (s : Finset ℕ) (a : ℕ → ℂ) (d : ℕ)
    (hs0 : ∀ n ∈ s, n ≠ 0) (hsd : ∀ n ∈ s, primeDegree n ≤ d) :
    (∑ q ∈ (rationalFrequencySupport s).erase 1, ‖rationalAutocorrelation s a q‖ ^ 2) ≤
      (((2 * d).choose d : ℝ) - 1) * (∑ n ∈ s, ‖a n‖ ^ 2) ^ 2 := by
  classical
  by_cases he : s = ∅
  · simp [he, rationalFrequencySupport]
  · obtain ⟨n, hn⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hq : (1 : ℚ) ∈ rationalFrequencySupport s := by
      apply Finset.mem_image.mpr
      refine ⟨(n, n), Finset.mem_product.mpr ⟨hn, hn⟩, ?_⟩
      exact div_self (Nat.cast_ne_zero.mpr (hs0 n hn))
    have hsplit := Finset.sum_erase_add (rationalFrequencySupport s)
      (fun q => ‖rationalAutocorrelation s a q‖ ^ 2) hq
    have hE : 0 ≤ ∑ n ∈ s, ‖a n‖ ^ 2 := Finset.sum_nonneg fun n hn => sq_nonneg _
    have hb : ‖rationalAutocorrelation s a 1‖ ^ 2 = (∑ n ∈ s, ‖a n‖ ^ 2) ^ 2 := by
      rw [rationalAutocorrelation_one s a hs0]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE]
    rw [hb] at hsplit
    have hbound := boundedPrimeDegree_rationalAutocorrelation_energy_le s a d hs0 hsd
    nlinarith only [hsplit, hbound]

/-- A logarithmic interval bounds each rational frequency actually present. -/
theorem rationalFrequency_log_fourth_le (s : Finset ℕ) (L U : ℝ)
    (hs0 : ∀ n ∈ s, n ≠ 0)
    (hu : ∀ n ∈ s, L ≤ Real.log n ∧ Real.log n ≤ U)
    {q : ℚ} (hq : q ∈ rationalFrequencySupport s) :
    Real.log (q : ℝ) ^ 4 ≤ (U - L) ^ 4 := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  have hp' := Finset.mem_product.mp hp
  have hn0 : (p.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hs0 p.1 hp'.1)
  have hm0 : (p.2 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hs0 p.2 hp'.2)
  simp only [Rat.cast_div, Rat.cast_natCast, Real.log_div hn0 hm0]
  have h := mul_nonneg
    (show 0 ≤ (U - L) - (Real.log p.1 - Real.log p.2) by
      linarith [(hu p.1 hp'.1).2, (hu p.2 hp'.2).1])
    (show 0 ≤ (U - L) + (Real.log p.1 - Real.log p.2) by
      linarith [(hu p.1 hp'.1).1, (hu p.2 hp'.2).2])
  have h2 : (Real.log p.1 - Real.log p.2) ^ 2 ≤ (U - L) ^ 2 := by nlinarith only [h]
  calc
    _ = ((Real.log p.1 - Real.log p.2) ^ 2) ^ 2 := by ring
    _ ≤ ((U - L) ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h2 2
    _ = _ := by ring

/-- The complete degree-sensitive quartic budget, with its diagonal saving. -/
theorem boundedPrimeDegree_rationalAutocorrelation_fourth_le
    (s : Finset ℕ) (a : ℕ → ℂ) (d : ℕ) (L U : ℝ)
    (hs0 : ∀ n ∈ s, n ≠ 0) (hsd : ∀ n ∈ s, primeDegree n ≤ d)
    (hu : ∀ n ∈ s, L ≤ Real.log n ∧ Real.log n ≤ U) :
    (∑ q ∈ (rationalFrequencySupport s).erase 1,
      ‖rationalAutocorrelation s a q‖ ^ 2 * Real.log (q : ℝ) ^ 4) ≤
      (U - L) ^ 4 * (((2 * d).choose d : ℝ) - 1) * (∑ n ∈ s, ‖a n‖ ^ 2) ^ 2 := by
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
    _ ≤ (U - L) ^ 4 * ((((2 * d).choose d : ℝ) - 1) * (∑ n ∈ s, ‖a n‖ ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (boundedPrimeDegree_rationalAutocorrelation_offDiagonal_energy_le s a d hs0 hsd)
        (by positivity)
    _ = _ := by ring

end RiemannResearch.Fourier
