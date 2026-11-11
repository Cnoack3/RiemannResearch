import RiemannResearch.Analysis.RationalLogSeparation
import RiemannResearch.Analysis.RationalAutocorrelationEnergy

/-!
Explicit height separation of integer and aggregated rational logarithmic
frequencies. The constants are 1/M and 1/M², using the integer cross-product gap.
-/

namespace RiemannResearch.Fourier

/-- Distinct positive integer frequencies up to M have log spacing at least 1/M. -/
theorem integerLog_separation_of_le {n m M : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hnM : n ≤ M) (hmM : m ≤ M) (hne : n ≠ m) :
    1 / (M : ℝ) ≤ |Real.log n - Real.log m| := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnMR : (n : ℝ) ≤ M := by exact_mod_cast hnM
  have hmMR : (m : ℝ) ≤ M := by exact_mod_cast hmM
  have hgap : (1 : ℝ) ≤ |(n : ℝ) - (m : ℝ)| := by
    simpa using RiemannResearch.Analysis.RationalLogSeparation.integer_gap
      (m := m) (n := n) (q := 1) (by simpa using hne)
  have hmax : (0 : ℝ) < max (n : ℝ) (m : ℝ) := lt_of_lt_of_le hnR (le_max_left _ _)
  calc
    1 / (M : ℝ) ≤ 1 / max (n : ℝ) (m : ℝ) :=
      one_div_le_one_div_of_le hmax (max_le hnMR hmMR)
    _ ≤ |(n : ℝ) - (m : ℝ)| / max (n : ℝ) (m : ℝ) :=
      div_le_div_of_nonneg_right hgap hmax.le
    _ ≤ |Real.log ((n : ℝ) / (m : ℝ))| :=
      RiemannResearch.Analysis.RationalLogSeparation.abs_sub_div_max_le_abs_log_div hnR hmR
    _ = _ := by rw [Real.log_div (ne_of_gt hnR) (ne_of_gt hmR)]

/-- Distinct ratios with entries at most M have logarithmic separation 1/M². -/
theorem rationalLog_separation_of_height {n m r t M : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hr : 0 < r) (ht : 0 < t)
    (hnM : n ≤ M) (hmM : m ≤ M) (hrM : r ≤ M) (htM : t ≤ M)
    (hne : (n : ℚ) / (m : ℚ) ≠ (r : ℚ) / (t : ℚ)) :
    1 / (M : ℝ) ^ 2 ≤ |(Real.log n - Real.log m) - (Real.log r - Real.log t)| := by
  have hcross : n * t ≠ r * m := by
    intro heq
    exact hne ((rational_ratio_eq_iff_cross_mul (ne_of_gt hm) (ne_of_gt ht)).mpr heq)
  have h := integerLog_separation_of_le (Nat.mul_pos hn ht) (Nat.mul_pos hr hm)
    (Nat.mul_le_mul hnM htM) (Nat.mul_le_mul hrM hmM) hcross
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm)
  have hr0 : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hr)
  have ht0 : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt ht)
  have hlog : (Real.log n - Real.log m) - (Real.log r - Real.log t) =
      Real.log (n * t : ℕ) - Real.log (r * m : ℕ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Real.log_mul hn0 ht0, Real.log_mul hr0 hm0]
    ring
  rw [hlog]
  simpa only [Nat.cast_mul, pow_two] using h

/-- The 1/M² gap applies after equal rational frequencies have been aggregated. -/
theorem rationalFrequencySupport_log_separation
    (s : Finset ℕ) (M : ℕ) (hs0 : ∀ n ∈ s, 0 < n) (hsM : ∀ n ∈ s, n ≤ M)
    {q r : ℚ} (hq : q ∈ rationalFrequencySupport s) (hr : r ∈ rationalFrequencySupport s)
    (hne : q ≠ r) :
    1 / (M : ℝ) ^ 2 ≤ |Real.log (q : ℝ) - Real.log (r : ℝ)| := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
  have hp' := Finset.mem_product.mp hp
  have hv' := Finset.mem_product.mp hv
  have h := rationalLog_separation_of_height (hs0 _ hp'.1) (hs0 _ hp'.2)
    (hs0 _ hv'.1) (hs0 _ hv'.2) (hsM _ hp'.1) (hsM _ hp'.2)
    (hsM _ hv'.1) (hsM _ hv'.2) hne
  have hp10 : (p.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (hs0 _ hp'.1))
  have hp20 : (p.2 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (hs0 _ hp'.2))
  have hv10 : (v.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (hs0 _ hv'.1))
  have hv20 : (v.2 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (hs0 _ hv'.2))
  simpa only [Rat.cast_div, Rat.cast_natCast, Real.log_div hp10 hp20,
    Real.log_div hv10 hv20] using h

end RiemannResearch.Fourier
