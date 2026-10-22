import RiemannResearch.RH.CRTLegalCoordinates

/-!
# Inverse-square energy detects the actual CRT coefficient mean

Source: `Independent_Primes_Squarefree_Approximation_2026-10-07.md`,
Section 6 and research Priority 2. This module proves a first-period
Jensen bound. Its constant is weaker by the factor `1 / Z` than the
paper's all-period bound; it does not claim that stronger result.
Every infinite-sum lower bound retains a `Summable` hypothesis.

-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.CRTBlock
open ArithmeticCumulative

/-- Finite weighted Jensen bound for the actual prefix mean. -/
theorem weighted_periodMean_square_le
    (P : ℕ) (hP : 0 < P) (u w : ℕ → ℝ) (a : ℝ)
    (ha : 0 ≤ a)
    (hw : ∀ k ∈ Finset.range P, a ≤ w (k + 1)) :
    a * (P : ℝ) * (periodMean u P)^2 ≤
      ∑ k ∈ Finset.range P, w (k + 1) * (u (k + 1))^2 := by
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hm : (∑ k ∈ Finset.range P, u (k + 1)) =
      (P : ℝ) * periodMean u P := by
    unfold periodMean cumulative
    field_simp [ne_of_gt hPR]
  have hv : 0 ≤ ∑ k ∈ Finset.range P,
      (u (k + 1) - periodMean u P)^2 :=
    Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have he : (∑ k ∈ Finset.range P,
      (u (k + 1) - periodMean u P)^2) =
      (∑ k ∈ Finset.range P, (u (k + 1))^2) -
        (P : ℝ) * (periodMean u P)^2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    rw [hm]
    ring
  rw [he] at hv
  have hbase : (P : ℝ) * (periodMean u P)^2 ≤
      ∑ k ∈ Finset.range P, (u (k + 1))^2 := by linarith
  calc
    _ = a * ((P : ℝ) * (periodMean u P)^2) := by ring
    _ ≤ a * (∑ k ∈ Finset.range P, (u (k + 1))^2) :=
      mul_le_mul_of_nonneg_left hbase ha
    _ = ∑ k ∈ Finset.range P, a * (u (k + 1))^2 := by
      rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum (fun k hk =>
      mul_le_mul_of_nonneg_right (hw k hk) (sq_nonneg _))

/-- First-period lower bound. Summability avoids totalized-tsum artifacts. -/
theorem inverseSquare_periodMean_lower
    (Z : ℝ) (hZ : 0 < Z) (P : ℕ) (hP : 0 < P) (u : ℕ → ℝ)
    (hs : Summable (fun k : ℕ =>
      (1 / (Z * ((k + 1 : ℕ) : ℝ)^2)) * (u (k + 1))^2)) :
    (periodMean u P)^2 / (Z * (P : ℝ)) ≤
      ∑' k : ℕ, (1 / (Z * ((k + 1 : ℕ) : ℝ)^2)) * (u (k + 1))^2 := by
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hw : ∀ k ∈ Finset.range P,
      1 / (Z * (P : ℝ)^2) ≤ 1 / (Z * ((k + 1 : ℕ) : ℝ)^2) := by
    intro k hk
    have hkP : ((k + 1 : ℕ) : ℝ) ≤ P := by
      exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
    have hk0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hsq : (((k + 1 : ℕ) : ℝ))^2 ≤ (P : ℝ)^2 := by nlinarith
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left hsq hZ.le)
  have hb := weighted_periodMean_square_le P hP u
    (fun n => 1 / (Z * (n : ℝ)^2))
    (1 / (Z * (P : ℝ)^2)) (by positivity) hw
  have hid : (1 / (Z * (P : ℝ)^2)) * (P : ℝ) * (periodMean u P)^2 =
      (periodMean u P)^2 / (Z * (P : ℝ)) := by
    field_simp [ne_of_gt hZ, ne_of_gt hPR]
  rw [hid] at hb
  exact hb.trans (hs.sum_le_tsum (Finset.range P) (fun k _ => by positivity))

theorem periodMean_one_sub (u : ℕ → ℝ) (P : ℕ) (hP : 0 < P) :
    periodMean (fun k => 1 - u k) P = 1 - periodMean u P := by
  have hPR : (P : ℝ) ≠ 0 := by positivity
  unfold periodMean cumulative
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  field_simp

/-- Actual residue coefficients enter through the two exact moments. -/
theorem normalizedResidueSynthesis_inverseSquare_error_lower
    (Z : ℝ) (hZ : 0 < Z) (s : Finset ℕ) (c : ℕ → ℝ)
    (P : ℕ) (hP : 0 < P) (hs : ∀ d ∈ s, 2 ≤ d)
    (hdiv : ∀ d ∈ s, d ∣ P)
    (henergy : Summable (fun k : ℕ =>
      (1 / (Z * ((k + 1 : ℕ) : ℝ)^2)) *
        (1 - normalizedResidueSynthesis s c (k + 1))^2)) :
    (1 - ((∑ d ∈ s, c d) - (∑ d ∈ s, c d / (d : ℝ))) / 2)^2 /
        (Z * (P : ℝ)) ≤
      ∑' k : ℕ, (1 / (Z * ((k + 1 : ℕ) : ℝ)^2)) *
        (1 - normalizedResidueSynthesis s c (k + 1))^2 := by
  have h := inverseSquare_periodMean_lower Z hZ P hP
    (fun k => 1 - normalizedResidueSynthesis s c k) henergy
  rw [periodMean_one_sub _ P hP,
    normalizedResidueSynthesis_periodMean s c P hP hs hdiv] at h
  exact h

end RiemannResearch.RH.CRTBlock
