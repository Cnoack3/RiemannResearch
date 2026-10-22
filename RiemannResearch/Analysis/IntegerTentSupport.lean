import RiemannResearch.Analysis.LogarithmicTentIntegral
import Mathlib.Tactic.NormNum

/-!
# Integer support of the compensated dyadic shells

Source: user-provided FourierBridgeUniformSignedEnergy20260910.md, Section 8.
These are unconditional identities for the actual root tent. In particular,
the negative-depth atomic shell vanishes before a norm estimate is taken.
The compensated continuum contribution is not asserted to vanish.
-/

namespace RiemannResearch.Analysis
open scoped BigOperators

theorem rootTent_le_one (a x : ℝ) : rootTent a x ≤ 1 := by
  unfold rootTent
  apply max_le (by norm_num)
  linarith [abs_nonneg (x - (a + 1))]

theorem rootTent_pos_iff (a x : ℝ) :
    0 < rootTent a x ↔ a < x ∧ x < a + 2 := by
  constructor
  · intro h
    constructor
    · by_contra hn
      rw [rootTent_eq_zero_of_le (le_of_not_gt hn)] at h
      exact (lt_irrefl 0) h
    · by_contra hn
      rw [rootTent_eq_zero_of_ge (le_of_not_gt hn)] at h
      exact (lt_irrefl 0) h
  · rintro ⟨hl, hr⟩
    have habs : |x - (a + 1)| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    exact lt_of_lt_of_le (by linarith : 0 < 1 - |x - (a + 1)|)
      (le_max_right _ _)

theorem rootTent_even_nat (l k : ℕ) :
    rootTent (2 * (l : ℝ)) (2 * (k : ℝ)) = 0 := by
  by_cases h : k ≤ l
  · apply rootTent_eq_zero_of_le
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast h) (by norm_num)
  · have h' : l + 1 ≤ k := by omega
    apply rootTent_eq_zero_of_ge
    have hc : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast h'
    linarith

theorem rootTent_positive_nat_index_unique (l m : ℕ) (x : ℝ)
    (hl : 0 < rootTent (2 * (l : ℝ)) x)
    (hm : 0 < rootTent (2 * (m : ℝ)) x) : l = m := by
  obtain ⟨hl1, hl2⟩ := (rootTent_pos_iff _ _).mp hl
  obtain ⟨hm1, hm2⟩ := (rootTent_pos_iff _ _).mp hm
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hc : (l : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hlt)
    linarith
  · have hc : (m : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hgt)
    linarith

theorem rootTent_negative_depth_atomic_zero (l A d n : ℕ) :
    rootTent (2 * (l : ℝ))
      (((A : ℝ) * 2 ^ (d + 1)) * (n : ℝ)) = 0 := by
  have heq : ((A : ℝ) * 2 ^ (d + 1)) * (n : ℝ) =
      2 * ((A * 2 ^ d * n : ℕ) : ℝ) := by
    push_cast
    rw [pow_succ]
    ring
  rw [heq]
  exact rootTent_even_nat l (A * 2 ^ d * n)

theorem negative_depth_signed_atomic_sum_zero
    (s : Finset ℕ) (b : ℕ → ℝ) (l A d : ℕ) :
    (∑ n ∈ s, (b n / (n : ℝ)) *
      rootTent (2 * (l : ℝ))
        (((A : ℝ) * 2 ^ (d + 1)) * (n : ℝ))) = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  rw [rootTent_negative_depth_atomic_zero, mul_zero]

end RiemannResearch.Analysis
