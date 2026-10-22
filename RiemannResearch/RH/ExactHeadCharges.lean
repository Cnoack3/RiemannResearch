import RiemannResearch.RH.ParetoResidueDuality
import Mathlib.Tactic.Linarith

/-!
# Uniqueness and arithmetic determination of exact-head charges

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 8, equations (37)--(38). These are genuine arithmetic consequences
of exact interpolation; no energy bound or RH hypothesis is introduced.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators

noncomputable section

/-- The divisor-inverted jump depends only on the anchored finite head. -/
theorem mobiusDifference_congr_initial {F G : ℕ → ℝ} {N n : ℕ}
    (hn : n ≤ N) (hhead : ∀ k ≤ N, F k = G k) :
    mobiusDifference n F = mobiusDifference n G := by
  unfold mobiusDifference
  apply Finset.sum_congr rfl
  intro d hd
  have hnpos : 0 < n := Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2
  have hdN : d ≤ N := (Nat.le_of_dvd hnpos
    (Nat.dvd_of_mem_divisors hd)).trans hn
  rw [hhead d hdN, hhead (d - 1) (by omega)]

/-- Exact agreement with the anchored target forces the actual Möbius charge. -/
theorem exact_head_mobiusDifference {F : ℕ → ℝ} {N n : ℕ}
    (hzero : F 0 = 0) (hhead : ∀ k, 0 < k → k ≤ N → F k = 1)
    (hn : 0 < n) (hnN : n ≤ N) :
    mobiusDifference n F = (ArithmeticFunction.moebius n : ℝ) := by
  rw [mobiusDifference_congr_initial (G := fun k => if k = 0 then 0 else 1)
    hnN (by
      intro k hk
      by_cases hk0 : k = 0
      · simp [hk0, hzero]
      · simpa [hk0] using hhead k (Nat.pos_of_ne_zero hk0) hk)]
  exact mobiusDifference_one n hn

/-- Equation (38), with its normalization and the index 1 retained. -/
theorem exact_head_normalized_charge {F : ℕ → ℝ} {N n : ℕ}
    (hzero : F 0 = 0) (hhead : ∀ k, 0 < k → k ≤ N → F k = 1)
    (hn : 0 < n) (hnN : n ≤ N) :
    mobiusDifference n F / (n : ℝ) =
      (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) := by
  rw [exact_head_mobiusDifference hzero hhead hn hnN]

/-- Anchoring at zero removes the sole additive ambiguity of jump inversion. -/
theorem mobiusDifference_injective_anchored {F G : ℕ → ℝ}
    (hzero : F 0 = G 0)
    (hcharge : ∀ n, 0 < n → mobiusDifference n F = mobiusDifference n G) :
    F = G := by
  funext n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    have hs : (∑ d ∈ (n + 1).divisors, mobiusDifference d F) =
        ∑ d ∈ (n + 1).divisors, mobiusDifference d G := by
      apply Finset.sum_congr rfl
      intro d hd
      exact hcharge d (Nat.pos_of_mem_divisors hd)
    rw [sum_mobiusDifference F (n + 1) (by omega),
      sum_mobiusDifference G (n + 1) (by omega)] at hs
    simp only [Nat.add_sub_cancel] at hs
    linarith

/-- The complete residue formula, retaining the special charge at index 1. -/
theorem mobiusDifference_residue_initial (m n : ℕ) (hm : 0 < m) :
    mobiusDifference m (residue n) =
      (if m = 1 then 1 else 0) - (if m = n then (n : ℝ) else 0) := by
  let f : ℕ → ℝ := fun d => (if d = 1 then 1 else 0) -
    (if d = n then (n : ℝ) else 0)
  have hs : ∀ k > 0, ∑ d ∈ k.divisors, f d =
      residue n k - residue n (k - 1) := by
    intro k hk
    rw [residue_difference n k hk]
    simp [f, Finset.sum_sub_distrib, Nat.mem_divisors, ne_of_gt hk]
  exact (mobius_inversion f (fun k => residue n k - residue n (k - 1))).mp hs m hm

/-- Finite balanced residue coefficients really are the normalized jump charges. -/
theorem balanced_residue_mobiusDifference (s : Finset ℕ) (c : ℕ → ℝ)
    (hbalance : ∑ d ∈ s, c d = 0) (n : ℕ) (hn : 0 < n) :
    mobiusDifference n (fun k => ∑ d ∈ s, (-c d) * residue d k) =
      (n : ℝ) * (if n ∈ s then c n else 0) := by
  rw [mobiusDifference_sum]
  simp_rw [mobiusDifference_residue_initial n _ hn, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hz : (∑ d ∈ s, -c d * (if n = 1 then 1 else 0)) = 0 := by
    rw [← Finset.sum_mul, Finset.sum_neg_distrib, hbalance]
    simp
  rw [hz]
  simp [mul_ite, Finset.sum_neg_distrib, mul_comm]
  split_ifs <;> ring

/-- In a finite legal charge presentation the head coefficients are forced,
including the otherwise invisible residue index 1. -/
theorem balanced_residue_exact_head_coefficients (s : Finset ℕ) (c : ℕ → ℝ)
    (hbalance : ∑ d ∈ s, c d = 0) (N : ℕ)
    (hhead : ∀ k, 0 < k → k ≤ N →
      (∑ d ∈ s, (-c d) * residue d k) = 1)
    (n : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
    (if n ∈ s then c n else 0) =
      (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) := by
  have hz : (∑ d ∈ s, (-c d) * residue d 0) = 0 := by
    simp [residue]
  have he := exact_head_mobiusDifference hz hhead hn hnN
  rw [balanced_residue_mobiusDifference s c hbalance n hn] at he
  have hnR : (n : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hnR).mpr
  nlinarith

end
end RiemannResearch.RH.Pareto
