/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.PrimeTreeCarryLaw
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic

/-! # Uniform remainder and finite first moment for physical carry chains

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros* (2026),
§§3.1–3.2. The final conductor contributes one parent weight and the
remaining prime terms cost at most two more.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.CRTCarryArithmetic.NormalizedCarryChain
open ArithmeticCumulative

variable (s : NormalizedCarryChain)

theorem primeWeight_bound (k : ℕ) (hw : 0 ≤ s.w k) (hw' : 0 ≤ s.w (k+1))
    (hmono : s.w (k+1) ≤ s.w k) (hp : s.p k ≤ s.D k) :
    |s.w (k+1) * (s.b k : ℝ)| ≤ s.w k := by
  have hD : 0 < (s.D k : ℝ) := by exact_mod_cast
    (pow_pos (by decide : 0 < (2 : ℕ)) k).trans_le (s.modulus_growth k)
  have hpR : (s.p k : ℝ) ≤ s.D k := by exact_mod_cast hp
  have hpL : (2 : ℝ) ≤ s.p k := by exact_mod_cast s.radix_ge k
  have he : (s.w (k+1) * (s.b k : ℝ)) * (s.D k : ℝ) = s.w (k+1) - s.w k * (s.p k : ℝ) := by
    linear_combination s.w (k+1) * s.bezout k - (s.p k : ℝ) * s.normalize k
  have hn : s.w (k+1) * (s.b k : ℝ) ≤ 0 := by
    apply nonpos_of_mul_nonpos_left _ hD
    rw [he]
    linarith [mul_le_mul_of_nonneg_left hpL hw]
  have hl : -(s.w k) ≤ s.w (k+1) * (s.b k : ℝ) := by
    apply (le_of_mul_le_mul_right _ hD)
    rw [he, neg_mul]
    linarith [mul_le_mul_of_nonneg_left hpR hw]
  rw [abs_of_nonpos hn]
  linarith

theorem futureWeight_bound (hw : ∀ k, 0 ≤ s.w k) (ha : ∀ k, (2 : ℤ) ≤ s.a (k+1))
    (K : ℕ) (hK : 0 < K) (j : ℕ) : s.w (j+K) ≤ s.w K * (1/2 : ℝ)^j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hindex : j + K = (j + K - 1) + 1 := by omega
    have hr : (2 : ℝ) ≤ (s.a (j+K) : ℝ) := by
      rw [hindex]
      exact_mod_cast ha _
    have h := mul_le_mul_of_nonneg_left hr (hw (j+K+1))
    rw [pow_succ, Nat.succ_add]
    change s.w (j+K+1) ≤ _
    linarith [s.normalize (j+K)]

/-- The absolute sum of all prime coefficients after stage K costs at most
twice its final parent weight. -/
theorem primeWeight_tail (hw : ∀ k, 0 ≤ s.w k) (hmono : ∀ k, s.w (k+1) ≤ s.w k)
    (ha : ∀ k, (2 : ℤ) ≤ s.a (k+1)) (hp : ∀ k, s.p (k+1) ≤ s.D (k+1))
    (K : ℕ) (hK : 0 < K) :
    Summable (fun j => |s.w (j+K+1) * (s.b (j+K) : ℝ)|) ∧
    (∑' j, |s.w (j+K+1) * (s.b (j+K) : ℝ)|) ≤ 2 * s.w K := by
  have hge : HasSum (fun j : ℕ => (1/2 : ℝ)^j) 2 := by
    convert hasSum_geometric_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num) using 1
    norm_num
  have hg := hge.mul_left (s.w K)
  have hb (j : ℕ) : ‖|s.w (j+K+1) * (s.b (j+K) : ℝ)|‖ ≤ s.w K * (1/2 : ℝ)^j := by
    rw [Real.norm_eq_abs, abs_abs]
    have hpi : s.p (j+K) ≤ s.D (j+K) := by
      obtain ⟨i, hi⟩ : ∃ i, j+K = i+1 := ⟨j+K-1, by omega⟩
      rw [hi]
      exact hp i
    exact (s.primeWeight_bound _ (hw _) (hw _) (hmono _) hpi).trans (s.futureWeight_bound hw ha K hK j)
  refine ⟨Summable.of_norm_bounded hg.summable hb, ?_⟩
  have h := tsum_of_norm_bounded hg hb
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun _ => abs_nonneg _), mul_comm] at h
  exact h

/-- Pointwise estimate with a common coefficient independent of the site.
This is the 3w_K estimate of §3.1. -/
theorem carry_uniform_remainder (hw : ∀ k, 0 ≤ s.w k) (hmono : ∀ k, s.w (k+1) ≤ s.w k)
    (ha : ∀ k, (2 : ℤ) ≤ s.a (k+1)) (hp : ∀ k, s.p (k+1) ≤ s.D (k+1))
    (K : ℕ) (hK : 0 < K) (n : ℕ) :
    |(∑' k, s.carryTerm n k) - ∑ k ∈ Finset.range K, s.carryTerm n k| ≤ 3 * s.w K := by
  have hs := (s.infinite_carry_expansion n).1
  have he := hs.sum_add_tsum_nat_add K
  have ht := s.primeWeight_tail hw hmono ha hp K hK
  have hterm (j : ℕ) : ‖s.primeTerm n (j+K)‖ ≤ |s.w (j+K+1) * (s.b (j+K) : ℝ)| := by
    rw [Real.norm_eq_abs, primeTerm, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (residueFraction_abs_le_one _ _)
  have htt := (tsum_of_norm_bounded ht.1.hasSum hterm).trans ht.2
  have hpar : |s.parentTerm n K| ≤ s.w K := by
    rw [parentTerm, abs_mul, abs_of_nonneg (hw K)]
    exact mul_le_of_le_one_right (hw _) (residueFraction_abs_le_one _ _)
  have heq : (∑' k, s.carryTerm n k) - ∑ k ∈ Finset.range K, s.carryTerm n k =
      (∑' j, s.primeTerm n (j+K)) + s.parentTerm n K := by
    rw [(s.infinite_carry_expansion n).2.2, s.sum_carries]
    linarith
  rw [heq]
  rw [Real.norm_eq_abs] at htt
  exact (abs_add_le _ _).trans (by linarith)

end RiemannResearch.RH.CRTCarryArithmetic.NormalizedCarryChain
