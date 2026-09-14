import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Bounded average square from dyadic invariance

Source: user-provided two-seed rigidity argument,
`RH_Iff_Two_Seed_Approximation_20260914.md`, Section 4.
This auxiliary proof controls finite prefix energies by fourfold blocking
and Cauchy--Schwarz. It supplies the bound used to construct the continuous
prefix primitive; no approximation or RH hypothesis is assumed.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis

private theorem dyadic_sum_range_four (f : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (4 * N), f k) =
      ∑ k ∈ Finset.range N, (f (4 * k) + f (4 * k + 1) +
        f (4 * k + 2) + f (4 * k + 3)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [show 4 * (N + 1) = (((4 * N + 1) + 1) + 1) + 1 by omega]
      simp only [Finset.sum_range_succ, ih]
      ring

private theorem dyadic_subsequence_energy_le {b : ℕ → ℝ}
    (hb : Summable (fun n => (b n) ^ 2))
    (f : ℕ → ℕ) (hf : Function.Injective f) (N : ℕ) :
    (∑ k ∈ Finset.range N, (b (f k)) ^ 2) ≤ ∑' n, (b n) ^ 2 := by
  calc
    _ = ∑ k ∈ (Finset.range N).image f, (b k) ^ 2 := by
      rw [Finset.sum_image]
      intro x hx y hy hxy
      exact hf hxy
    _ ≤ ∑' n, (b n) ^ 2 := hb.sum_le_tsum _ (fun n hn => sq_nonneg _)

/-- A dyadically invariant sequence with square-summable increments has bounded
average square on all finite initial segments. Source: user-provided argument;
the proof uses a fourfold blocking of the dyadic identity and Cauchy--Schwarz. -/
theorem dyadicInvariant_prefix_energy_bound (a : ℕ → ℝ)
    (h2 : ∀ n, a (2 * n) = a n)
    (hs : Summable (fun n => (a (n + 1) - a n) ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      (∑ k ∈ Finset.range N, (a k) ^ 2) ≤ C * (N : ℝ) := by
  let b : ℕ → ℝ := fun n => a (n + 1) - a n
  let E : ℝ := ∑' n, (b n) ^ 2
  have hb : Summable (fun n => (b n) ^ 2) := hs
  have hE : 0 ≤ E := tsum_nonneg (fun n => sq_nonneg _)
  let B : ℝ := (a 0) ^ 2 + 18 * E + 1
  have hB1 : 1 ≤ B := by dsimp [B]; nlinarith [sq_nonneg (a 0)]
  have hB : 0 ≤ B := le_trans (by norm_num) hB1
  have hBB : B ≤ B ^ 2 := by nlinarith
  have hBE : 18 * E ≤ B ^ 2 := by
    have haux : 18 * E ≤ B := by dsimp [B]; nlinarith [sq_nonneg (a 0)]
    exact haux.trans hBB
  have hBa : (a 0) ^ 2 ≤ B ^ 2 := by
    have haux : (a 0) ^ 2 ≤ B := by dsimp [B]; nlinarith
    exact haux.trans hBB
  have hfour (k : ℕ) : a (4 * k) = a k := by
    calc
      a (4 * k) = a (2 * (2 * k)) := by congr 1; omega
      _ = a (2 * k) := h2 _
      _ = a k := h2 _
  have hmid (k : ℕ) : a (4 * k + 2) = a (2 * k + 1) := by
    convert h2 (2 * k + 1) using 1 <;> congr 1 <;> omega
  have hodd (k : ℕ) : a (2 * k + 1) = a k + b (2 * k) := by
    dsimp [b]
    rw [h2]
    ring
  have hfour_one (k : ℕ) : a (4 * k + 1) = a k + b (4 * k) := by
    dsimp [b]
    rw [hfour]
    ring
  have hfour_two (k : ℕ) : a (4 * k + 2) = a k + b (2 * k) := by
    rw [hmid, hodd]
  have hfour_three (k : ℕ) :
      a (4 * k + 3) = a k + b (2 * k) + b (4 * k + 2) := by
    dsimp [b]
    rw [show 4 * k + 2 + 1 = 4 * k + 3 by omega, hmid, h2]
    ring
  have hstep (N : ℕ) (t : ℝ) (ht0 : 0 ≤ t)
      (ht : (∑ k ∈ Finset.range N, (a k) ^ 2) ≤ t ^ 2) :
      (∑ k ∈ Finset.range (4 * N), (a k) ^ 2) ≤ (2 * t + B) ^ 2 := by
    let c : ℕ → ℝ := fun k => b (4 * k) + 2 * b (2 * k) + b (4 * k + 2)
    let r : ℕ → ℝ := fun k => (b (4 * k)) ^ 2 + (b (2 * k)) ^ 2 +
      (b (2 * k) + b (4 * k + 2)) ^ 2
    have hx : (∑ k ∈ Finset.range N, (b (4 * k)) ^ 2) ≤ E :=
      dyadic_subsequence_energy_le hb (fun k => 4 * k) (by intro i j hij; dsimp at hij; omega) N
    have hy : (∑ k ∈ Finset.range N, (b (2 * k)) ^ 2) ≤ E :=
      dyadic_subsequence_energy_le hb (fun k => 2 * k) (by intro i j hij; dsimp at hij; omega) N
    have hz : (∑ k ∈ Finset.range N, (b (4 * k + 2)) ^ 2) ≤ E :=
      dyadic_subsequence_energy_le hb (fun k => 4 * k + 2) (by intro i j hij; dsimp at hij; omega) N
    have hc : (∑ k ∈ Finset.range N, (c k) ^ 2) ≤ 18 * E := by
      calc
        _ ≤ ∑ k ∈ Finset.range N,
              6 * ((b (4 * k)) ^ 2 + (b (2 * k)) ^ 2 + (b (4 * k + 2)) ^ 2) := by
          apply Finset.sum_le_sum
          intro k hk
          dsimp [c]
          nlinarith [sq_nonneg (2 * b (4 * k) - b (2 * k)),
            sq_nonneg (b (4 * k) - b (4 * k + 2)),
            sq_nonneg (b (2 * k) - 2 * b (4 * k + 2))]
        _ = 6 * ((∑ k ∈ Finset.range N, (b (4 * k)) ^ 2) +
              (∑ k ∈ Finset.range N, (b (2 * k)) ^ 2) +
              (∑ k ∈ Finset.range N, (b (4 * k + 2)) ^ 2)) := by
          simp only [← Finset.mul_sum, Finset.sum_add_distrib]
        _ ≤ 18 * E := by linarith
    have hr : (∑ k ∈ Finset.range N, r k) ≤ 6 * E := by
      calc
        _ ≤ ∑ k ∈ Finset.range N,
              ((b (4 * k)) ^ 2 + 3 * (b (2 * k)) ^ 2 + 2 * (b (4 * k + 2)) ^ 2) := by
          apply Finset.sum_le_sum
          intro k hk
          dsimp [r]
          nlinarith [sq_nonneg (b (2 * k) - b (4 * k + 2))]
        _ = (∑ k ∈ Finset.range N, (b (4 * k)) ^ 2) +
              3 * (∑ k ∈ Finset.range N, (b (2 * k)) ^ 2) +
              2 * (∑ k ∈ Finset.range N, (b (4 * k + 2)) ^ 2) := by
          simp only [Finset.mul_sum, Finset.sum_add_distrib]
        _ ≤ 6 * E := by linarith
    have hcs : (∑ k ∈ Finset.range N, a k * c k) ^ 2 ≤ t ^ 2 * B ^ 2 := by
      calc
        _ ≤ (∑ k ∈ Finset.range N, (a k) ^ 2) *
              (∑ k ∈ Finset.range N, (c k) ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        _ ≤ t ^ 2 * B ^ 2 :=
          mul_le_mul ht (hc.trans hBE) (Finset.sum_nonneg (fun k hk => sq_nonneg _))
            (sq_nonneg t)
    have hcross : (∑ k ∈ Finset.range N, a k * c k) ≤ t * B := by
      have habs : |∑ k ∈ Finset.range N, a k * c k| ≤ t * B :=
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg ht0 hB)).mp
          (by simpa only [sq_abs, mul_pow] using hcs)
      exact (le_abs_self _).trans habs
    have heq : (∑ k ∈ Finset.range (4 * N), (a k) ^ 2) =
        4 * (∑ k ∈ Finset.range N, (a k) ^ 2) +
        2 * (∑ k ∈ Finset.range N, a k * c k) + (∑ k ∈ Finset.range N, r k) := by
      calc
        _ = ∑ k ∈ Finset.range N,
            ((a (4 * k)) ^ 2 + (a (4 * k + 1)) ^ 2 +
              (a (4 * k + 2)) ^ 2 + (a (4 * k + 3)) ^ 2) := dyadic_sum_range_four _ N
        _ = ∑ k ∈ Finset.range N, (4 * (a k) ^ 2 + 2 * (a k * c k) + r k) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [hfour, hfour_one, hfour_two, hfour_three]
          dsimp [c, r]
          ring
        _ = _ := by simp only [Finset.mul_sum, Finset.sum_add_distrib]
    nlinarith [mul_nonneg ht0 hB]
  have hp (j : ℕ) : (1 : ℝ) ≤ 2 ^ j := by
    induction j with
    | zero => norm_num
    | succ j ih => rw [pow_succ]; nlinarith
  have hd (j : ℕ) : (∑ k ∈ Finset.range (4 ^ j), (a k) ^ 2) ≤
      (B * ((2 : ℝ) ^ (j + 1) - 1)) ^ 2 := by
    induction j with
    | zero => norm_num <;> exact hBa
    | succ j ih =>
        calc
          _ = ∑ k ∈ Finset.range (4 * 4 ^ j), (a k) ^ 2 := by
            rw [pow_succ, Nat.mul_comm (4 ^ j) 4]
          _ ≤ (2 * (B * ((2 : ℝ) ^ (j + 1) - 1)) + B) ^ 2 :=
            hstep _ _ (mul_nonneg hB (sub_nonneg.mpr (hp _))) ih
          _ = _ := by simp only [pow_succ]; ring
  have hd' (j : ℕ) : (∑ k ∈ Finset.range (4 ^ j), (a k) ^ 2) ≤
      4 * B ^ 2 * (4 : ℝ) ^ j := by
    calc
      _ ≤ (B * ((2 : ℝ) ^ (j + 1) - 1)) ^ 2 := hd j
      _ ≤ (B * (2 : ℝ) ^ (j + 1)) ^ 2 := by
        apply (sq_le_sq₀ (mul_nonneg hB (sub_nonneg.mpr (hp _)))
          (mul_nonneg hB (le_trans (by norm_num) (hp _)))).2
        nlinarith
      _ = 4 * B ^ 2 * (4 : ℝ) ^ j := by
        rw [mul_pow]
        have hpow : ((2 : ℝ) ^ (j + 1)) ^ 2 = (4 : ℝ) ^ (j + 1) := by
          rw [sq, ← mul_pow]
          norm_num
        rw [hpow, pow_succ]
        ring
  refine ⟨16 * B ^ 2, by positivity, ?_⟩
  intro N
  by_cases hN : N = 0
  · subst N
    simp
  obtain ⟨j, hj0, hj1⟩ := exists_nat_pow_near (show 1 ≤ N by omega) (show 1 < (4 : ℕ) by norm_num)
  have hpow : (4 : ℝ) ^ (j + 1) ≤ 4 * (N : ℝ) := by
    have hjR : (4 : ℝ) ^ j ≤ (N : ℝ) := by exact_mod_cast hj0
    rw [pow_succ]
    nlinarith
  calc
    _ ≤ ∑ k ∈ Finset.range (4 ^ (j + 1)), (a k) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_of_lt hj1))
        (fun k hk hkn => sq_nonneg _)
    _ ≤ 4 * B ^ 2 * (4 : ℝ) ^ (j + 1) := hd' _
    _ ≤ 4 * B ^ 2 * (4 * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 16 * B ^ 2 * (N : ℝ) := by ring

end RiemannResearch.Analysis
