/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.LogPowerSummability
import RiemannResearch.NumberTheory.DivisorCountSummability
import Mathlib.Tactic.FieldSimp

/-!
# Divisor-count summability at the logarithmic boundary

For a nonnegative weight g decreasing on positive integers, Dirichlet convolution
transfers summability of g(n)/n to summability of tau(n) g(n)^2/n. Taking
 g(n) = 1 / log(2n)^(p/2) gives convergence of tau(n)/(n log(2n)^p) for p > 2.
The convention at n = 0 is Lean's totalized division; every displayed series
has zero initial term.

Source for the convolution proof step: Mathlib's `LSeriesSummable.convolution`,
https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/Convolution.html.
The other analytic provider is the locally proved classical logarithmic p-series
in `Analysis.LogPowerSummability`. The comparison is elementary; no novelty
claim or unproved arithmetic input is used.

RH consumer: `RH.NaturalMobiusLogarithmicTests` extends the physical-primitive
test class from fixed sublinear powers to n/log(2n)^p, p > 2. It does not assert
that the actual limiting RH residual satisfies this additional regularity.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.NumberTheory

/-- A Dirichlet-convolution transfer for nonnegative decreasing weights. -/
theorem summable_divisor_count_mul_sq_div_of_antitone
    (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n)
    (hmono : ∀ {m n : ℕ}, 0 < m → m ≤ n → g n ≤ g m)
    (hs : Summable (fun n : ℕ => g n / (n : ℝ))) :
    Summable (fun n : ℕ => (n.divisors.card : ℝ) * (g n)^2 / (n : ℝ)) := by
  let f : ℕ → ℂ := fun n => (g n : ℂ)
  have hf : LSeriesSummable f 1 := by
    apply summable_norm_iff.mp
    apply hs.congr
    intro n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn, f, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg n)]
  let C : ℕ → ℝ := fun n => ∑ d ∈ n.divisors, g d * g (n / d)
  have hC (n : ℕ) : 0 ≤ C n := by
    exact Finset.sum_nonneg (fun d _ => mul_nonneg (hg d) (hg (n / d)))
  have he (n : ℕ) : LSeries.convolution f f n = (C n : ℂ) := by
    rw [LSeries.convolution_def]
    dsimp only
    rw [Nat.sum_divisorsAntidiagonal (fun a b => f a * f b)]
    simp [C, f]
  have hc := hf.convolution hf
  have hsum : Summable (fun n : ℕ => C n / (n : ℝ)) := by
    apply hc.norm.congr
    intro n
    rw [LSeries.norm_term_eq, he]
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hC n)]
  apply hsum.of_nonneg_of_le
  · intro n
    positivity
  · intro n
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    calc
      (n.divisors.card : ℝ) * (g n)^2 =
          ∑ d ∈ n.divisors, g n * g n := by simp [pow_two]
      _ ≤ C n := by
        apply Finset.sum_le_sum
        intro d hd
        have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
        have hdn : d ≤ n := Nat.divisor_le hd
        have hnd0 : 0 < n / d := Nat.div_pos hdn hd0
        exact mul_le_mul (hmono hd0 hdn)
          (hmono hnd0 (Nat.div_le_self n d)) (hg n) (hg d)

/-- The divisor-weighted logarithmic series converges when p > 2. -/
theorem summable_divisor_count_log_power_majorant {p : ℝ} (hp : 2 < p) :
    Summable (fun n : ℕ =>
      (n.divisors.card : ℝ) / ((n : ℝ) * Real.log (2 * (n : ℝ)) ^ p)) := by
  let q : ℝ := p / 2
  have hq : 1 < q := by dsimp [q]; linarith
  let g : ℕ → ℝ := fun n => 1 / Real.log (2 * (n : ℝ)) ^ q
  have hl (n : ℕ) : 0 ≤ Real.log (2 * (n : ℝ)) := by
    rcases n with _ | n
    · simp
    · apply Real.log_nonneg
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hg (n : ℕ) : 0 ≤ g n := by
    exact div_nonneg zero_le_one (Real.rpow_nonneg (hl n) q)
  have hmono : ∀ {m n : ℕ}, 0 < m → m ≤ n → g n ≤ g m := by
    intro m n hm hmn
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hlm : 0 < Real.log (2 * (m : ℝ)) := Real.log_pos (by linarith)
    have hlogs : Real.log (2 * (m : ℝ)) ≤ Real.log (2 * (n : ℝ)) :=
      Real.log_le_log (by positivity) (by linarith)
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hlm q)
      (Real.rpow_le_rpow hlm.le hlogs (by linarith))
  have hs : Summable (fun n : ℕ => g n / (n : ℝ)) := by
    apply (RiemannResearch.Analysis.summable_log_power_majorant hq).congr
    intro n
    dsimp [g]
    ring
  apply (summable_divisor_count_mul_sq_div_of_antitone g hg hmono hs).congr
  intro n
  have hpow : Real.log (2 * (n : ℝ)) ^ p =
      (Real.log (2 * (n : ℝ)) ^ q)^2 := by
    rw [← Real.rpow_two, ← Real.rpow_mul (hl n)]
    congr 1
    dsimp [q]
    ring
  dsimp [g]
  rw [hpow]
  ring

theorem summable_logarithmic_divisor_count_successor_majorant
    {p : ℝ} (hp : 2 < p) :
    Summable (fun k : ℕ =>
      (((k : ℝ) + 1) / Real.log (2 * ((k : ℝ) + 1)) ^ p) *
        ((3 + ((k + 1).divisors.card : ℝ)) /
          (((k : ℝ) + 1) * ((k : ℝ) + 2)))) := by
  have hs := ((RiemannResearch.Analysis.summable_log_power_majorant
    (by linarith : 1 < p)).mul_left 3).add
      (summable_divisor_count_log_power_majorant hp)
  have hs' : Summable (fun k : ℕ =>
      (3 + ((k + 1).divisors.card : ℝ)) /
        (((k : ℝ) + 1) * Real.log (2 * ((k : ℝ) + 1)) ^ p)) := by
    apply ((summable_nat_add_iff 1).mpr hs).congr
    intro k
    push_cast
    ring
  apply hs'.of_nonneg_of_le
  · intro k
    have hl : 0 ≤ Real.log (2 * ((k : ℝ) + 1)) :=
      Real.log_nonneg (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith)
    exact mul_nonneg (div_nonneg (by positivity) (Real.rpow_nonneg hl p))
      (by positivity)
  · intro k
    have hk : 0 < (k : ℝ) + 1 := by positivity
    have hl : 0 < Real.log (2 * ((k : ℝ) + 1)) := Real.log_pos (by linarith)
    have hpw : 0 < Real.log (2 * ((k : ℝ) + 1)) ^ p :=
      Real.rpow_pos_of_pos hl p
    calc
      _ = (3 + ((k + 1).divisors.card : ℝ)) /
          (((k : ℝ) + 2) * Real.log (2 * ((k : ℝ) + 1)) ^ p) := by
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_right (by linarith) hpw.le)

end RiemannResearch.NumberTheory
