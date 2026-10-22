/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic


/-!
# Factorial decay and prime selection for the Lindemann assembly

Source: Trevor Morris, `gotrevor/lean-formalizations`,
https://github.com/gotrevor/lean-formalizations/blob/bad0e21a37874f09f45072dad6225de55742e6c5/src/LeanFormalizations/NumberTheory/Transcendence/ETranscendental.lean.
The cited source supplies both statements and proof bodies. This adaptation
uses the RiemannResearch namespace and focused imports. Its concrete RH
consumer is the exact physical minimum in `ArithmeticMinimumTranscendence`.
-/

noncomputable section
open Filter
open scoped Nat Topology
namespace RiemannResearch.NumberTheory.Transcendence

/-- `B · c^p / (p-1)! → 0` as `p → ∞`: the analytic decay driving Hermite's bound.
Reindex `tendsto_pow_div_factorial_atTop` (`c^n/n! → 0`) by `p ↦ p-1`. -/
theorem tendsto_const_mul_pow_div_factorial (c B : ℝ) :
    Tendsto (fun p : ℕ => B * (c ^ p / (p - 1)!)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n : ℕ => c ^ n / n ! : ℕ → ℝ) atTop (𝓝 0) :=
    FloorSemiring.tendsto_pow_div_factorial_atTop c
  have h1 : Tendsto (fun j : ℕ => c ^ (j + 1) / j ! : ℕ → ℝ) atTop (𝓝 0) := by
    have : Tendsto (fun j : ℕ => c * (c ^ j / j !) : ℕ → ℝ) atTop (𝓝 (c * 0)) := h0.const_mul c
    rw [mul_zero] at this
    refine this.congr (fun j => ?_); rw [pow_succ]; ring
  have h2 : Tendsto (fun p : ℕ => c ^ p / (p - 1)! : ℕ → ℝ) atTop (𝓝 0) := by
    refine (h1.comp (tendsto_sub_atTop_nat 1)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with p hp
    simp only [Function.comp_apply]; rw [Nat.sub_add_cancel hp]
  have := h2.const_mul B; rw [mul_zero] at this; exact this

/-- **Prime selection** (roadmap step 2): a prime `p` exceeding any bound `M` with the
Hermite smallness `B · c^p/(p-1)! < 1`. From the decay above + infinitude of primes. -/
theorem exists_prime_smallness (c B : ℝ) (M : ℕ) :
    ∃ p : ℕ, p.Prime ∧ M < p ∧ B * (c ^ p / (p - 1)!) < 1 := by
  have hev : ∀ᶠ p : ℕ in atTop, B * (c ^ p / (p - 1)!) < 1 :=
    (tendsto_const_mul_pow_div_factorial c B).eventually_lt_const (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (max N (M + 1))
  exact ⟨p, hp_prime,
    lt_of_lt_of_le (Nat.lt_succ_self M) (le_trans (le_max_right _ _) hp_ge),
    hN p (le_trans (le_max_left _ _) hp_ge)⟩

end RiemannResearch.NumberTheory.Transcendence
