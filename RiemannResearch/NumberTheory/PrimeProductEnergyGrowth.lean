/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Growth of the prime-product primitive-energy obstruction

Source: direct elementary product bound for the derivative-optimizer research
agenda, 4 November 2026. No prime number theorem or Mertens estimate is needed.
The first two prime factors contribute 3/8 and must not be omitted.

The growth statements are unconditional. The energy consumers explicitly
retain the period-energy lower bound as a hypothesis; they do not assert that
an arbitrary legal approximant has that lower bound.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.NumberTheory.PrimeProductEnergyGrowth

/-- Product of the first n primes, using Mathlib's zero-based enumeration. -/
def ordinalPrimorial (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, Nat.nth Nat.Prime j

/-- The exact scalar L/M² when M=2^n and L is the ordinal primorial. -/
def energyScale (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, ((Nat.nth Nat.Prime j : ℕ) : ℝ) / 4

theorem energyScale_nonneg (n : ℕ) : 0 ≤ energyScale n := by
  unfold energyScale
  exact Finset.prod_nonneg (fun j _ => by positivity)

theorem energyScale_eq_primorial_quotient (n : ℕ) :
    energyScale n = (ordinalPrimorial n : ℝ) / (4 : ℝ) ^ n := by
  simp [energyScale, ordinalPrimorial, Finset.prod_div_distrib]

theorem energyScale_eq_boolean_dimension_quotient (n : ℕ) :
    energyScale n = (ordinalPrimorial n : ℝ) / ((2 : ℝ) ^ n) ^ 2 := by
  have hpow : ((2 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ n := by
    rw [pow_two, ← mul_pow]
    norm_num
  rw [hpow]
  exact energyScale_eq_primorial_quotient n

theorem five_le_nth_prime_from_two (n : ℕ) :
    5 ≤ Nat.nth Nat.Prime (n + 2) := by
  have h := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone
    (show 2 ≤ n + 2 by omega)
  simpa only [Nat.nth_prime_two_eq_five] using h

/-- Exact initial constant and elementary geometric growth; no asymptotics. -/
theorem energyScale_geometric_lower (n : ℕ) :
    (3 / 8 : ℝ) * (5 / 4 : ℝ) ^ n ≤ energyScale (n + 2) := by
  induction n with
  | zero =>
      norm_num [energyScale, Finset.prod_range_succ]
  | succ n ih =>
      have hp : (5 / 4 : ℝ) ≤
          ((Nat.nth Nat.Prime (n + 2) : ℕ) : ℝ) / 4 := by
        have hh : (5 : ℝ) ≤ ((Nat.nth Nat.Prime (n + 2) : ℕ) : ℝ) := by
          exact_mod_cast five_le_nth_prime_from_two n
        linarith
      calc
        (3 / 8 : ℝ) * (5 / 4 : ℝ) ^ (n + 1) =
            ((3 / 8 : ℝ) * (5 / 4 : ℝ) ^ n) * (5 / 4 : ℝ) := by
              rw [pow_succ]
              ring
        _ ≤ energyScale (n + 2) *
            (((Nat.nth Nat.Prime (n + 2) : ℕ) : ℝ) / 4) :=
          mul_le_mul ih hp (by norm_num) (energyScale_nonneg (n + 2))
        _ = energyScale (n + 1 + 2) := by
          rw [show n + 1 + 2 = (n + 2) + 1 by omega]
          simp only [energyScale, Finset.prod_range_succ]

/-- The scalar obstruction diverges, already along the stages n+2. -/
theorem energyScale_shift_tendsto_atTop :
    Tendsto (fun n => energyScale (n + 2)) atTop atTop := by
  apply tendsto_atTop_mono energyScale_geometric_lower
  exact Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 3 / 8)
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 5 / 4))

/-- A complete-energy estimate with any fixed positive prefactor forces escape.
The lower estimate is an explicit hypothesis, not an inferred positivity bound. -/
theorem energy_tendsto_atTop_of_period_lower (E : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c)
    (hlower : ∀ n, c * (ordinalPrimorial (n + 2) : ℝ) /
      ((2 : ℝ) ^ (n + 2)) ^ 2 ≤ E n) :
    Tendsto E atTop atTop := by
  have hlower' (n : ℕ) : c * energyScale (n + 2) ≤ E n := by
    rw [energyScale_eq_boolean_dimension_quotient, ← mul_div_assoc]
    exact hlower n
  exact tendsto_atTop_mono hlower'
    (Tendsto.const_mul_atTop hc energyScale_shift_tendsto_atTop)

/-- No fixed complete-energy budget can coexist with the stated period lower bound. -/
theorem no_uniform_energy_budget_of_period_lower (E : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c)
    (hlower : ∀ n, c * (ordinalPrimorial (n + 2) : ℝ) /
      ((2 : ℝ) ^ (n + 2)) ^ 2 ≤ E n) :
    ¬ ∃ C : ℝ, ∀ n, E n ≤ C := by
  rintro ⟨C, hC⟩
  have h := (tendsto_atTop.mp (energy_tendsto_atTop_of_period_lower E hc hlower))
    (C + 1)
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have hlow := hN N le_rfl
  have hupp := hC N
  linarith

end RiemannResearch.NumberTheory.PrimeProductEnergyGrowth
