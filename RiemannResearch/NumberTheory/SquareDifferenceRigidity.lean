/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
/-!
# Square - difference rigidity
Source: the paper continuation of the user's four regularity criteria, 4 November 2026.
The exact squaring - orbit identity turns physical sublinearity and a weighted local
test into constancy. Alternatively, vanishing first differences suffice.
No RH assumption occurs here; QSquarefreePrimeLocalTests is the RH consumer.
-/
open Filter
open scoped Topology
namespace RiemannResearch.NumberTheory.SquareDifferenceRigidity

def squareOrbit (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => (squareOrbit n k) ^ 2

theorem squareOrbit_ge_two (n : ℕ) (hn : 2 ≤ n) :
    ∀ k, 2 ≤ squareOrbit n k := by
  intro k
  induction k with
  | zero => exact hn
  | succ k ih =>
      change 2 ≤ (squareOrbit n k) ^ 2
      nlinarith

theorem squareOrbit_strictMono (n : ℕ) (hn : 2 ≤ n) :
    StrictMono (squareOrbit n) := by
  apply strictMono_nat_of_lt_succ
  intro k
  change squareOrbit n k < (squareOrbit n k) ^ 2
  have hh := squareOrbit_ge_two n hn k
  nlinarith

/-- A square - recurrent physically sublinear sequence needs only its local
    multiplication - by - the - index test to force adjacent equality. -/
theorem adjacent_eq_of_one_weighted_test
    (h : ℕ → ℝ)
    (hsub : Tendsto (fun n : ℕ => h n / (n : ℝ)) atTop (𝓝 0))
    (hsquare : ∀ n : ℕ, 2 ≤ n →
      h (n ^ 2) - h (n ^ 2 - 1) = h n - h (n - 1))
    (hweighted : ∀ n : ℕ, 2 ≤ n →
      (n : ℝ) ^ 2 * h (n ^ 2) - ((n : ℝ) ^ 2 - 1) * h (n ^ 2 - 1) -
        (n : ℝ) * h n + ((n : ℝ) - 1) * h (n - 1) = 0)
    (n : ℕ) (hn : 2 ≤ n) : h n = h (n - 1) := by
  let δ : ℝ := h n - h (n - 1)
  have hstep (m : ℕ) (hm : 2 ≤ m) :
      h (m ^ 2) + (m : ℝ) ^ 2 * (h m - h (m - 1)) =
        h m + (m : ℝ) * (h m - h (m - 1)) := by
    have hs := hsquare m hm
    have hw := hweighted m hm
    linear_combination hw - ((m : ℝ) ^ 2 - 1) * hs
  have hinv : ∀ k : ℕ,
      (h (squareOrbit n k) - h (squareOrbit n k - 1) = δ) ∧
      h (squareOrbit n k) + (squareOrbit n k : ℝ) * δ =
        h n + (n : ℝ) * δ := by
    intro k
    induction k with
    | zero => exact ⟨rfl, rfl⟩
    | succ k ih =>
        constructor
        · change h ((squareOrbit n k) ^ 2) - h ((squareOrbit n k) ^ 2 - 1) = δ
          rw [hsquare _ (squareOrbit_ge_two n hn k), ih.1]
        · have ht := hstep (squareOrbit n k) (squareOrbit_ge_two n hn k)
          rw [ih.1] at ht
          change h ((squareOrbit n k) ^ 2) +
            (((squareOrbit n k) ^ 2 : ℕ) : ℝ) * δ = h n + (n : ℝ) * δ
          rw [Nat.cast_pow]
          exact ht.trans ih.2
  have ha : Tendsto (squareOrbit n) atTop atTop :=
    (squareOrbit_strictMono n hn).tendsto_atTop
  have heq (k : ℕ) :
      h (squareOrbit n k) / (squareOrbit n k : ℝ) =
        (h n + (n : ℝ) * δ) / (squareOrbit n k : ℝ) - δ := by
    have hne : (squareOrbit n k : ℝ) ≠ 0 := by
      exact_mod_cast (show squareOrbit n k ≠ 0 by
        have hh := squareOrbit_ge_two n hn k
        omega)
    field_simp [hne]
    nlinarith [(hinv k).2]
  have hrat : Tendsto
      (fun k : ℕ => (h n + (n : ℝ) * δ) / (squareOrbit n k : ℝ) - δ)
      atTop (𝓝 (-δ)) := by
    simpa only [zero_sub, Function.comp_def] using
      ((tendsto_const_div_atTop_nhds_zero_nat (h n + (n : ℝ) * δ)).comp ha).sub_const δ
  have hother : Tendsto
      (fun k : ℕ => h (squareOrbit n k) / (squareOrbit n k : ℝ))
      atTop (𝓝 (-δ)) := by
    apply hrat.congr'
    exact Eventually.of_forall (fun k => (heq k).symm)
  have hz : (0 : ℝ) = -δ := tendsto_nhds_unique (hsub.comp ha) hother
  have hd : δ = 0 := by linarith
  exact sub_eq_zero.mp hd

theorem constant_of_one_weighted_test
    (h : ℕ → ℝ)
    (hsub : Tendsto (fun n : ℕ => h n / (n : ℝ)) atTop (𝓝 0))
    (hsquare : ∀ n : ℕ, 2 ≤ n →
      h (n ^ 2) - h (n ^ 2 - 1) = h n - h (n - 1))
    (hweighted : ∀ n : ℕ, 2 ≤ n →
      (n : ℝ) ^ 2 * h (n ^ 2) - ((n : ℝ) ^ 2 - 1) * h (n ^ 2 - 1) -
        (n : ℝ) * h n + ((n : ℝ) - 1) * h (n - 1) = 0) :
    ∀ n : ℕ, 1 ≤ n → h n = h 1 := by
  have hall : ∀ k : ℕ, h (k + 1) = h 1 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        have hh := adjacent_eq_of_one_weighted_test h hsub hsquare hweighted
          (k + 2) (by omega)
        have he : k + 2 - 1 = k + 1 := by omega
        rw [he] at hh
        exact hh.trans ih
  intro n hn
  have hh := hall (n - 1)
  simpa only [Nat.sub_add_cancel hn] using hh


theorem constant_of_difference_tendsto_zero (h : ℕ → ℝ)
    (hsquare : ∀ n : ℕ, 2 ≤ n →
      h (n ^ 2) - h (n ^ 2 - 1) = h n - h (n - 1))
    (hdiff : Tendsto (fun n : ℕ => h n - h (n - 1)) atTop (𝓝 0)) :
    ∀ n : ℕ, 1 ≤ n → h n = h 1 := by
  have hadj (n : ℕ) (hn : 2 ≤ n) : h n = h (n - 1) := by
    have hinv : ∀ k, h (squareOrbit n k) - h (squareOrbit n k - 1) =
        h n - h (n - 1) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        change h ((squareOrbit n k) ^ 2) - h ((squareOrbit n k) ^ 2 - 1) = _
        rw [hsquare _ (squareOrbit_ge_two n hn k), ih]
    have ht := hdiff.comp (squareOrbit_strictMono n hn).tendsto_atTop
    have hc : Tendsto (fun k => h (squareOrbit n k) - h (squareOrbit n k - 1))
        atTop (𝓝 (h n - h (n - 1))) := by
      simpa only [hinv] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => h n - h (n - 1)) atTop
          (𝓝 (h n - h (n - 1))))
    exact sub_eq_zero.mp (tendsto_nhds_unique hc ht)
  have hall : ∀ k : ℕ, h (k + 1) = h 1 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      have hh := hadj (k + 2) (by omega)
      have he : k + 2 - 1 = k + 1 := by omega
      rw [he] at hh
      exact hh.trans ih
  intro n hn
  simpa only [Nat.sub_add_cancel hn] using hall (n - 1)

end RiemannResearch.NumberTheory.SquareDifferenceRigidity
