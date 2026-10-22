/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.NumberTheory.DivisorIncidence
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Periodic functions with gcd-class jumps

Source: user-provided RH/CRT/profinite research handoff, 20 October 2026,
priority 6 (cylinder intersection). These are finite divisor-incidence and
integration identities supporting that question; no legal closure assumption
or RH assertion appears in this module. The intermediate identity retains
the complete linear slope before periodicity eliminates it.
-/

/-!
# Integrating finite gcd-class jumps

Source: user-provided RH/CRT handoff, Section 10, cylinder-intersection target.
The existing finite divisor-incidence inverse reconstructs a gcd-class
function. Integration retains its exact slope, and a period endpoint
identity eliminates that slope. The Q-Hilbert consumer lives in
`QSquarefreeCylinder`; these finite identities require no RH hypothesis.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.PeriodicDivisorJumps
open ArithmeticCumulative
open RiemannResearch.NumberTheory.DivisorIncidence

/-- Möbius coefficients of a function on the divisors of a finite period. -/
def divisorCoefficients (L : ℕ) (h : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ e ∈ L.divisors,
    (if e ∣ d then (ArithmeticFunction.moebius (d / e) : ℝ) else 0) * h e

/-- Finite divisor incidence reconstructs every gcd-class function. -/
theorem gcd_function_eq_divisor_sum (L : ℕ) (hL : 0 < L)
    (h : ℕ → ℝ) (n : ℕ) :
    h (Nat.gcd n L) = ∑ d ∈ L.divisors,
      divisorCoefficients L h d * divisorIndicator d n := by
  classical
  have hg : Nat.gcd n L ∈ L.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n L, ne_of_gt hL⟩
  symm
  calc
    _ = ∑ d ∈ L.divisors, ∑ e ∈ L.divisors,
        h e * ((if e ∣ d then (ArithmeticFunction.moebius (d/e) : ℝ) else 0) *
          (if d ∣ Nat.gcd n L then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [divisorCoefficients, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e he
      have hiff : d ∣ Nat.gcd n L ↔ d ∣ n := by
        simp [Nat.dvd_gcd_iff, Nat.dvd_of_mem_divisors hd]
      simp only [divisorIndicator, hiff]
      ring
    _ = ∑ e ∈ L.divisors, h e *
        ∑ d ∈ L.divisors,
          (if e ∣ d then (ArithmeticFunction.moebius (d/e) : ℝ) else 0) *
            (if d ∣ Nat.gcd n L then (1 : ℝ) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]
    _ = ∑ e ∈ L.divisors, h e * (if e = Nat.gcd n L then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [moebius_left_inverse L e (Nat.gcd n L) he hg]
    _ = h (Nat.gcd n L) := by
      simp [hg]

/-- Integrating a finite divisor-indicator expansion retains the exact slope. -/
theorem integrate_divisor_jumps (L : ℕ) (c f : ℕ → ℝ)
    (hj : ∀ n, f (n + 1) - f n =
      ∑ d ∈ L.divisors, c d * divisorIndicator d (n + 1)) (n : ℕ) :
    f n = f 0 + (n : ℝ) * (∑ d ∈ L.divisors, c d / (d : ℝ)) -
      ∑ d ∈ L.divisors, c d * residueFraction d n := by
  have ht : f n - f 0 = cumulative
      (fun k => ∑ d ∈ L.divisors, c d * divisorIndicator d k) n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [cumulative_succ, ← ih, ← hj n]
      ring
  have hb (d : ℕ) (hd : d ∈ L.divisors) :
      cumulative (divisorIndicator d) n =
        (n : ℝ) / (d : ℝ) - residueFraction d n := by
    have h := cumulative_balancedDivisor d n (Nat.pos_of_mem_divisors hd)
    change cumulative (fun k => divisorIndicator d k - 1 / (d : ℝ)) n = _ at h
    rw [cumulative_sub, cumulative_const] at h
    have hn : (n : ℝ) * (1 / (d : ℝ)) = (n : ℝ) / (d : ℝ) := by ring
    rw [hn] at h
    linarith
  have hs : cumulative
      (fun k => ∑ d ∈ L.divisors, c d * divisorIndicator d k) n =
      (n : ℝ) * (∑ d ∈ L.divisors, c d / (d : ℝ)) -
        ∑ d ∈ L.divisors, c d * residueFraction d n := by
    unfold cumulative
    rw [Finset.sum_comm]
    calc
      _ = ∑ d ∈ L.divisors,
          c d * ((n : ℝ) / (d : ℝ) - residueFraction d n) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [← Finset.mul_sum]
        exact congrArg (fun x : ℝ => c d * x) (hb d hd)
      _ = _ := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro d hd
        ring
  linarith

/-- Periodicity kills the slope and leaves exactly the constant and residue atoms. -/
theorem integrate_periodic_divisor_jumps (L : ℕ) (hL : 0 < L) (c f : ℕ → ℝ)
    (hp : f L = f 0)
    (hj : ∀ n, f (n + 1) - f n =
      ∑ d ∈ L.divisors, c d * divisorIndicator d (n + 1)) (n : ℕ) :
    f n = f 0 - ∑ d ∈ L.divisors, c d * residueFraction d n := by
  have hzero : (∑ d ∈ L.divisors, c d * residueFraction d L) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    simp [residueFraction, Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mem_divisors hd)]
  have h := integrate_divisor_jumps L c f hj L
  rw [hp, hzero, sub_zero] at h
  have hs : (∑ d ∈ L.divisors, c d / (d : ℝ)) = 0 := by
    have hmul : (L : ℝ) * (∑ d ∈ L.divisors, c d / (d : ℝ)) = 0 := by linarith
    exact (mul_eq_zero.mp hmul).resolve_left (by positivity)
  rw [integrate_divisor_jumps L c f hj n, hs, mul_zero, add_zero]

/-- A periodic function with gcd-class jumps is a constant plus finite residue synthesis. -/
theorem periodic_gcd_jumps_representation (L : ℕ) (hL : 0 < L) (f h : ℕ → ℝ)
    (hp : f L = f 0)
    (hj : ∀ n, f (n + 1) - f n = h (Nat.gcd (n + 1) L)) :
    ∀ n, f n = f 0 - ∑ d ∈ L.divisors,
      divisorCoefficients L h d * residueFraction d n := by
  apply integrate_periodic_divisor_jumps L hL (divisorCoefficients L h) f hp
  intro n
  rw [hj n, gcd_function_eq_divisor_sum L hL h (n + 1)]

end RiemannResearch.RH.PeriodicDivisorJumps
