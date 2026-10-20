/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PrimeSieveSecantAlgebra
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Normed.Group.Basic
/-!
# Uniform secant limits including repeated stages

Source: user-provided TwoStageSieveObstructionResearch20261020.md.
Positive secant bounds transfer adjacent decay uniformly over all later endpoints.
The hypotheses concern real scalar sequences, independently of RH.
-/

open Filter
open scoped Topology
namespace RiemannResearch.RH.PrimeSieveSecant
theorem equal_probe_of_equal_slopes (a u : ℕ → ℝ)
    (hanti : Antitone a) (hstall : ∀ k, a (k + 1) = a k → u (k + 1) = u k)
    (i n : ℕ) (h : a (i + n) = a i) : u (i + n) = u i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hamid := hanti (show i ≤ i + n by omega)
    have haend := hanti (show i + n ≤ i+(n + 1) by omega)
    have heq : a (i + n) = a i := by rw [h] at haend; exact le_antisymm hamid haend
    have hstep : a (i + n + 1) = a (i + n) := by simpa [Nat.add_assoc, heq] using h
    calc
      u (i + (n + 1)) = u (i + n) := by simpa [Nat.add_assoc] using hstall (i + n) hstep
      _ = u i := ih heq

theorem intercept_abs_le_of_adjacent_antitone (a u : ℕ → ℝ)
    (hpos : ∀ k, 0 < a k) (hanti : Antitone a)
    (hstall : ∀ k, a (k + 1) = a k → u (k + 1) = u k)
    (i : ℕ) (e : ℝ) (he : 0 ≤ e) :
    ∀ n : ℕ,
      (∀ k, i ≤ k → k < i + n →
        |intercept (a k) (a (k + 1)) (u k) (u (k + 1))| ≤ e) →
      |intercept (a i) (a (i + n)) (u i) (u (i + n))| ≤ e := by
  intro n
  induction n with
  | zero => intro _; simpa [intercept] using he
  | succ n ih =>
    intro hadj
    have hfirst := ih (fun k hk hl => hadj k hk (by omega))
    have hlast := hadj (i + n) (by omega) (by omega)
    by_cases hlastEq : a (i + n + 1) = a (i + n)
    · have hu := hstall (i + n) hlastEq
      change |intercept (a i) (a (i + n + 1)) (u i) (u (i + n + 1))| ≤ e
      rw [hlastEq, hu]
      exact hfirst
    · by_cases hfirstEq : a (i + n) = a i
      · have hu := equal_probe_of_equal_slopes a u hanti hstall i n hfirstEq
        simpa only [hfirstEq, hu, Nat.add_assoc] using hlast
      · have hbc : a (i + n + 1) < a (i + n) :=
          lt_of_le_of_ne (hanti (by omega)) hlastEq
        have hab : a (i + n) < a i := lt_of_le_of_ne (hanti (by omega)) hfirstEq
        have hr := intercept_abs_le_split (a i) (a (i + n)) (a (i + n + 1))
          (u i) (u (i + n)) (u (i + n + 1)) e (hpos _) hbc hab hfirst hlast
        simpa [Nat.add_assoc] using hr

theorem uniform_intercept_of_tendsto_adjacent_antitone (a u : ℕ → ℝ)
    (hpos : ∀ k, 0 < a k) (hanti : Antitone a)
    (hstall : ∀ k, a (k + 1) = a k → u (k + 1) = u k)
    (hlim : Tendsto (fun k => intercept (a k) (a (k + 1)) (u k) (u (k + 1)))
      atTop (𝓝 0)) :
    ∀ ε > 0, ∃ N : ℕ, ∀ i ≥ N, ∀ j, i ≤ j →
      |intercept (a i) (a j) (u i) (u j)| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (by linarith)
  refine ⟨N, ?_⟩
  intro i hi j hij
  have hb := intercept_abs_le_of_adjacent_antitone a u hpos hanti hstall i (ε / 2)
    (by linarith) (j - i) (fun k hk _ => (show
      |intercept (a k) (a (k + 1)) (u k) (u (k + 1))| < ε / 2 by
        simpa only [Real.dist_eq, sub_zero] using hN k (hi.trans hk)).le)
  rw [Nat.add_sub_of_le hij] at hb
  linarith
end RiemannResearch.RH.PrimeSieveSecant
