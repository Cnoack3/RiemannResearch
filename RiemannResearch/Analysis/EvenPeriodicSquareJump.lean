/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Even periodic square-jump rigidity

An even real sequence invariant modulo a positive integer and satisfying
Delta f(n^2) = Delta f(n) at all positive n >= 2 is two-periodic.
Reflection supplies a second square-jump identity with the same left side;
their exact difference gives f(n+1) = f(n-1).

Source: independently developed proof in the user-directed continuation
of QDivisorLegality_Research_2026-10-16, agenda item 3, on 16 October 2026.
This reference identifies the research question, not an external theorem.
-/

namespace RiemannResearch.Analysis.EvenPeriodicSquareJump

/-- Reflection of the complete square-jump identity forces two-step equality. -/
theorem even_periodic_square_jump_two_periodic
    (f : ℤ → ℝ) (L : ℤ) (hL : 0 < L)
    (hmod : ∀ u v : ℤ, L ∣ u - v → f u = f v)
    (heven : ∀ z : ℤ, f (-z) = f z)
    (hsquare : ∀ n : ℤ, 2 ≤ n →
      f (n ^ 2) - f (n ^ 2 - 1) = f n - f (n - 1)) :
    ∀ n : ℤ, 2 ≤ n → f (n + 1) = f (n - 1) := by
  intro n hn
  let t : ℤ := 2 * (n + 1)
  let a : ℤ := L * t - n
  have ha : 2 ≤ a := by dsimp [a, t]; nlinarith
  have hsq : f (a ^ 2) = f (n ^ 2) := by
    apply hmod
    refine ⟨L * t ^ 2 - 2 * t * n, ?_⟩
    dsimp [a]
    ring
  have hsq1 : f (a ^ 2 - 1) = f (n ^ 2 - 1) := by
    apply hmod
    refine ⟨L * t ^ 2 - 2 * t * n, ?_⟩
    dsimp [a]
    ring
  have ha0 : f a = f n := by
    calc
      f a = f (-n) := hmod _ _ ⟨t, by dsimp [a]; ring⟩
      _ = f n := heven n
  have ha1 : f (a - 1) = f (n + 1) := by
    calc
      f (a - 1) = f (-(n + 1)) := hmod _ _ ⟨t, by dsimp [a]; ring⟩
      _ = f (n + 1) := heven (n + 1)
  have h1 := hsquare n hn
  have h2 := hsquare a ha
  rw [hsq, hsq1, ha0, ha1] at h2
  linarith


/-- The two positive parity values determine every two-periodic sequence. -/
theorem values_of_two_periodic (f : ℕ → ℝ)
    (h : ∀ n : ℕ, 0 < n → f (n + 2) = f n) :
    ∀ n : ℕ, 0 < n → f n = if 2 ∣ n then f 2 else f 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst n; norm_num
    by_cases h2 : n = 2
    · subst n; norm_num
    have h3 : 3 ≤ n := by omega
    have he := h (n - 2) (by omega)
    rw [show n - 2 + 2 = n by omega] at he
    rw [he, ih (n - 2) (by omega) (by omega)]
    have hmod : (n - 2) % 2 = n % 2 := by omega
    simp only [Nat.dvd_iff_mod_eq_zero, hmod]


end RiemannResearch.Analysis.EvenPeriodicSquareJump
