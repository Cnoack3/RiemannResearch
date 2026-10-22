/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# A finite bound for equal floor quotients at distinct conductors

Source: independently developed in the user's sparse-power-cost research,
17 October 2026. For 0<a<b, equal floor quotients force n*(b-a)<a*b.
Thus common-quotient arithmetic for distinct canonical anchors leaves an
entire infinite complement. The application is the screened variance
investigation in RH/QCanonicalSchurVariance.lean; this is not an energy bound.
-/

namespace RiemannResearch.NumberTheory
theorem common_floor_quotient_bound (a b n : ℕ) (ha : 0 < a) (hab : a < b)
    (hq : n / a = n / b) : n * (b - a) < a * b := by
  have hd : 0 < b - a := Nat.sub_pos_of_lt hab
  have hba : b = a + (b - a) := (Nat.add_sub_of_le hab.le).symm
  have hlo : n / a * b ≤ n := by
    rw [hq]
    exact Nat.div_mul_le_self n b
  have hhi : n < (n / a + 1) * a := by simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ n ha
  have hqdiff : n / a * (b - a) < a := by
    have hsum : n / a * a + n / a * (b - a) < n / a * a + a := by
      calc
        _ = n / a * b := by rw [← Nat.mul_add, ← hba]
        _ ≤ n := hlo
        _ < _ := by simpa only [Nat.add_mul, Nat.one_mul] using hhi
    omega
  have hsucc : (n / a + 1) * (b - a) < b := by
    nlinarith only [hqdiff, hba]
  calc
    n * (b - a) < ((n / a + 1) * a) * (b - a) :=
      Nat.mul_lt_mul_of_pos_right hhi hd
    _ = a * ((n / a + 1) * (b - a)) := by ring
    _ < a * b := Nat.mul_lt_mul_of_pos_left hsucc ha
end RiemannResearch.NumberTheory
