/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.ModEq
import Lean.Elab.Tactic.Omega

/-!
# Positive powers in squarefree residue quotients

Source: the user-directed cylinder-intersection continuation, 20 October 2026.
Splitting a squarefree modulus into a gcd and its coprime complement allows
Euler's theorem and CRT to collapse every gcd class to one power residue.
The consumer is the complete-Q periodic squarefree closure classification.
-/

namespace RiemannResearch.NumberTheory.SquarefreePowerCongruence

/-- Equal gcd classes in a squarefree quotient have a common positive power. -/
theorem exists_power_modEq_of_gcd_eq (L : ℕ) (hL : 0 < L) (hs : Squarefree L)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (hg : Nat.gcd n L = Nat.gcd m L) :
    ∃ k : ℕ, k ≠ 0 ∧ Nat.ModEq L (n ^ k) (m ^ k) := by
  let g := Nat.gcd n L
  let q := L / g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right n hL
  have hgL : g ∣ L := Nat.gcd_dvd_right n L
  have hgn : g ∣ n := Nat.gcd_dvd_left n L
  have hgm : g ∣ m := by simpa [g, hg] using Nat.gcd_dvd_left m L
  have hqpos : 0 < q := Nat.div_pos (Nat.le_of_dvd hL hgL) hgpos
  have hqn : n.Coprime q := by
    simpa [q, g, Nat.gcd_comm] using
      (Nat.coprime_div_gcd_of_squarefree hs (ne_of_gt hn)).symm
  have hqm : m.Coprime q := by
    simpa [q, g, hg, Nat.gcd_comm] using
      (Nat.coprime_div_gcd_of_squarefree hs (ne_of_gt hm)).symm
  have hgq : g.Coprime q := hqn.of_dvd_left hgn
  have hk : q.totient ≠ 0 := ne_of_gt (Nat.totient_pos.mpr hqpos)
  refine ⟨q.totient, hk, ?_⟩
  have heqQ : Nat.ModEq q (n ^ q.totient) (m ^ q.totient) :=
    (Nat.ModEq.pow_totient hqn).trans (Nat.ModEq.pow_totient hqm).symm
  have heqG : Nat.ModEq g (n ^ q.totient) (m ^ q.totient) := by
    exact (hgn.modEq_zero_nat.pow q.totient).trans
      (hgm.modEq_zero_nat.pow q.totient).symm
  have heq : Nat.ModEq (g * q) (n ^ q.totient) (m ^ q.totient) :=
    (Nat.modEq_and_modEq_iff_modEq_mul hgq).mp ⟨heqG, heqQ⟩
  simpa [q, Nat.mul_div_cancel' hgL] using heq

/-- Periodicity plus invariance under positive powers forces gcd-class invariance. -/
theorem eq_of_gcd_eq (L : ℕ) (hL : 0 < L) (hs : Squarefree L)
    {α : Type*} (f : ℕ → α)
    (hp : ∀ n m, 2 ≤ n → 2 ≤ m → Nat.ModEq L n m → f n = f m)
    (hpow : ∀ n k, 2 ≤ n → k ≠ 0 → f (n ^ k) = f n)
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (hg : Nat.gcd n L = Nat.gcd m L) :
    f n = f m := by
  obtain ⟨k, hk, heq⟩ := exists_power_modEq_of_gcd_eq L hL hs n m (by omega) (by omega) hg
  have hge (a : ℕ) (ha : 2 ≤ a) : 2 ≤ a ^ k := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [pow_succ]
    have hh : 0 < a ^ j := pow_pos (by omega) _
    have hh1 : 1 ≤ a ^ j := by omega
    have ht := Nat.mul_le_mul_right a hh1
    simp only [one_mul] at ht
    exact le_trans ha ht
  rw [← hpow n k hn hk, ← hpow m k hm hk]
  exact hp _ _ (hge n hn) (hge m hm) heq

end RiemannResearch.NumberTheory.SquarefreePowerCongruence
