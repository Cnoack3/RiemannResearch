/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# An elementary cubic lower bound for primorials

Source: the direct three-interval argument using Mathlib's Bertrand theorem,
`Nat.exists_prime_lt_and_le_two_mul`. Three distinct primes in (n,2n],
(2n,4n], and (4n,8n] give the bound. No prime number theorem is used.
-/

namespace RiemannResearch.NumberTheory.PrimorialPolynomialLower

theorem eight_mul_cube_le_primorial_eight_mul (n : ℕ) (hn : 0 < n) :
    8 * n ^ 3 ≤ primorial (8 * n) := by
  obtain ⟨p, hp, hnp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  obtain ⟨q, hq, hnq, hq4⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * n) (by omega)
  obtain ⟨r, hr, hnr, hr8⟩ := Nat.exists_prime_lt_and_le_two_mul (4 * n) (by omega)
  have hpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr (by omega)
  have hrpq : Nat.Coprime r (p * q) := hr.coprime_iff_not_dvd.mpr (by
    intro hd
    rcases hr.dvd_mul.mp hd with hd | hd
    · have hh := Nat.le_of_dvd hp.pos hd
      omega
    · have hh := Nat.le_of_dvd hq.pos hd
      omega)
  have hpd : p ∣ primorial (8 * n) := hp.dvd_primorial_iff.mpr (by omega)
  have hqd : q ∣ primorial (8 * n) := hq.dvd_primorial_iff.mpr (by omega)
  have hrd : r ∣ primorial (8 * n) := hr.dvd_primorial_iff.mpr (by omega)
  have hprod : p * q * r ∣ primorial (8 * n) :=
    hrpq.symm.mul_dvd_of_dvd_of_dvd (hpq.mul_dvd_of_dvd_of_dvd hpd hqd) hrd
  calc
    8 * n ^ 3 = n * (2 * n) * (4 * n) := by ring
    _ ≤ p * q * r := Nat.mul_le_mul (Nat.mul_le_mul hnp.le hnq.le) hnr.le
    _ ≤ primorial (8 * n) := Nat.le_of_dvd (primorial_pos _) hprod

theorem eight_mul_floor_cube_le_primorial (x : ℕ) (hx : 8 ≤ x) :
    8 * (x / 8) ^ 3 ≤ primorial x := by
  exact (eight_mul_cube_le_primorial_eight_mul (x / 8) (by omega)).trans
    (primorial_mono (by omega))

end RiemannResearch.NumberTheory.PrimorialPolynomialLower
