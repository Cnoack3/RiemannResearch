/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.E8.WeylIndexPacket

/-!
# The prime-marked full-Weyl E8 packet

This module kernel-checks the corrected full-Weyl arithmetic for the
`D₈`, `A₂⁴`, and `A₄²` subsystem packet. It is deliberately separate
from `WeylIndexPacket`, which records an older packet with different
reduction degrees.

The certificate proves finite arithmetic only. In particular, the final
annihilator theorem applies to an additive invariant and is not a
restriction/corestriction argument on nonabelian `H¹`.

Source: the user-provided *Prime-Marked Compatible Frames and the Remaining
Cases of Serre's Conjecture II* and its Wolfram Language certificate
(10 August 2026); the source supports the numerical statement and
computational model.
-/

namespace RiemannResearch.E8

/-- The three full-rank subsystem types in the prime-marked packet. -/
inductive PrimeMarkedSubsystem
  | d8 | a2Pow4 | a4Pow2
  deriving DecidableEq

namespace PrimeMarkedSubsystem

def normalizerOrder : PrimeMarkedSubsystem → ℕ
  | .d8 => 5_160_960
  | .a2Pow4 => 62_208
  | .a4Pow2 => 57_600

def orbitDegree : PrimeMarkedSubsystem → ℕ
  | .d8 => 135
  | .a2Pow4 => 11_200
  | .a4Pow2 => 12_096

def rootLatticeIndex : PrimeMarkedSubsystem → ℕ
  | .d8 => 2
  | .a2Pow4 => 9
  | .a4Pow2 => 5

def boundaryPrime : PrimeMarkedSubsystem → ℕ
  | .d8 => 2
  | .a2Pow4 => 3
  | .a4Pow2 => 5

def subsystemWeylOrder : PrimeMarkedSubsystem → ℕ
  | .d8 => 2 ^ 7 * Nat.factorial 8
  | .a2Pow4 => 6 ^ 4
  | .a4Pow2 => 120 ^ 2

/-- Each listed normalizer has the claimed full-Weyl orbit, is divisible by
the subsystem Weyl group, and has orbit degree one modulo its boundary
prime. -/
theorem certificate (S : PrimeMarkedSubsystem) :
    normalizerOrder S * orbitDegree S = 696_729_600 ∧
    normalizerOrder S % subsystemWeylOrder S = 0 ∧
    orbitDegree S % boundaryPrime S = 1 := by
  cases S <;>
    norm_num [normalizerOrder, orbitDegree, boundaryPrime,
      subsystemWeylOrder, Nat.factorial]

end PrimeMarkedSubsystem

/-- The exact Bézout relation for the corrected orbit degrees. -/
theorem primeMarkedPacket_bezout :
    (-73 : ℤ) * 135 - 11 * 11_200 + 11 * 12_096 = 1 := by
  norm_num

/-- The corrected orbit degrees have gcd one. -/
theorem primeMarkedPacket_gcd :
    Nat.gcd (Nat.gcd 135 11_200) 12_096 = 1 := by
  norm_num

/-- Additive shadow of the prime-marked packet: a class annihilated by all
three orbit degrees vanishes. This does not apply directly to a pointed
nonabelian cohomology set. -/
theorem eq_zero_of_primeMarkedPacket_annihilators
    {A : Type*} [AddCommGroup A] {x : A}
    (h135 : 135 • x = 0) (h11200 : 11_200 • x = 0)
    (h12096 : 12_096 • x = 0) : x = 0 := by
  have h5 : 5 • x = 0 := by
    have h27 : 27 • (5 • x) = 0 := by
      rw [← mul_nsmul]
      norm_num
      exact h135
    have h2240 : 2240 • (5 • x) = 0 := by
      rw [← mul_nsmul]
      norm_num
      exact h11200
    exact
      (nsmul_eq_zero_iff_of_coprime
        (by norm_num : Nat.Coprime 27 2240)).mp ⟨h27, h2240⟩
  exact
    (nsmul_eq_zero_iff_of_coprime
      (by norm_num : Nat.Coprime 5 12_096)).mp ⟨h5, h12096⟩

end RiemannResearch.E8
