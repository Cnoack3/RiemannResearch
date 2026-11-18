/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import RiemannResearch.RH.QPrimeCRTCarries

/-!
# Prime-power CRT decomposition of residue atoms

Source: the user-provided categorical atom/carry argument, priorities 14.1 and
14.6. The arithmetic CRT and prime-factorization steps use Mathlib's
`Nat.coprime_ordCompl`, `Nat.prod_primeFactors_pow_factorization`, and
`ZMod.isUnit_iff_coprime`. This extends the existing squarefree carry construction
to every positive conductor; no squarefree hypothesis is used.

The resulting floor carry is an actual integer-valued function. The coefficients
depend only on the conductor, not on a larger ambient cutoff.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.NumberTheory.PrimePowerCRT

open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.RH.QPrimeCRTCarries

/-- The maximal power of `p` dividing `d`. -/
def modulus (d p : ℕ) : ℕ := p ^ d.factorization p

theorem modulus_pos (d p : ℕ) : 0 < modulus d p :=
  Nat.ordProj_pos d p

theorem modulus_dvd (d p : ℕ) : modulus d p ∣ d :=
  Nat.ordProj_dvd d p

theorem modulus_one_lt {d p : ℕ} (hp : p ∈ d.primeFactors) :
    1 < modulus d p := by
  have hpP := (Nat.mem_primeFactors.mp hp).1
  have hv := hpP.factorization_pos_of_dvd
    (Nat.mem_primeFactors.mp hp).2.2 (Nat.mem_primeFactors.mp hp).2.1
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hv)
  have hpos : 0 < p ^ k := pow_pos hpP.pos _
  rw [modulus, hk, pow_succ]
  have := hpP.two_le
  nlinarith

theorem cofactor_coprime {d p : ℕ} (hd : d ≠ 0) (hp : p.Prime) :
    (d / modulus d p).Coprime (modulus d p) := by
  exact (Nat.coprime_ordCompl hp hd).symm.pow_right _

theorem moduli_coprime {d p q : ℕ} (hp : p ∈ d.primeFactors)
    (hq : q ∈ d.primeFactors) (hpq : p ≠ q) :
    (modulus d p).Coprime (modulus d q) := by
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes
    (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hq).1).mpr hpq)

theorem product_moduli (d : ℕ) (hd : d ≠ 0) :
    (∏ p ∈ d.primeFactors, modulus d p) = d :=
  (Nat.prod_primeFactors_pow_factorization hd).symm

/-- Canonical least nonnegative inverse of the complementary factor. -/
def coefficient (d p : ℕ) : ℕ := canonicalCoefficient d (modulus d p)

theorem coefficient_inverse {d p : ℕ} (hd : d ≠ 0) (hp : p.Prime) :
    ((d / modulus d p : ℕ) : ZMod (modulus d p)) *
      (coefficient d p : ZMod (modulus d p)) = 1 := by
  let : NeZero (modulus d p) := ⟨ne_of_gt (modulus_pos d p)⟩
  have hu := (ZMod.isUnit_iff_coprime (d / modulus d p) (modulus d p)).mpr
    (cofactor_coprime hd hp)
  simpa only [coefficient, canonicalCoefficient, ZMod.natCast_zmod_val] using
    ZMod.mul_inv_of_unit ((d / modulus d p : ℕ) : ZMod (modulus d p)) hu

theorem coefficient_bounds {d p : ℕ} (hp : p ∈ d.primeFactors) :
    1 ≤ coefficient d p ∧ coefficient d p < modulus d p := by
  let : NeZero (modulus d p) := ⟨ne_of_gt (modulus_pos d p)⟩
  let : Fact (1 < modulus d p) := ⟨modulus_one_lt hp⟩
  refine ⟨Nat.one_le_iff_ne_zero.mpr ?_, ZMod.val_lt _⟩
  intro hz
  have hi := coefficient_inverse (Nat.mem_primeFactors.mp hp).2.2
    (Nat.mem_primeFactors.mp hp).1
  simp [hz] at hi

/-- The canonical inverse table satisfies the simultaneous CRT congruence. -/
theorem canonical_modular_certificate (d : ℕ) (hd : d ≠ 0) :
    ((∑ p ∈ d.primeFactors, ((d / modulus d p : ℕ) : ℤ) *
      (coefficient d p : ℤ) : ℤ) : ZMod d) = 1 := by
  classical
  let S : ℤ := ∑ p ∈ d.primeFactors,
    ((d / modulus d p : ℕ) : ℤ) * (coefficient d p : ℤ)
  have hprime (p : ℕ) (hp : p ∈ d.primeFactors) :
      (modulus d p : ℤ) ∣ S - 1 := by
    have hs : (S : ZMod (modulus d p)) = 1 := by
      simp only [S, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
      rw [Finset.sum_eq_single p]
      · exact coefficient_inverse hd (Nat.mem_primeFactors.mp hp).1
      · intro q hq hqp
        have hc := moduli_coprime hp hq hqp.symm
        have hpq : modulus d p ∣ d / modulus d q := by
          apply hc.dvd_mul_left.mp
          have he : modulus d q * (d / modulus d q) = d := by
            simpa only [Nat.mul_comm] using Nat.div_mul_cancel (modulus_dvd d q)
          rw [he]
          exact modulus_dvd d p
        have hz : ((d / modulus d q : ℕ) : ZMod (modulus d p)) = 0 :=
          (ZMod.natCast_eq_zero_iff (d / modulus d q) (modulus d p)).mpr hpq
        simp only [hz, zero_mul]
      · intro hn
        exact (hn hp).elim
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (S - 1) (modulus d p)).mp
    simp only [Int.cast_sub, Int.cast_one, hs, sub_self]
  have hcop : (d.primeFactors : Set ℕ).Pairwise
      (fun p q => IsCoprime (modulus d p : ℤ) (modulus d q : ℤ)) := by
    intro p hp q hq hpq
    exact (moduli_coprime hp hq hpq).isCoprime
  have hdiv : (∏ p ∈ d.primeFactors, (modulus d p : ℤ)) ∣ S - 1 :=
    Finset.prod_dvd_of_coprime hcop hprime
  have hprod : (∏ p ∈ d.primeFactors, (modulus d p : ℤ)) = (d : ℤ) := by
    exact_mod_cast product_moduli d hd
  rw [hprod] at hdiv
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (S - 1) d).mpr hdiv
  simp only [Int.cast_sub, Int.cast_one] at hz
  exact sub_eq_zero.mp hz

/-- The integer charge retained when the CRT congruence is cleared. -/
theorem cleared_reciprocal_identity (d : ℕ) (hd : d ≠ 0) :
    ∃ k : ℤ, (∑ p ∈ d.primeFactors, ((d / modulus d p : ℕ) : ℤ) *
      (coefficient d p : ℤ)) = 1 + (d : ℤ) * k := by
  have hmod : (((∑ p ∈ d.primeFactors, ((d / modulus d p : ℕ) : ℤ) *
      (coefficient d p : ℤ)) - 1 : ℤ) : ZMod d) = 0 := by
    simp only [Int.cast_sub, Int.cast_one, canonical_modular_certificate d hd, sub_self]
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mp hmod
  exact ⟨k, by linarith⟩

theorem reciprocal_identity (d : ℕ) (hd : 0 < d) :
    ∃ k : ℤ, (∑ p ∈ d.primeFactors, (coefficient d p : ℝ) / (modulus d p : ℝ)) =
      1 / (d : ℝ) + (k : ℝ) := by
  obtain ⟨k, hk⟩ := cleared_reciprocal_identity d (ne_of_gt hd)
  refine ⟨k, ?_⟩
  have hsumZ : (∑ p : d.primeFactors, ((d / modulus d p.val : ℕ) : ℤ) *
      (coefficient d p.val : ℤ)) =
      ∑ p ∈ d.primeFactors, ((d / modulus d p : ℕ) : ℤ) * (coefficient d p : ℤ) :=
    Finset.sum_coe_sort d.primeFactors
      (fun p : ℕ => ((d / modulus d p : ℕ) : ℤ) * (coefficient d p : ℤ))
  have hsumR : (∑ p : d.primeFactors, (coefficient d p.val : ℝ) / (modulus d p.val : ℝ)) =
      ∑ p ∈ d.primeFactors, (coefficient d p : ℝ) / (modulus d p : ℝ) :=
    Finset.sum_coe_sort d.primeFactors
      (fun p : ℕ => (coefficient d p : ℝ) / (modulus d p : ℝ))
  have hcert : (∑ p : d.primeFactors, ((d / modulus d p.val : ℕ) : ℤ) *
      (coefficient d p.val : ℤ)) = 1 + (d : ℤ) * k := by
    rw [hsumZ]
    exact hk
  have h := reciprocal_charge d hd (fun p : d.primeFactors => modulus d p.val)
    (fun p => modulus_pos d p.val) (fun p => modulus_dvd d p.val)
    (fun p => (coefficient d p.val : ℤ)) k hcert
  simpa only [Int.cast_natCast, hsumR] using h

/-- Actual integer floor carry for the canonical maximal-prime-power inputs. -/
def canonicalCarry (d n : ℕ) : ℤ :=
  ⌊∑ p ∈ d.primeFactors, (coefficient d p : ℝ) * residueFraction (modulus d p) n⌋

/-- Every positive conductor has an exact atom/prime-power/floor-carry identity. -/
theorem atom_reconstruction (d : ℕ) (hd : 0 < d) (n : ℕ) :
    residueFraction d n =
      (∑ p ∈ d.primeFactors, (coefficient d p : ℝ) * residueFraction (modulus d p) n) -
        (canonicalCarry d n : ℝ) := by
  have hsumZ : (∑ p : d.primeFactors, ((d / modulus d p.val : ℕ) : ℤ) *
      (coefficient d p.val : ℤ)) =
      ∑ p ∈ d.primeFactors, ((d / modulus d p : ℕ) : ℤ) * (coefficient d p : ℤ) :=
    Finset.sum_coe_sort d.primeFactors
      (fun p : ℕ => ((d / modulus d p : ℕ) : ℤ) * (coefficient d p : ℤ))
  have hsumR : (∑ p : d.primeFactors, (coefficient d p.val : ℝ) *
      residueFraction (modulus d p.val) n) =
      ∑ p ∈ d.primeFactors, (coefficient d p : ℝ) * residueFraction (modulus d p) n :=
    Finset.sum_coe_sort d.primeFactors
      (fun p : ℕ => (coefficient d p : ℝ) * residueFraction (modulus d p) n)
  have hc : ((∑ p : d.primeFactors, ((d / modulus d p.val : ℕ) : ℤ) *
      (coefficient d p.val : ℤ) : ℤ) : ZMod d) = 1 := by
    rw [hsumZ]
    exact canonical_modular_certificate d (ne_of_gt hd)
  have h := residue_eq_sum_sub_carry_of_modular d hd
    (fun p : d.primeFactors => modulus d p.val)
    (fun p => modulus_pos d p.val) (fun p => modulus_dvd d p.val)
    (fun p => (coefficient d p.val : ℤ)) hc n
  simpa only [carry, canonicalCarry, Int.cast_natCast, hsumR] using h

/-- Mixed conductors cannot divide a prime-power input. This is the arithmetic
support statement needed to identify the mixed Ramanujan coordinates of a carry. -/
theorem mixed_not_dvd_prime_pow {q p a : ℕ} (hq : 2 ≤ q.primeFactors.card)
    (hp : p.Prime) : ¬ q ∣ p ^ a := by
  intro hdiv
  have hsub : q.primeFactors ⊆ {p} := by
    intro r hr
    apply Finset.mem_singleton.mpr
    have hrP := (Nat.mem_primeFactors.mp hr).1
    apply (Nat.prime_dvd_prime_iff_eq hrP hp).mp
    exact hrP.dvd_of_dvd_pow (dvd_trans (Nat.mem_primeFactors.mp hr).2.1 hdiv)
  have hc := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at hc
  linarith

end RiemannResearch.NumberTheory.PrimePowerCRT
