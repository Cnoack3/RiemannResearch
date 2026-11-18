/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimeCRTCarries
import RiemannResearch.RH.ParetoPacketGreenGram
import RiemannResearch.NumberTheory.PrimePowerCRTDecomposition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact integrated Ramanujan coordinates of floor carries

Source: user-provided categorical CRT priorities 14.1 and 14.6.
Ramanujan, On certain trigonometrical sums and their applications in the
 theory of numbers, Trans. Cambridge Philos. Soc. 22 (1918), 259--276,
section 2, equations (2.6)--(2.7), supplies the divisor/Mobius transform;
section 16 introduces cumulative Ramanujan sums.
https://ramanujan.sirinudi.org/Volumes/published/ram21.html

The displayed coefficient is used only on divisors of the output conductor.
For prime-power inputs, every mixed-conductor coefficient equals -1/d.
All identities are finite and pointwise; no Hilbert orthogonality or infinite
coordinate bound is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.CRTCarryRamanujan
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.RH.Pareto

private theorem fraction_packets (d n : ℕ) (hd : 0 < d) :
    residueFraction d n = (1 / (d : ℝ)) * ∑ q ∈ d.divisors, ramanujanPacket q n := by
  rw [ramanujanPacket_divisor_sum d n hd]
  simp [residueFraction, Pareto.residue, div_eq_mul_inv, mul_comm]

variable {ι : Type*} [Fintype ι]

def packetCoefficient (p : ι → ℕ) (a : ι → ℤ) (d q : ℕ) : ℝ :=
  (∑ i, if q ∣ p i then (a i : ℝ) / (p i : ℝ) else 0) - 1 / (d : ℝ)

theorem carry_packet_expansion (d : ℕ) (hd : 0 < d)
    (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpd : ∀ i, p i ∣ d)
    (a : ι → ℤ) (k : ℤ)
    (hcert : (∑ i, ((d / p i : ℕ) : ℤ) * a i) = 1 + (d : ℤ) * k) (n : ℕ) :
    (QPrimeCRTCarries.carry p a n : ℝ) =
      ∑ q ∈ d.divisors, packetCoefficient p a d q * ramanujanPacket q n := by
  have hf := QPrimeCRTCarries.residue_eq_sum_sub_carry d hd p hp hpd a k hcert n
  have hi (i : ι) :
      (a i : ℝ) * residueFraction (p i) n =
        ∑ q ∈ d.divisors, (if q ∣ p i then (a i : ℝ) / (p i : ℝ) else 0) *
          ramanujanPacket q n := by
    rw [fraction_packets (p i) n (hp i)]
    have hs : d.divisors.filter (fun q => q ∣ p i) = (p i).divisors := by
      ext q
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨_, _⟩, hqi⟩
        exact ⟨hqi, ne_of_gt (hp i)⟩
      · rintro ⟨hqi, _⟩
        exact ⟨⟨dvd_trans hqi (hpd i), ne_of_gt hd⟩, hqi⟩
    simp_rw [ite_mul, zero_mul]
    rw [← Finset.sum_filter, hs, ← Finset.mul_sum]
    ring
  have he :
      (∑ i, (a i : ℝ) * residueFraction (p i) n) - residueFraction d n =
        ∑ q ∈ d.divisors, packetCoefficient p a d q * ramanujanPacket q n := by
    simp_rw [hi]
    rw [Finset.sum_comm, fraction_packets d n hd, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    simp only [packetCoefficient, sub_mul, Finset.sum_mul]
  linarith

theorem packetCoefficient_of_absent (p : ι → ℕ) (a : ι → ℤ) (d q : ℕ)
    (h : ∀ i, ¬ q ∣ p i) :
    packetCoefficient p a d q = -1 / (d : ℝ) := by
  simp [packetCoefficient, h, div_eq_mul_inv]

theorem mixed_packetCoefficient (p : ι → ℕ) (a : ι → ℤ) (d q : ℕ)
    (hp : ∀ i, 0 < p i) (hprime : ∀ i, (p i).primeFactors.card ≤ 1)
    (hq : 2 ≤ q.primeFactors.card) :
    packetCoefficient p a d q = -1 / (d : ℝ) := by
  apply packetCoefficient_of_absent
  intro i hqi
  have hle := Finset.card_le_card (Nat.primeFactors_mono hqi (ne_of_gt (hp i)))
  have hi := hprime i
  omega

end RiemannResearch.RH.CRTCarryRamanujan

namespace RiemannResearch.RH.CRTCarryRamanujan
open RiemannResearch.RH.Pareto
open RiemannResearch.NumberTheory.PrimePowerCRT

/-- Exact packet coordinates of the canonical full prime-power floor carry. -/
theorem canonicalCarry_packet_expansion (d : ℕ) (hd : 0 < d) (n : ℕ) :
    (canonicalCarry d n : ℝ) =
      ∑ q ∈ d.divisors,
        ((∑ p ∈ d.primeFactors,
          if q ∣ modulus d p then (coefficient d p : ℝ) / (modulus d p : ℝ) else 0) -
          1 / (d : ℝ)) * ramanujanPacket q n := by
  obtain ⟨k, hk⟩ := cleared_reciprocal_identity d (ne_of_gt hd)
  have hsumZ : (∑ p : d.primeFactors, ((d / modulus d p.val : ℕ) : ℤ) *
      (coefficient d p.val : ℤ)) =
      ∑ p ∈ d.primeFactors, ((d / modulus d p : ℕ) : ℤ) * (coefficient d p : ℤ) :=
    Finset.sum_coe_sort d.primeFactors
      (fun p : ℕ => ((d / modulus d p : ℕ) : ℤ) * (coefficient d p : ℤ))
  have hsumC : (∑ p : d.primeFactors, (coefficient d p.val : ℝ) *
      ArithmeticCumulative.residueFraction (modulus d p.val) n) =
      ∑ p ∈ d.primeFactors, (coefficient d p : ℝ) *
        ArithmeticCumulative.residueFraction (modulus d p) n :=
    Finset.sum_coe_sort d.primeFactors (fun p : ℕ => (coefficient d p : ℝ) *
      ArithmeticCumulative.residueFraction (modulus d p) n)
  have hsumA (q : ℕ) : (∑ p : d.primeFactors,
      if q ∣ modulus d p.val then (coefficient d p.val : ℝ) / (modulus d p.val : ℝ) else 0) =
      ∑ p ∈ d.primeFactors,
        if q ∣ modulus d p then (coefficient d p : ℝ) / (modulus d p : ℝ) else 0 :=
    Finset.sum_coe_sort d.primeFactors (fun p : ℕ =>
      if q ∣ modulus d p then (coefficient d p : ℝ) / (modulus d p : ℝ) else 0)
  have hc : (∑ p : d.primeFactors, ((d / modulus d p.val : ℕ) : ℤ) *
      (coefficient d p.val : ℤ)) = 1 + (d : ℤ) * k := by
    rw [hsumZ]
    exact hk
  have h := carry_packet_expansion d hd (fun p : d.primeFactors => modulus d p.val)
    (fun p => modulus_pos d p.val) (fun p => modulus_dvd d p.val)
    (fun p => (coefficient d p.val : ℤ)) k hc n
  simpa only [QPrimeCRTCarries.carry, canonicalCarry, packetCoefficient,
    Int.cast_natCast, hsumC, hsumA] using h

/-- For mixed divisors of the output conductor, the canonical carry expansion
has coefficient `-1/d`; the prime-power inverse representatives have no contribution there. -/
theorem canonical_mixed_packetCoefficient (d q : ℕ)
    (hq : 2 ≤ q.primeFactors.card) :
    ((∑ p ∈ d.primeFactors,
      if q ∣ modulus d p then (coefficient d p : ℝ) / (modulus d p : ℝ) else 0) -
      1 / (d : ℝ)) = -1 / (d : ℝ) := by
  have hz : (∑ p ∈ d.primeFactors,
      if q ∣ modulus d p then (coefficient d p : ℝ) / (modulus d p : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hn := mixed_not_dvd_prime_pow (a := d.factorization p) hq
      (Nat.mem_primeFactors.mp hp).1
    have hn' : ¬ q ∣ modulus d p := hn
    exact if_neg hn'
  rw [hz]
  ring

end RiemannResearch.RH.CRTCarryRamanujan
