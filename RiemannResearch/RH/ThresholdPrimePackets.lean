import RiemannResearch.RH.ThresholdDilationAlgebra
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

/-!
# Exact equality of prime seed and divisible-conductor packet spans

Source: Christian Noack, `RH_Two_Seed_Threshold.tex`, September 8, 2026,
Section 2, equation (packetmodule). The proof is finite divisor subtraction
and strong induction, retaining all positive integer dilations and every
other prime factor of a packet conductor. No analytic density is asserted.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Actual Möbius packets whose conductor is divisible by a given prime. -/
def primePacketSpan (p : ℕ) : Submodule ℝ (ℕ → ℝ) :=
  Submodule.span ℝ {f | ∃ q : ℕ, 0 < q ∧ p ∣ q ∧ f = ramanujanPacket q}

private theorem quotient_divisors_subset {p q : ℕ} (hq : 0 < q) (hpq : p ∣ q) :
    (q / p).divisors ⊆ q.divisors := by
  intro d hd
  exact Nat.mem_divisors.mpr
    ⟨dvd_trans (Nat.mem_divisors.mp hd).1 ⟨p, (Nat.div_mul_cancel hpq).symm⟩,
      ne_of_gt hq⟩

/-- A divisor newly introduced by multiplication by a prime contains that prime. -/
private theorem prime_dvd_new_divisor {p q d : ℕ} (hp : p.Prime)
    (hq : 0 < q) (hpq : p ∣ q)
    (hd : d ∈ q.divisors \ (q / p).divisors) : p ∣ d := by
  by_contra hpd
  have hcop : Nat.Coprime d p := (hp.coprime_iff_not_dvd.mpr hpd).symm
  have hdq : d ∣ q := (Nat.mem_divisors.mp (Finset.mem_sdiff.mp hd).1).1
  have hmul : d ∣ p * (q / p) := by
    simpa only [Nat.mul_comm p, Nat.div_mul_cancel hpq] using hdq
  have hdp : d ∣ q / p := hcop.dvd_of_dvd_mul_left hmul
  have hqp : 0 < q / p := Nat.div_pos (Nat.le_of_dvd hq hpq) hp.pos
  exact (Finset.mem_sdiff.mp hd).2 (Nat.mem_divisors.mpr ⟨hdp, ne_of_gt hqp⟩)

/-- Exact pointwise divisor subtraction, with no discarded packet terms. -/
theorem dilation_prime_packet_sum (p q : ℕ) (hp : p.Prime)
    (hq : 0 < q) (hpq : p ∣ q) (k : ℕ) :
    dilation (q / p) (residue p) k =
      ∑ d ∈ q.divisors \ (q / p).divisors, ramanujanPacket d k := by
  rw [residue_mul_floor, Nat.div_mul_cancel hpq]
  have hqp : 0 < q / p := Nat.div_pos (Nat.le_of_dvd hq hpq) hp.pos
  have hs := Finset.sum_sdiff (f := fun d => ramanujanPacket d k)
    (quotient_divisors_subset hq hpq)
  rw [ramanujanPacket_divisor_sum q k hq,
    ramanujanPacket_divisor_sum (q / p) k hqp] at hs
  linarith

/-- Every legal prime-seed dilation is a finite sum of admissible packets. -/
theorem dilation_prime_mem_packetSpan (p m : ℕ) (hp : p.Prime) (hm : 0 < m) :
    dilation m (residue p) ∈ primePacketSpan p := by
  let q := m * p
  have hq : 0 < q := Nat.mul_pos hm hp.pos
  have hpq : p ∣ q := ⟨m, Nat.mul_comm _ _⟩
  have hqm : q / p = m := Nat.mul_div_cancel m hp.pos
  have he : dilation m (residue p) =
      ∑ d ∈ q.divisors \ (q / p).divisors, ramanujanPacket d := by
    funext k
    simpa only [hqm, Finset.sum_apply] using dilation_prime_packet_sum p q hp hq hpq k
  rw [he]
  apply (primePacketSpan p).sum_mem
  intro d hd
  apply Submodule.subset_span
  exact ⟨d, Nat.pos_of_mem_divisors (Finset.mem_sdiff.mp hd).1,
    prime_dvd_new_divisor hp hq hpq hd, rfl⟩

/-- Every admissible packet is synthesized by the prime seed and integer dilations. -/
theorem prime_packet_mem_legalSeedSpan (p : ℕ) (hp : p.Prime) (q : ℕ)
    (hq : 0 < q) (hpq : p ∣ q) :
    ramanujanPacket q ∈ legalSeedSpan {p} := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    let ds := q.divisors \ (q / p).divisors
    have hqp : 0 < q / p := Nat.div_pos (Nat.le_of_dvd hq hpq) hp.pos
    have hqmem : q ∈ ds := by
      apply Finset.mem_sdiff.mpr
      refine ⟨Nat.mem_divisors.mpr ⟨dvd_rfl, ne_of_gt hq⟩, ?_⟩
      intro h
      have hle := Nat.le_of_dvd hqp (Nat.mem_divisors.mp h).1
      have hlt := Nat.div_lt_self hq hp.one_lt
      omega
    have hrest : (∑ d ∈ ds.erase q, ramanujanPacket d) ∈ legalSeedSpan {p} := by
      apply (legalSeedSpan {p}).sum_mem
      intro d hd
      have hdq : d ∈ q.divisors := (Finset.mem_sdiff.mp (Finset.mem_erase.mp hd).2).1
      have hdn : d ≠ q := (Finset.mem_erase.mp hd).1
      have hle : d ≤ q := Nat.le_of_dvd hq (Nat.mem_divisors.mp hdq).1
      exact ih d (lt_of_le_of_ne hle hdn) (Nat.pos_of_mem_divisors hdq)
        (prime_dvd_new_divisor hp hq hpq (Finset.mem_erase.mp hd).2)
    have he : ramanujanPacket q = dilation (q / p) (residue p) -
        ∑ d ∈ ds.erase q, ramanujanPacket d := by
      funext k
      have hs := Finset.sum_erase_add (s := ds) (f := fun d => ramanujanPacket d k) hqmem
      have hg := dilation_prime_packet_sum p q hp hq hpq k
      simp only [Pi.sub_apply, Finset.sum_apply]
      change dilation (q / p) (residue p) k = ∑ d ∈ ds, ramanujanPacket d k at hg
      linarith
    rw [he]
    exact (legalSeedSpan {p}).sub_mem
      (dilation_generator_mem {p} (by simp) hqp) hrest

/-- Equality holds at the algebraic level, before any choice of topology. -/
theorem legalSeedSpan_prime_eq_packetSpan (p : ℕ) (hp : p.Prime) :
    legalSeedSpan {p} = primePacketSpan p := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨a, ha, m, hm, rfl⟩
    have ha' : a = p := Set.mem_singleton_iff.mp ha
    subst a
    exact dilation_prime_mem_packetSpan p m hp hm
  · apply Submodule.span_le.mpr
    rintro f ⟨q, hq, hpq, rfl⟩
    exact prime_packet_mem_legalSeedSpan p hp q hq hpq

/-- The two-seed span is exactly the sum of the two divisible-conductor spans.
In particular this applies to the seeds 2 and 3, with every integer dilation
and every auxiliary prime factor still present. -/
theorem legalSeedSpan_prime_pair (p r : ℕ) (hp : p.Prime) (hr : r.Prime) :
    legalSeedSpan {p, r} = primePacketSpan p ⊔ primePacketSpan r := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨a, ha, m, hm, rfl⟩
    rcases Set.mem_insert_iff.mp ha with ha | ha
    · rw [ha]
      exact (le_sup_left : primePacketSpan p ≤ primePacketSpan p ⊔ primePacketSpan r)
        (dilation_prime_mem_packetSpan p m hp hm)
    · have ha' : a = r := Set.mem_singleton_iff.mp ha
      subst a
      exact (le_sup_right : primePacketSpan r ≤ primePacketSpan p ⊔ primePacketSpan r)
        (dilation_prime_mem_packetSpan r m hr hm)
  · apply sup_le
    · rw [← legalSeedSpan_prime_eq_packetSpan p hp]
      apply Submodule.span_le.mpr
      rintro f ⟨a, ha, m, hm, rfl⟩
      have ha' : a = p := Set.mem_singleton_iff.mp ha
      subst a
      exact dilation_generator_mem {p, r} (by simp) hm
    · rw [← legalSeedSpan_prime_eq_packetSpan r hr]
      apply Submodule.span_le.mpr
      rintro f ⟨a, ha, m, hm, rfl⟩
      have ha' : a = r := Set.mem_singleton_iff.mp ha
      subst a
      exact dilation_generator_mem {p, r} (by simp) hm

end
end RiemannResearch.RH.Pareto
