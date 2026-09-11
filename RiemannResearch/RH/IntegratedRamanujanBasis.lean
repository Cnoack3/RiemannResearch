import RiemannResearch.RH.ParetoPrimePackets
import RiemannResearch.RH.ThresholdDilationAlgebra
import Mathlib.Data.Finset.Max

/-!
# Integrated Ramanujan coordinates for legal Pareto packets

Source: user-provided September 11, 2026 conversation. The existing
`ramanujanPacket` is the integrated Ramanujan function B_d. This module proves
independence of arbitrary finite
families of positive conductors greater than one and the exact allowed-conductor
span characterization. Antiderivative identities already live in
`ParetoPacketGreenGram`. Independence is algebraic;
no completeness or uniform inverse-Gram estimate is asserted.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- No nonzero finite coefficient vector can annihilate the integrated packets.
The proof extracts the largest conductor with nonzero coefficient using the
actual Möbius difference functional, with no uniform-measure orthogonality
hypothesis. -/
theorem ramanujanPacket_finite_independent (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ q ∈ s, 1 < q)
    (hz : ∀ k : ℕ, ∑ q ∈ s, c q * ramanujanPacket q k = 0) :
    ∀ q ∈ s, c q = 0 := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨q, hqs, hcq⟩ := h
  let t := s.filter (fun q => c q ≠ 0)
  have ht : t.Nonempty := ⟨q, Finset.mem_filter.mpr ⟨hqs, hcq⟩⟩
  let m := t.max' ht
  have hmt : m ∈ t := Finset.max'_mem t ht
  have hms : m ∈ s := (Finset.mem_filter.mp hmt).1
  have hcm : c m ≠ 0 := (Finset.mem_filter.mp hmt).2
  have hm : 1 < m := hs m hms
  have hzero : mobiusDifference m
      (fun k => ∑ q ∈ s, c q * ramanujanPacket q k) = 0 := by
    simp [mobiusDifference, hz]
  rw [mobiusDifference_sum] at hzero
  have hsingle : (∑ q ∈ s, c q * mobiusDifference m (ramanujanPacket q)) =
      c m * (-(m : ℝ)) := by
    rw [Finset.sum_eq_single m]
    · have hm0 : m ≠ 0 := by omega
      simp [mobiusDifference_packet m m hm (by omega), Nat.div_self (show 0 < m by omega)]
    · intro b hbs hbm
      by_cases hcb : c b = 0
      · simp [hcb]
      · have hbt : b ∈ t := Finset.mem_filter.mpr ⟨hbs, hcb⟩
        have hbmle : b ≤ m := Finset.le_max' t b hbt
        have hnd : ¬ m ∣ b := by
          intro hd
          have hmb := Nat.le_of_dvd (show 0 < b by have := hs b hbs; omega) hd
          exact hbm (by omega)
        rw [mobiusDifference_packet m b hm (by have := hs b hbs; omega)]
        simp [hnd]
    · exact fun h => False.elim (h hms)
  rw [hsingle] at hzero
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  exact (mul_ne_zero hcm (neg_ne_zero.mpr hmR)) hzero

/-- At a prime conductor the integrated packet is the original residue seed. -/
theorem ramanujanPacket_prime_eq_residue (p : ℕ) (hp : p.Prime) :
    ramanujanPacket p = residue p := by
  funext k
  rw [ramanujanPacket, hp.divisors,
    Finset.sum_insert (by simpa using hp.ne_one.symm), Finset.sum_singleton]
  simp [residue, Nat.div_self hp.pos, Nat.mod_one]

/-- Multiplication of the conductor by a prime preserves actual finite legality. -/
theorem ramanujanPacket_prime_mul_mem (A : Set ℕ) (r q : ℕ)
    (hr : r.Prime) (hq : 1 < q)
    (hlegal : ramanujanPacket q ∈ legalSeedSpan A) :
    ramanujanPacket (r * q) ∈ legalSeedSpan A := by
  have he : ramanujanPacket (r * q) = dilation r (ramanujanPacket q) -
      (if r ∣ q then 0 else ramanujanPacket q) := by
    funext k
    by_cases h : r ∣ q <;>
      simpa [h] using ramanujanPacket_mul_prime r q k hr hq
  rw [he]
  apply (legalSeedSpan A).sub_mem
  · exact legalSeedSpan_dilation A hlegal r hr.pos
  · split_ifs
    · exact (legalSeedSpan A).zero_mem
    · exact hlegal

/-- Every multiple of a seed prime gives a legal integrated Ramanujan packet.
This permits arbitrary other prime factors in the conductor. -/
theorem ramanujanPacket_seed_multiple_mem (A : Set ℕ) (p : ℕ)
    (hp : p.Prime) (hpA : p ∈ A) (m : ℕ) (hm : 0 < m) :
    ramanujanPacket (p * m) ∈ legalSeedSpan A := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm1 : m = 1
    · subst m
      rw [Nat.mul_one, ramanujanPacket_prime_eq_residue p hp]
      simpa [dilation_one] using
        dilation_generator_mem A (m := 1) hpA (by norm_num)
    · obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hm1
      have hspos : 0 < m / r := Nat.div_pos (Nat.le_of_dvd hm hrd) hr.pos
      have hslt : m / r < m := Nat.div_lt_self hm hr.one_lt
      have hps : 1 < p * (m / r) := by
        have h := Nat.mul_le_mul_left p hspos
        nlinarith [hp.two_le]
      have hrec := ih (m / r) hslt hspos
      have hnew := ramanujanPacket_prime_mul_mem A r (p * (m / r)) hr hps hrec
      have he : r * (p * (m / r)) = p * m := by
        calc
          _ = p * (r * (m / r)) := by ring
          _ = p * m := by rw [Nat.mul_div_cancel' hrd]
      simpa [he] using hnew

theorem ramanujanPacket_twoSeed_mem (d : ℕ) (hd : 0 < d)
    (hallowed : 2 ∣ d ∨ 3 ∣ d) :
    ramanujanPacket d ∈ legalSeedSpan ({2, 3} : Set ℕ) := by
  rcases hallowed with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · exact ramanujanPacket_seed_multiple_mem _ 2 (by decide) (by simp) m (by omega)
  · exact ramanujanPacket_seed_multiple_mem _ 3 (by decide) (by simp) m (by omega)

/-- All finitely supported real coefficients on allowed conductors are legal. -/
theorem ramanujanPacket_allowed_sum_mem (s : Finset ℕ) (H : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d ∧ (2 ∣ d ∨ 3 ∣ d)) :
    (∑ d ∈ s, H d • ramanujanPacket d) ∈ legalSeedSpan ({2, 3} : Set ℕ) := by
  apply (legalSeedSpan ({2, 3} : Set ℕ)).sum_mem
  intro d hd
  exact (legalSeedSpan ({2, 3} : Set ℕ)).smul_mem (H d)
    (ramanujanPacket_twoSeed_mem d (hs d hd).1 (hs d hd).2)

/-- Exact synthesis of a legal prime-seed generator by its newly introduced
divisor conductors. No norm estimate or limiting interchange is used. -/
theorem dilation_prime_eq_ramanujan_sum (p m : ℕ) (hp : p.Prime) (hm : 0 < m) :
    dilation m (residue p) =
      ∑ d ∈ (m * p).divisors.filter (fun d => ¬ d ∣ m), ramanujanPacket d := by
  classical
  have hfilter : (m * p).divisors.filter (fun d => d ∣ m) = m.divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨_, _⟩, hdm⟩
      exact ⟨hdm, ne_of_gt hm⟩
    · rintro ⟨hdm, _⟩
      exact ⟨⟨dvd_mul_of_dvd_left hdm p, ne_of_gt (Nat.mul_pos hm hp.pos)⟩, hdm⟩
  funext k
  simp only [Finset.sum_apply]
  rw [residue_mul_floor,
    ← ramanujanPacket_divisor_sum (m * p) k (Nat.mul_pos hm hp.pos),
    ← ramanujanPacket_divisor_sum m k hm,
    ← Finset.sum_filter_add_sum_filter_not (m * p).divisors (fun d => d ∣ m),
    hfilter]
  ring

/-- The allowed integrated Ramanujan packets are exactly a basis of the
algebraic two-seed legal span; the separate independence theorem supplies
uniqueness of their finite coordinates. -/
theorem twoSeedSpan_eq_ramanujanSpan :
    legalSeedSpan ({2, 3} : Set ℕ) =
      Submodule.span ℝ {f : ℕ → ℝ | ∃ d : ℕ,
        1 < d ∧ (2 ∣ d ∨ 3 ∣ d) ∧ f = ramanujanPacket d} := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨p, hpA, m, hm, rfl⟩
    have hp : p.Prime := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpA
      rcases hpA with rfl | rfl <;> decide
    rw [dilation_prime_eq_ramanujan_sum p m hp hm]
    apply Submodule.sum_mem
    intro d hd
    obtain ⟨hdprod, hnot⟩ := Finset.mem_filter.mp hd
    have hdpos := Nat.pos_of_mem_divisors hdprod
    have hd1 : 1 < d := by
      have hne : d ≠ 1 := by intro he; subst d; exact hnot (one_dvd m)
      omega
    have hpd : p ∣ d := by
      by_contra h
      have hcop := (hp.coprime_iff_not_dvd.mpr h).symm
      have hdiv : d ∣ p * m := by
        simpa [Nat.mul_comm] using Nat.dvd_of_mem_divisors hdprod
      exact hnot (hcop.dvd_mul_left.mp hdiv)
    have hallowed : 2 ∣ d ∨ 3 ∣ d := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpA
      rcases hpA with rfl | rfl
      · exact Or.inl hpd
      · exact Or.inr hpd
    exact Submodule.subset_span ⟨d, hd1, hallowed, rfl⟩
  · apply Submodule.span_le.mpr
    rintro f ⟨d, hd, ha, rfl⟩
    exact ramanujanPacket_twoSeed_mem d (by omega) ha

end
end RiemannResearch.RH.Pareto
