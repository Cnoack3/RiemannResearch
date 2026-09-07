/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.ParetoResidueDuality

/-!
# ParetoPrimePackets

Both prime multiplication identities for the genuine divisor-sum Ramanujan packets. Source: user-provided argument RH_Pareto_CRT_Enlargement_and_Dual_Obstruction_2026-09-07.md, §3, equation (3.6). The prime-dividing case is retained separately. These are finite pointwise identities, not an independence assertion.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

theorem moebius_prime_mul (p a : ℕ) (hp : p.Prime) :
    ArithmeticFunction.moebius (p*a) =
      if p ∣ a then 0 else -ArithmeticFunction.moebius a := by
  by_cases h : p ∣ a
  · rw [if_pos h]
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro hs
    exact (Nat.squarefree_iff_prime_squarefree.mp hs p hp)
      (Nat.mul_dvd_mul_left p h)
  · rw [if_neg h, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (hp.coprime_iff_not_dvd.mpr h), ArithmeticFunction.moebius_apply_prime hp]
    ring

theorem prime_divisor_transform (p q : ℕ) (hp : p.Prime) (hq : 0 < q)
    (F : ℕ → ℝ) :
    (∑ d ∈ (p*q).divisors, (ArithmeticFunction.moebius (p*q/d) : ℝ) * F d) =
      (∑ d ∈ q.divisors, (ArithmeticFunction.moebius (q/d) : ℝ) * F (p*d)) -
        if p ∣ q then 0 else
          ∑ d ∈ q.divisors, (ArithmeticFunction.moebius (q/d) : ℝ) * F d := by
  have hpos : p*q ≠ 0 := ne_of_gt (Nat.mul_pos hp.pos hq)
  have hdiv (d : ℕ) (hd : d ∈ (p*q).divisors) (hpd : ¬ p ∣ d) : d ∣ q := by
    exact (hp.coprime_iff_not_dvd.mpr hpd).symm.dvd_mul_left.mp
      (Nat.dvd_of_mem_divisors hd)
  have hyes :
      (∑ d ∈ (p*q).divisors.filter (fun d => p ∣ d),
        (ArithmeticFunction.moebius (p*q/d) : ℝ) * F d) =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius (q/d) : ℝ) * F (p*d) := by
    symm
    apply Finset.sum_bij (fun d _ => p*d)
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨Nat.mul_dvd_mul_left p (Nat.dvd_of_mem_divisors hd), hpos⟩,
        dvd_mul_right p d⟩
    · intro d hd e he h
      exact Nat.eq_of_mul_eq_mul_left hp.pos h
    · intro d hd
      rcases Finset.mem_filter.mp hd with ⟨hd, ⟨e, rfl⟩⟩
      refine ⟨e, ?_, rfl⟩
      exact Nat.mem_divisors.mpr ⟨(Nat.mul_dvd_mul_iff_left hp.pos).mp
        (Nat.dvd_of_mem_divisors hd), ne_of_gt hq⟩
    · intro d hd
      rw [Nat.mul_div_mul_left _ _ hp.pos]
  have hno :
      (∑ d ∈ (p*q).divisors.filter (fun d => ¬ p ∣ d),
        (ArithmeticFunction.moebius (p*q/d) : ℝ) * F d) =
        -(if p ∣ q then 0 else
          ∑ d ∈ q.divisors, (ArithmeticFunction.moebius (q/d) : ℝ) * F d) := by
    by_cases hpq : p ∣ q
    · simp only [hpq, ↓reduceIte, neg_zero]
      apply Finset.sum_eq_zero
      intro d hd
      rcases Finset.mem_filter.mp hd with ⟨hd, hpd⟩
      have hdq := hdiv d hd hpd
      have hquot : p ∣ q/d := by
        have he : d * (q/d) = q := Nat.mul_div_cancel' hdq
        rw [← he] at hpq
        exact (hp.dvd_mul.mp hpq).resolve_left hpd
      rw [Nat.mul_div_assoc p hdq, moebius_prime_mul p (q/d) hp, if_pos hquot]
      simp
    · simp only [hpq, ↓reduceIte]
      have hset : (p*q).divisors.filter (fun d => ¬ p ∣ d) = q.divisors := by
        ext d
        constructor
        · intro hd
          rcases Finset.mem_filter.mp hd with ⟨hd, hpd⟩
          exact Nat.mem_divisors.mpr ⟨hdiv d hd hpd, ne_of_gt hq⟩
        · intro hd
          have hdq := Nat.dvd_of_mem_divisors hd
          exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
            ⟨dvd_mul_of_dvd_right hdq p, hpos⟩, fun h => hpq (dvd_trans h hdq)⟩
      rw [hset, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      have hdq := Nat.dvd_of_mem_divisors hd
      have hquot : ¬ p ∣ q/d := fun h => hpq (dvd_trans h (Nat.div_dvd_of_dvd hdq))
      rw [Nat.mul_div_assoc p hdq, moebius_prime_mul p (q/d) hp, if_neg hquot]
      push_cast
      ring
  rw [← Finset.sum_filter_add_sum_filter_not (p*q).divisors (fun d => p ∣ d), hyes, hno]
  ring

theorem sum_moebius_div (q : ℕ) (hq : 1 < q) :
    (∑ d ∈ q.divisors, (ArithmeticFunction.moebius (q/d) : ℝ)) = 0 := by
  have h := (mobius_inversion (fun n => if n = 1 then 1 else 0) (fun _ => 1)).mp
    (by intro n hn; simp [Nat.mem_divisors, ne_of_gt hn]) q (by omega)
  simpa [ne_of_gt hq] using h

theorem ramanujanPacket_mul_prime (p q k : ℕ) (hp : p.Prime) (hq : 1 < q) :
    ramanujanPacket (p*q) k = dilation p (ramanujanPacket q) k -
      if p ∣ q then 0 else ramanujanPacket q k := by
  rw [ramanujanPacket, prime_divisor_transform p q hp (by omega)]
  have hsum : (∑ d ∈ q.divisors, (ArithmeticFunction.moebius (q/d) : ℝ) *
      residue (p*d) k) = dilation p (ramanujanPacket q) k := by
    have hr (d : ℕ) : residue (p*d) k = dilation p (residue d) k + residue p k := by
      rw [residue_mul_floor]; ring
    simp_rw [hr, mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, sum_moebius_div q hq, zero_mul, add_zero]
    unfold dilation ramanujanPacket
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [hsum]
  rfl

theorem ramanujanPacket_mul_prime_of_not_dvd (p q k : ℕ)
    (hp : p.Prime) (hq : 1 < q) (h : ¬ p ∣ q) :
    ramanujanPacket (p*q) k = dilation p (ramanujanPacket q) k - ramanujanPacket q k := by
  simpa [h] using ramanujanPacket_mul_prime p q k hp hq

theorem ramanujanPacket_mul_prime_of_dvd (p q k : ℕ)
    (hp : p.Prime) (hq : 1 < q) (h : p ∣ q) :
    ramanujanPacket (p*q) k = dilation p (ramanujanPacket q) k := by
  simpa [h] using ramanujanPacket_mul_prime p q k hp hq

end
end RiemannResearch.RH.Pareto
