/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.ParetoArithmeticRepair
import RiemannResearch.RH.ParetoBoundedInteraction

/-!
# ParetoRepairObstruction

The binary repairs with old scales `3^a * 5^b` in
*Noise, signal, and arithmetic repair* (2026-09-07), §5, share a composite
arithmetic obstruction. Adding any fixed finite packet base still cannot
produce pointwise convergence to the constant target. This obstruction is
independent of smooth-number gaps and of diagonal variance estimates.
-/

open scoped BigOperators
open Filter
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- A prime at least seven cannot be twice a natural number. -/
theorem prime_ge_seven_ne_double (p n : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    p ≠ 2*n := by
  intro he
  have hn : 0 < n := by omega
  have hd : p ∣ 2*n := by simpa only [he] using (dvd_rfl : p ∣ p)
  rcases hp.dvd_mul.mp hd with hd | hd
  · have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  · have := Nat.le_of_dvd hn hd
    omega

/-- Every old `3,5`-smooth scale avoids a prime at least seven. -/
theorem prime_ge_seven_not_dvd_smooth35 (p a b : ℕ)
    (hp : p.Prime) (hp7 : 7 ≤ p) : ¬ p ∣ 3^a * 5^b := by
  have hsmall (r : ℕ) (hr0 : 0 < r) (hrp : r < p) : ¬ p ∣ r := by
    intro h
    have := Nat.le_of_dvd hr0 h
    omega
  have hpow (r : ℕ) (hr : ¬ p ∣ r) (j : ℕ) : ¬ p ∣ r^j := by
    induction j with
    | zero =>
      simpa only [pow_zero] using (hsmall 1 (by omega) (by omega))
    | succ j ih =>
      rw [pow_succ]
      intro h
      rcases hp.dvd_mul.mp h with h | h
      · exact ih h
      · exact hr h
  intro h
  rcases hp.dvd_mul.mp h with h | h
  · exact hpow 3 (hsmall 3 (by omega) (by omega)) a h
  · exact hpow 5 (hsmall 5 (by omega) (by omega)) b h

/-- The obstruction applies to every old `3,5`-smooth scale, without any
assumption about how close that scale is to the new prime. -/
theorem binaryRepairInvariant_smooth35 (p q a b : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hp7 : 7 ≤ p) (hq7 : 7 ≤ q) :
    binaryRepairInvariant p (arithmeticRepair 2 q (3^a * 5^b)) = 0 := by
  have hnd := prime_ge_seven_not_dvd_smooth35 p a b hp hp7
  have hpE : p ≠ 3^a * 5^b := by
    intro he
    exact hnd ⟨1, by omega⟩
  apply binaryRepairInvariant_arithmeticRepair p q (3^a * 5^b) hp.one_lt
  · exact prime_ge_seven_ne_double p q hp hp7
  · exact (prime_ge_seven_ne_double q p hq hq7).symm
  · exact hpE
  · exact prime_ge_seven_ne_double p (3^a * 5^b) hp hp7
  · intro he
    exact hnd ⟨2, by omega⟩
  · omega

/-- Every packet whose conductor is below the selected prime lies in the
kernel of the two-index functional. -/
theorem binaryRepairInvariant_packet_of_lt (p q : ℕ) (hp : 1 < p)
    (hq0 : 0 < q) (hqp : q < p) :
    binaryRepairInvariant p (ramanujanPacket q) = 0 := by
  have hpd : ¬ p ∣ q := by
    intro h
    have := Nat.le_of_dvd hq0 h
    omega
  have h2pd : ¬ 2*p ∣ q := by
    intro h
    have := Nat.le_of_dvd hq0 h
    omega
  unfold binaryRepairInvariant
  rw [mobiusDifference_packet (2*p) q (by omega) hq0,
    mobiusDifference_packet p q hp hq0]
  simp [hpd, h2pd]

/-- The intended constant target violates the binary repair invariant. -/
theorem binaryRepairInvariant_one (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    binaryRepairInvariant p (fun k => if k = 0 then 0 else 1) = -1 := by
  have h2p : ¬ 2 ∣ p := by
    rintro ⟨n, hn⟩
    exact prime_ge_seven_ne_double p n hp hp7 hn
  unfold binaryRepairInvariant
  rw [mobiusDifference_one (2*p) (by omega), mobiusDifference_one p hp.pos,
    moebius_prime_mul 2 p (by decide), if_neg h2p,
    ArithmeticFunction.moebius_apply_prime hp]
  norm_num

/-- A fixed finite packet base, enlarged by arbitrary finite combinations of
the smooth-scale binary directions, still satisfies the wrong invariant. -/
theorem binaryRepairInvariant_base_add_smooth35 (p : ℕ)
    (s t : Finset ℕ) (c u : ℕ → ℝ) (a b : ℕ → ℕ)
    (hp : p.Prime) (hp7 : 7 ≤ p)
    (hs : ∀ q ∈ s, 0 < q ∧ q < p)
    (ht : ∀ q ∈ t, q.Prime ∧ 7 ≤ q) :
    binaryRepairInvariant p (fun k =>
      (∑ q ∈ s, c q * ramanujanPacket q k) +
      ∑ q ∈ t, u q * arithmeticRepair 2 q (3^(a q) * 5^(b q)) k) = 0 := by
  rw [binaryRepairInvariant_add_fn]
  have hb := binaryRepairInvariant_sum_zero p s c ramanujanPacket
    (fun q hq => binaryRepairInvariant_packet_of_lt p q hp.one_lt
      (hs q hq).1 (hs q hq).2)
  have hr := binaryRepairInvariant_sum_zero p t u
    (fun q => arithmeticRepair 2 q (3^(a q) * 5^(b q)))
    (fun q hq => binaryRepairInvariant_smooth35 p q (a q) (b q) hp
      (ht q hq).1 hp7 (ht q hq).2)
  rw [hb, hr, add_zero]

/-- The finite-coordinate invariant alone forbids pointwise convergence on
the positive integers, once the functions vanish at zero. -/
theorem binaryRepairInvariant_no_pointwise_limit (p : ℕ)
    (hp : p.Prime) (hp7 : 7 ≤ p) (f : ℕ → ℕ → ℝ)
    (hz : ∀ t, binaryRepairInvariant p (f t) = 0)
    (hf0 : ∀ t, f t 0 = 0) :
    ¬ (∀ k > 0, Tendsto (fun t => f t k) atTop (nhds 1)) := by
  intro hlimit
  have hpoint (k : ℕ) : Tendsto (fun t => f t k) atTop
      (nhds (if k = 0 then 0 else 1)) := by
    by_cases hk : k = 0
    · subst k
      simpa only [hf0, ↓reduceIte] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    · simpa only [if_neg hk] using hlimit k (by omega)
  have hl : Tendsto (fun t => binaryRepairInvariant p (f t)) atTop
      (nhds (binaryRepairInvariant p (fun k => if k = 0 then 0 else 1))) :=
    (mobiusDifference_tendsto (2*p) hpoint).add
      (tendsto_const_nhds.mul (mobiusDifference_tendsto p hpoint))
  rw [binaryRepairInvariant_one p hp hp7] at hl
  simp only [hz] at hl
  have he : (0 : ℝ) = -1 := tendsto_nhds_unique tendsto_const_nhds hl
  norm_num at he

/-- Every fixed finite packet base remains insufficient after adjoining all
binary repairs with `3,5`-smooth old scales. Even the base coefficients and
the selected finite repair combination may change at every approximation
stage. Therefore no such sequence can converge pointwise to `1`. -/
theorem smooth35Repairs_fixed_base_no_pointwise_limit
    (s : Finset ℕ) (c : ℕ → ℕ → ℝ) (t : ℕ → Finset ℕ)
    (u : ℕ → ℕ → ℝ) (a b : ℕ → ℕ → ℕ)
    (hs : ∀ q ∈ s, 0 < q)
    (ht : ∀ n q, q ∈ t n → q.Prime ∧ 7 ≤ q) :
    ¬ (∀ k > 0, Tendsto (fun n =>
      (∑ q ∈ s, c n q * ramanujanPacket q k) +
      ∑ q ∈ t n, u n q * arithmeticRepair 2 q (3^(a n q) * 5^(b n q)) k)
      atTop (nhds 1)) := by
  obtain ⟨p, hpLarge, hp⟩ := Nat.exists_infinite_primes (s.sup id + 7)
  have hp7 : 7 ≤ p := by omega
  have hs' : ∀ q ∈ s, 0 < q ∧ q < p := by
    intro q hq
    have hqle : q ≤ s.sup id := Finset.le_sup (f := id) hq
    exact ⟨hs q hq, by omega⟩
  let f : ℕ → ℕ → ℝ := fun n k =>
    (∑ q ∈ s, c n q * ramanujanPacket q k) +
    ∑ q ∈ t n, u n q * arithmeticRepair 2 q (3^(a n q) * 5^(b n q)) k
  have hz (n : ℕ) : binaryRepairInvariant p (f n) = 0 :=
    binaryRepairInvariant_base_add_smooth35 p s (t n) (c n) (u n) (a n) (b n)
      hp hp7 hs' (ht n)
  have hf0 (n : ℕ) : f n 0 = 0 := by
    simp [f, ramanujanPacket, residue, arithmeticRepair]
  exact binaryRepairInvariant_no_pointwise_limit p hp hp7 f hz hf0

end
end RiemannResearch.RH.Pareto
