import RiemannResearch.RH.ParetoLaguerreCoordinates
import RiemannResearch.RH.RamanujanOrdinaryMomentsProof
import RiemannResearch.RH.IntegratedRamanujanHilbert
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# Quantitative separation of successive prime-support levels

The first surviving Laguerre coefficient of a packet separates it from all
packets having more distinct prime factors, even after taking their closed span.
The arithmetic coefficient evaluation comes from RamanujanOrdinaryMomentsProof.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.RamanujanLaguerre

/-- Closed span of packets whose conductors have more than `r` distinct primes. -/
def largerSupportPackets (r : ℕ) : Submodule ℝ ThresholdHilbert :=
  (Submodule.span ℝ {v | ∃ d : ℕ, 1 < d ∧ r < d.primeFactors.card ∧
      v = ramanujanPacketHilbert d}).topologicalClosure

/-- The `i`th bounded Laguerre coefficient kills the complete closure, including
limits of approximants with moving conductors. -/
theorem largerSupportPackets_le_readout_ker {i r : ℕ} (hi : i < r) :
    largerSupportPackets r ≤ (laguerreReadout i).ker := by
  apply Submodule.topologicalClosure_minimal _ _ (laguerreReadout i).isClosed_ker
  apply Submodule.span_le.mpr
  rintro _ ⟨d, hd, hr, rfl⟩
  change laguerreReadout i (ramanujanPacketHilbert d) = 0
  rw [readout_coeff, hilbertSequence_ramanujanPacketHilbert]
  exact (ramanujanLaguerreCancellationTarget d hd).1 i (by omega)

/-- The entire span of higher-support packets misses the base packet by at
least its first nonvanishing Laguerre coefficient. -/
theorem primeLogProduct_le_dist_largerSupportPackets {d : ℕ} (hd : 1 < d)
    {x : ThresholdHilbert} (hx : x ∈ largerSupportPackets d.primeFactors.card) :
    (∏ p ∈ d.primeFactors, Real.log (p : ℝ)) ≤ ‖ramanujanPacketHilbert d - x‖ := by
  have hcard : 0 < d.primeFactors.card := by
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
    exact Finset.card_pos.mpr ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩⟩
  have hx0 : laguerreReadout (d.primeFactors.card - 1) x = 0 :=
    largerSupportPackets_le_readout_ker
      (by omega : d.primeFactors.card - 1 < d.primeFactors.card) hx
  have hpnon : 0 ≤ ∏ p ∈ d.primeFactors, Real.log (p : ℝ) := by
    apply Finset.prod_nonneg
    intro p hp
    apply Real.log_nonneg
    exact_mod_cast (Nat.mem_primeFactors.mp hp).1.one_lt.le
  have h := readout_bound (d.primeFactors.card - 1) (ramanujanPacketHilbert d - x)
  rw [map_sub, hx0, sub_zero, readout_coeff, hilbertSequence_ramanujanPacketHilbert,
    (ramanujanLaguerreCancellationTarget d hd).2] at h
  simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hpnon] using h

/-- Every new-prime successor of every mixed base has support size at least three. -/
theorem freshPrimeMixedSuccessors_le_largerSupportPackets :
    (Submodule.span ℝ {v | ∃ q p : ℕ, 1 < q ∧ ¬ IsPrimePow q ∧ p.Prime ∧
      ¬ p ∣ q ∧ v = ramanujanPacketHilbert (p*q)}).topologicalClosure ≤
      largerSupportPackets 2 := by
  apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_topologicalClosure _)
  apply Submodule.span_le.mpr
  rintro _ ⟨q, p, hq, hm, hp, hpq, rfl⟩
  apply Submodule.le_topologicalClosure _
  apply Submodule.subset_span
  refine ⟨p*q, ?_, ?_, rfl⟩
  · exact lt_of_lt_of_le hq (Nat.le_mul_of_pos_left q hp.pos)
  · have hn : p ∉ q.primeFactors := fun h => hpq (Nat.mem_primeFactors.mp h).2.1
    have hc : 0 < q.primeFactors.card := by
      obtain ⟨a, ha, haq⟩ := Nat.exists_prime_and_dvd (by omega : q ≠ 1)
      exact Finset.card_pos.mpr ⟨a, Nat.mem_primeFactors.mpr ⟨ha, haq, by omega⟩⟩
    have hne : q.primeFactors.card ≠ 1 := fun h => hm (isPrimePow_iff_card_primeFactors_eq_one.mpr h)
    rw [Nat.primeFactors_mul hp.ne_zero (by omega), hp.primeFactors, Finset.singleton_union,
      Finset.card_insert_of_notMem hn]
    omega

/-- The conductor-six lower bound is the specialization `a=2`, `b=3`. -/
theorem twoPrimePacket_dist_mixedSuccessors {a b : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hab : a ≠ b) {x : ThresholdHilbert}
    (hx : x ∈ (Submodule.span ℝ {v | ∃ q p : ℕ, 1 < q ∧ ¬ IsPrimePow q ∧ p.Prime ∧
      ¬ p ∣ q ∧ v = ramanujanPacketHilbert (p*q)}).topologicalClosure) :
    Real.log (a : ℝ) * Real.log (b : ℝ) ≤ ‖ramanujanPacketHilbert (a*b) - x‖ := by
  have hfac : (a*b).primeFactors = {a,b} := by
    rw [Nat.primeFactors_mul ha.ne_zero hb.ne_zero, ha.primeFactors, hb.primeFactors,
      Finset.singleton_union]
  have hc : (a*b).primeFactors.card = 2 := by simp [hfac, hab]
  have hy : x ∈ largerSupportPackets (a*b).primeFactors.card := by
    rw [hc]
    exact freshPrimeMixedSuccessors_le_largerSupportPackets hx
  have h := primeLogProduct_le_dist_largerSupportPackets
    (lt_of_lt_of_le ha.one_lt (Nat.le_mul_of_pos_right a hb.pos)) hy
  simpa only [hfac, Finset.prod_insert (show a ∉ ({b} : Finset ℕ) by simp [hab]),
    Finset.prod_singleton] using h

/--
info: 'RiemannResearch.RH.Pareto.RamanujanLaguerre.primeLogProduct_le_dist_largerSupportPackets' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeLogProduct_le_dist_largerSupportPackets

end RiemannResearch.RH.Pareto.RamanujanLaguerre
