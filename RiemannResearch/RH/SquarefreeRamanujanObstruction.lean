import RiemannResearch.RH.SquarefreeDilationObstruction
import RiemannResearch.RH.ArithmeticChargeEscape
import RiemannResearch.RH.ThresholdPrimePackets

/-!
# Squarefree allowed Ramanujan conductors do not suffice

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
section 8. Divisor subtraction synthesizes each squarefree allowed block using
only squarefree dilations, so the same explicit finite component separates it.
-/
namespace RiemannResearch.RH.Pareto
open scoped BigOperators Topology
open Filter PositiveSeedCone FiniteSeedComponentCharge TwoSeedThreshold
noncomputable section

private theorem componentCharge_packetCombination (S s : Finset ℕ)
    (c : ℕ → ℝ) (f : ℕ → ℕ → ℝ) :
    componentCharge S (fun k => ∑ d ∈ s, c d * f d k) =
      ∑ d ∈ s, c d * componentCharge S (f d) := by
  unfold componentCharge
  simp_rw [mobiusDifference_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

private theorem new_divisor_contains_seed (p q d : ℕ) (hp : Nat.Prime p)
    (hq : 0 < q) (hpq : p ∣ q)
    (hd : d ∈ q.divisors \ (q / p).divisors) : p ∣ d := by
  by_contra hpd
  have hcop : Nat.Coprime d p := (hp.coprime_iff_not_dvd.mpr hpd).symm
  have hdq : d ∣ q := Nat.dvd_of_mem_divisors (Finset.mem_sdiff.mp hd).1
  have hmul : d ∣ p * (q / p) := by
    simpa only [Nat.mul_comm p, Nat.div_mul_cancel hpq] using hdq
  have hdp := hcop.dvd_of_dvd_mul_left hmul
  have hqp : 0 < q / p := Nat.div_pos (Nat.le_of_dvd hq hpq) hp.pos
  exact (Finset.mem_sdiff.mp hd).2 (Nat.mem_divisors.mpr ⟨hdp, ne_of_gt hqp⟩)

/-- Exact annihilation of every squarefree allowed Ramanujan block. -/
theorem squarefree_ramanujan_componentCharge_zero (p : ℕ) (hp : p = 2 ∨ p = 3)
    (q : ℕ) (hq : 0 < q) (hpq : p ∣ q) (hsq : Squarefree q) :
    componentCharge squarefreeChargeSet (ramanujanPacket q) = 0 := by
  have hprime : Nat.Prime p := by rcases hp with rfl | rfl <;> decide
  induction q using Nat.strong_induction_on with
  | h q ih =>
    let ds := q.divisors \ (q / p).divisors
    have hqp : 0 < q / p := Nat.div_pos (Nat.le_of_dvd hq hpq) hprime.pos
    have hsqdiv : Squarefree (q / p) :=
      Squarefree.squarefree_of_dvd ⟨p, (Nat.div_mul_cancel hpq).symm⟩ hsq
    have hqmem : q ∈ ds := by
      apply Finset.mem_sdiff.mpr
      refine ⟨Nat.mem_divisors.mpr ⟨dvd_rfl, ne_of_gt hq⟩, ?_⟩
      intro h
      have hle := Nat.le_of_dvd hqp (Nat.dvd_of_mem_divisors h)
      have hlt := Nat.div_lt_self hq hprime.one_lt
      omega
    have hgen : componentCharge squarefreeChargeSet
        (dilation (q / p) (residue p)) = 0 := by
      have he : dilation (q / p) (residue p) = certificateGenerator p (q / p) := by
        funext k
        rw [residue_mul_floor]
        simp only [certificateGenerator, residue, Nat.mul_comm (q / p) p]
      rw [he, componentCharge_generator squarefreeChargeSet p (q / p)
        (fun d hd => (squarefreeChargeSet_pos_bound d hd).1) hprime.pos hqp]
      have hclosed := squarefreeChargeSet_closed p (q / p) hp
        (squarefree_not_four_dvd hsqdiv) (squarefree_not_nine_dvd hsqdiv)
      simp only [hclosed, sub_self]
    have hfun : dilation (q / p) (residue p) =
        fun k => ∑ d ∈ ds, (1 : ℝ) * ramanujanPacket d k := by
      funext k
      simpa only [one_mul] using dilation_prime_packet_sum p q hprime hq hpq k
    rw [hfun, componentCharge_packetCombination] at hgen
    simp only [one_mul] at hgen
    have hsingle : (∑ d ∈ ds, componentCharge squarefreeChargeSet (ramanujanPacket d)) =
        componentCharge squarefreeChargeSet (ramanujanPacket q) := by
      apply Finset.sum_eq_single q
      · intro d hd hdq
        have hddiv := Nat.dvd_of_mem_divisors (Finset.mem_sdiff.mp hd).1
        exact ih d (lt_of_le_of_ne (Nat.le_of_dvd hq hddiv) hdq)
          (Nat.pos_of_mem_divisors (Finset.mem_sdiff.mp hd).1)
          (new_divisor_contains_seed p q d hprime hq hpq hd)
          (Squarefree.squarefree_of_dvd hddiv hsq)
      · exact fun h => False.elim (h hqmem)
    rwa [hsingle] at hgen

/-- Arbitrary signed combinations of squarefree allowed conductors are all
annihilated by the same explicit nonzero target functional. -/
theorem squarefree_ramanujan_combination_charge_zero
    (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d ∧ Squarefree d ∧ (2 ∣ d ∨ 3 ∣ d)) :
    componentCharge squarefreeChargeSet
      (fun k => ∑ d ∈ s, c d * ramanujanPacket d k) = 0 := by
  rw [componentCharge_packetCombination]
  apply Finset.sum_eq_zero
  intro d hd
  obtain ⟨hd0, hsf, hseed⟩ := hs d hd
  rcases hseed with h2 | h3
  · rw [squarefree_ramanujan_componentCharge_zero 2 (Or.inl rfl) d hd0 h2 hsf, mul_zero]
  · rw [squarefree_ramanujan_componentCharge_zero 3 (Or.inr rfl) d hd0 h3 hsf, mul_zero]

/-- The squarefree allowed Ramanujan dictionary cannot even converge pointwise
to the constant, hence cannot approximate it in the Pareto Hilbert norm. -/
theorem squarefree_allowed_ramanujan_no_pointwise_limit
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ)
    (hs : ∀ j d, d ∈ s j → 0 < d ∧ Squarefree d ∧ (2 ∣ d ∨ 3 ∣ d)) :
    ¬ (∀ n, 0 < n → Tendsto
      (fun j => ∑ d ∈ s j, c j d * ramanujanPacket d n) atTop (𝓝 1)) := by
  intro hp
  have ht := componentCharge_tendsto_target
    (F := fun j n => ∑ d ∈ s j, c j d * ramanujanPacket d n)
    (by intro j; simp [ramanujanPacket, residue]) hp squarefreeChargeSet
    (fun d hd => (squarefreeChargeSet_pos_bound d hd).1)
  have hz (j : ℕ) := squarefree_ramanujan_combination_charge_zero (s j) (c j) (hs j)
  simp only [hz, squarefreeChargeSet_signal] at ht
  have he := tendsto_nhds_unique ht
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  norm_num at he

end
end RiemannResearch.RH.Pareto
