import RiemannResearch.RH.CRTCarryRamanujanCoordinates
import RiemannResearch.RH.FiniteAtomCarryCRT
import RiemannResearch.RH.MixedConductorRankOne

/-! Canonical floor carries in the Pareto mixed-packet dictionary.
The divisor coordinates below specialize the CRT carry expansion to the
mixed-conductor projection of the conductor-two packet.

Source: Christian Noack's atom-to-carry question for the mixed parity projection. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization
open RiemannResearch.RH.CRTCarryRamanujan
open RiemannResearch.NumberTheory.PrimePowerCRT

private def mixedDivisors (d : ℕ) : Finset ℕ :=
  d.divisors.filter (fun q => 1 < q ∧ ¬ IsPrimePow q)

private theorem card_of_mixed_divisor {d q : ℕ} (hq : q ∈ d.divisors)
    (hgt : 1 < q) (hm : ¬ IsPrimePow q) : 2 ≤ q.primeFactors.card := by
  apply FiniteAtomCarryCRT.mixed_card_ge_two d ⟨q, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨hq, hgt, ?_⟩
  intro hone
  have hprime : q ∈ FiniteAtomCarryCRT.primeConductors d :=
    Finset.mem_filter.mpr ⟨hq, hgt, hone⟩
  obtain ⟨_, p, k, hp, hk, he⟩ := (FiniteAtomCarryCRT.mem_primeConductors_iff d q).mp hprime
  exact hm ((isPrimePow_nat_iff q).mpr ⟨p, k, hp, hk, he.symm⟩)

/-- The coefficient of packet q in the canonical floor carry at d. -/
def canonicalCarryPacketWeight (d q : ℕ) : ℝ :=
  (∑ p ∈ d.primeFactors, if q ∣ modulus d p then
    (RiemannResearch.NumberTheory.PrimePowerCRT.coefficient d p : ℝ) / (modulus d p : ℝ) else 0) - 1 / (d : ℝ)

/-- Subtract the canonical carry from its prime-power packet part and scale by d. -/
def correctedCanonicalCarry (d n : ℕ) : ℝ :=
  (d : ℝ) * ((∑ q ∈ d.divisors, if 1 < q ∧ ¬ IsPrimePow q then 0
    else canonicalCarryPacketWeight d q * ramanujanPacket q n) - (canonicalCarry d n : ℝ))

theorem correctedCanonicalCarry_eq_divisor_sum (d n : ℕ) (hd : 0 < d) :
    correctedCanonicalCarry d n =
      ∑ q ∈ d.divisors.filter (fun q => 1 < q ∧ ¬ IsPrimePow q), ramanujanPacket q n := by
  classical
  rw [correctedCanonicalCarry, canonicalCarry_packet_expansion d hd n,
    ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hm : 1 < q ∧ ¬ IsPrimePow q
  · rw [if_pos hm, if_pos hm,
      canonical_mixed_packetCoefficient d q (card_of_mixed_divisor hq hm.1 hm.2)]
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp [hd'] <;> ring
  · simp [hm, canonicalCarryPacketWeight]

/-- Hilbert vector realizing the corrected floor carry, in mixed packet coordinates. -/
def correctedCarryHilbert (d : ℕ) : ThresholdHilbert :=
  ∑ q ∈ mixedDivisors d, ramanujanPacketHilbert q

theorem hilbertSequence_correctedCarry (d n : ℕ) (hd : 0 < d) :
    hilbertSequence (correctedCarryHilbert d) n = correctedCanonicalCarry d n := by
  rw [correctedCanonicalCarry_eq_divisor_sum d n hd]
  change hilbertSequenceLinear (∑ q ∈ mixedDivisors d, ramanujanPacketHilbert q) n = _
  rw [map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro q _
  exact congrFun (hilbertSequence_ramanujanPacketHilbert q) n

/-- The corrected carries with mixed labels up to N. -/
def correctedCarrySpace (N : ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ (Set.range fun d : mixedConductors (Finset.Icc 2 N) =>
    correctedCarryHilbert d.val)

/-- Triangular divisor inversion identifies the finite mixed Gram problems. -/
theorem correctedCarrySpace_eq_mixedSpace (N : ℕ) :
    correctedCarrySpace N = mixedSpace (Finset.Icc 2 N) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    obtain ⟨hdN, _⟩ := Finset.mem_filter.mp d.property
    obtain ⟨h2d, hdle⟩ := Finset.mem_Icc.mp hdN
    apply (mixedSpace (Finset.Icc 2 N)).sum_mem
    intro q hq
    obtain ⟨hqd, h2q, hmq⟩ := Finset.mem_filter.mp hq
    have hqle := Nat.le_of_dvd (show 0 < d.val by omega) (Nat.dvd_of_mem_divisors hqd)
    exact Submodule.subset_span ⟨⟨q, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, hqle.trans hdle⟩, hmq⟩⟩, rfl⟩
  · have hpacket (d : ℕ) (hgt : 1 < d) (hdN : d ≤ N) (hm : ¬ IsPrimePow d) :
        ramanujanPacketHilbert d ∈ correctedCarrySpace N := by
      induction d using Nat.strong_induction_on with
      | h d ih =>
        have hdself : d ∈ mixedDivisors d :=
          Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩, hgt, hm⟩
        have hc : correctedCarryHilbert d ∈ correctedCarrySpace N :=
          Submodule.subset_span ⟨⟨d, Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨by omega, hdN⟩, hm⟩⟩, rfl⟩
        have ht : (∑ q ∈ (mixedDivisors d).erase d, ramanujanPacketHilbert q) ∈
            correctedCarrySpace N := by
          apply (correctedCarrySpace N).sum_mem
          intro q hq
          obtain ⟨hne, hqd⟩ := Finset.mem_erase.mp hq
          obtain ⟨hdvd, hqgt, hqm⟩ := Finset.mem_filter.mp hqd
          have hle := Nat.le_of_dvd (show 0 < d by omega) (Nat.dvd_of_mem_divisors hdvd)
          exact ih q (lt_of_le_of_ne hle hne) hqgt (hle.trans hdN) hqm
        rw [correctedCarryHilbert, ← Finset.sum_erase_add _ _ hdself] at hc
        simpa only [add_sub_cancel_left] using (correctedCarrySpace N).sub_mem hc ht
    apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    obtain ⟨hd, hm⟩ := Finset.mem_filter.mp d.property
    obtain ⟨hgt, hle⟩ := Finset.mem_Icc.mp hd
    exact hpacket d.val (by omega) hle hm

theorem mixedClosure_eq_correctedCarryClosure :
    mixedClosure = (⨆ N : ℕ, correctedCarrySpace N).topologicalClosure := by
  simp only [mixedClosure, correctedCarrySpace_eq_mixedSpace]

instance (N : ℕ) : (correctedCarrySpace N).HasOrthogonalProjection := by
  rw [correctedCarrySpace_eq_mixedSpace]
  infer_instance

/-- Exact cofinal saturation criterion in the corrected floor-carry coordinates. -/
theorem correctedCarry_capture_tendsto_iff :
    Filter.Tendsto (fun N : ℕ =>
      ‖(correctedCarrySpace N).starProjection (ramanujanPacketHilbert 2)‖ ^ 2)
      Filter.atTop (nhds (Real.log 2 - (Real.log 2) ^ 2)) ↔
      hilbertOne ∈ closedSpace := by
  simpa only [correctedCarrySpace_eq_mixedSpace] using fixed_capture_tendsto_saturation_iff

end RiemannResearch.RH.Pareto.PrimePowerSchur
