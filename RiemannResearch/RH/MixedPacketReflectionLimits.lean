import RiemannResearch.RH.QConductorLimits
import RiemannResearch.RH.MixedPacketDensityTests
import Mathlib.Data.Nat.Prime.Infinite

/-! # Physical limits of a mixed packet and its periodic reflection

For odd primes p the signed residue combination below is J_(2p)/p.
Replacing each normalized residue by its reflection gives the periodic
reflection of the same packet.  The two families have different limits.
The distance of the reflected family to the full legal space has an
unconditional limit, whose vanishing is equivalent to RH. -/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.MixedPacketReflectionLimits
open Pareto Pareto.CoefficientStabilization ZetaTwoHilbert ZetaTwoParetoTransfer
open ArithmeticCumulative QDivisibilityDensity

/-- Apply the three signed coefficients of J_(2p)/p to a residue family. -/
def packetRow (a : ℕ → QHilbert) (p : ℕ) : QHilbert :=
  (2 : ℝ) • a (2 * p) - a p - (2 / (p : ℝ)) • a 2

private theorem row_sequence (a : ℕ → QHilbert) (p n : ℕ) :
    qSequence (packetRow a p) n =
      2 * qSequence (a (2*p)) n - qSequence (a p) n -
        (2 / (p : ℝ)) * qSequence (a 2) n := by
  change qSequenceLinear (_ - _ - _) n = _
  simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rfl

theorem packetRow_residue_eq (p : ℕ) (hp : p.Prime) (ho : 2 < p) :
    toPareto (packetRow qResidue p) =
      (p : ℝ)⁻¹ • ramanujanPacketHilbert (2*p) := by
  apply hilbertSequence_injective
  funext n
  rw [toPareto_sequence, row_sequence, hilbertSequence_smul, Pi.smul_apply,
    smul_eq_mul, Pareto.PrimePowerSchur.MixedPacketDensity.semiprime_packet_sequence
      Nat.prime_two hp (by omega)]
  simp only [qSequence_qResidue, residueFraction, Pareto.residue, Nat.cast_mul, Nat.cast_ofNat]
  have h : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp [h]
  <;> ring

/-- The reflected atom evaluated at a positive physical index is the actual
fractional residue of the negative integer; the zero anchor also agrees. -/
theorem qReflected_eq_negative_mod (d n : ℕ) (hd : 0 < d) :
    qSequence (qReflected d) n = (((-(n : ℤ)) % (d : ℤ) : ℤ) : ℝ) / (d : ℝ) := by
  rw [qReflected_sequence, Int.neg_emod]
  have h : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  by_cases hn : n = 0
  · subst n
    simp [qOneSequence, residueFraction, positiveDivisor]
  by_cases hdn : d ∣ n
  · have hdi : (d : ℤ) ∣ (n : ℤ) := by exact_mod_cast hdn
    simp [hdi, hdn, hn, qOneSequence, residueFraction, positiveDivisor,
      Nat.mod_eq_zero_of_dvd hdn]
  · have hdi : ¬ (d : ℤ) ∣ (n : ℤ) := by exact_mod_cast hdn
    simp only [hdi, if_false, Int.natAbs_natCast, Int.cast_sub, Int.cast_natCast,
      ← Int.natCast_mod, qOneSequence, hn, residueFraction, positiveDivisor, hdn, sub_zero]
    field_simp [h]

theorem reflectedRow_sequence (p n : ℕ) (hp : 0 < p) :
    qSequence (packetRow qReflected p) n =
      ((((-(n : ℤ)) % ((2 * p : ℕ) : ℤ) : ℤ) : ℝ) -
        (((-(n : ℤ)) % (p : ℤ) : ℤ) : ℝ) - (((-(n : ℤ)) % 2 : ℤ) : ℝ)) / (p : ℝ) := by
  rw [row_sequence, qReflected_eq_negative_mod _ _ (by omega),
    qReflected_eq_negative_mod _ _ hp, qReflected_eq_negative_mod _ _ (by decide)]
  push_cast
  have h : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [h]

private theorem row_tendsto (a : ℕ → QHilbert) (v : QHilbert) (p : ℕ → ℕ)
    (hp : Tendsto p atTop atTop)
    (ha : ∀ d : ℕ → ℕ, Tendsto d atTop atTop → Tendsto (fun j => a (d j)) atTop (𝓝 v)) :
    Tendsto (fun j => packetRow a (p j)) atTop (𝓝 v) := by
  have h2 : Tendsto (fun j => 2 * p j) atTop atTop :=
    tendsto_atTop_mono (fun j => by omega : ∀ j, p j ≤ 2 * p j) hp
  have hs : Tendsto (fun j => (2 : ℝ) / (p j : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, div_eq_mul_inv, one_mul] using
      (((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hp).const_mul (2 : ℝ))
  have hv : (2 : ℝ) • v - v - (0 : ℝ) • a 2 = v := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, add_smul, one_smul, zero_smul, sub_zero]
    abel
  simpa only [packetRow, hv] using
    ((((tendsto_const_nhds (x := (2 : ℝ))).smul (ha _ h2)).sub (ha _ hp)).sub
      (hs.smul (tendsto_const_nhds (x := a 2))))

theorem normalizedRow_tendsto_zero (p : ℕ → ℕ) (hp : Tendsto p atTop atTop) :
    Tendsto (fun j => packetRow qResidue (p j)) atTop (𝓝 0) :=
  row_tendsto qResidue 0 p hp qResidue_tendsto_zero

theorem reflectedRow_tendsto_one (p : ℕ → ℕ) (hp : Tendsto p atTop atTop) :
    Tendsto (fun j => packetRow qReflected (p j)) atTop (𝓝 qOne) :=
  row_tendsto qReflected qOne p hp qReflected_tendsto_one

theorem pareto_reflectedRow_tendsto_one (p : ℕ → ℕ) (hp : Tendsto p atTop atTop) :
    Tendsto (fun j => toPareto (packetRow qReflected (p j))) atTop (𝓝 hilbertOne) := by
  simpa only [Function.comp_def, toParetoCLM_apply, toPareto_qOne] using
    (toParetoCLM.continuous.tendsto qOne).comp (reflectedRow_tendsto_one p hp)

theorem normalizedMixedPacket_tendsto_zero (p : ℕ → ℕ) (hp : Tendsto p atTop atTop)
    (hpr : ∀ j, (p j).Prime) (hodd : ∀ j, 2 < p j) :
    Tendsto (fun j => (p j : ℝ)⁻¹ • ramanujanPacketHilbert (2 * p j)) atTop (𝓝 0) := by
  have h := (toParetoCLM.continuous.tendsto 0).comp (normalizedRow_tendsto_zero p hp)
  simpa only [Function.comp_def, map_zero, toParetoCLM_apply,
    packetRow_residue_eq _ (hpr _) (hodd _)] using h

/-- The closure of the graph on genuine normalized mixed packets already
contains (0,1). This prevents a closable linear periodic-reflection operator
even when its initial domain is restricted to the mixed packet span. -/
theorem zero_one_mem_mixed_reflection_graph_closure :
    ((0, hilbertOne) : ThresholdHilbert × ThresholdHilbert) ∈ closure
      {z | ∃ p : ℕ, p.Prime ∧ 2 < p ∧
        z = ((p : ℝ)⁻¹ • ramanujanPacketHilbert (2*p), toPareto (packetRow qReflected p))} := by
  let p (j : ℕ) : ℕ := (Nat.exists_infinite_primes (j + 3)).choose
  have hpr (j : ℕ) : (p j).Prime := (Nat.exists_infinite_primes (j + 3)).choose_spec.2
  have hbig (j : ℕ) : j + 3 ≤ p j := (Nat.exists_infinite_primes (j + 3)).choose_spec.1
  have hodd (j : ℕ) : 2 < p j := by have := hbig j; omega
  have ht : Tendsto p atTop atTop := tendsto_atTop_mono (fun j => (show j ≤ p j from (Nat.le_add_right j 3).trans (hbig j))) tendsto_id
  apply mem_closure_of_tendsto
    ((normalizedMixedPacket_tendsto_zero p ht hpr hodd).prodMk_nhds
      (pareto_reflectedRow_tendsto_one p ht))
  exact Eventually.of_forall fun j => ⟨p j, hpr j, hodd j, rfl⟩

theorem reflectedRow_legalDistance_tendsto (p : ℕ → ℕ) (hp : Tendsto p atTop atTop) :
    Tendsto (fun j => Metric.infDist (toPareto (packetRow qReflected (p j)))
      (closedSpace : Set ThresholdHilbert)) atTop
      (𝓝 (Metric.infDist hilbertOne (closedSpace : Set ThresholdHilbert))) :=
  (Metric.continuous_infDist_pt _).continuousAt.tendsto.comp (pareto_reflectedRow_tendsto_one p hp)

/-- Exact RH criterion in terms of the distance of reflected mixed rows to V. -/
theorem rh_iff_reflectedRow_legalDistance_zero (p : ℕ → ℕ) (hp : Tendsto p atTop atTop) :
    RiemannHypothesis ↔
      Tendsto (fun j => Metric.infDist (toPareto (packetRow qReflected (p j)))
        (closedSpace : Set ThresholdHilbert)) atTop (𝓝 0) := by
  rw [Pareto.PrimePowerSchur.CenteredMeanSnake.riemannHypothesis_iff_naturalApproximation,
    BaezDuarte.naturalApproximation_iff_one_mem]
  constructor
  · intro hm
    simpa only [Metric.infDist_zero_of_mem hm] using reflectedRow_legalDistance_tendsto p hp
  · intro ht
    have hz := tendsto_nhds_unique (reflectedRow_legalDistance_tendsto p hp) ht
    have hm := (Metric.mem_closure_iff_infDist_zero
      (show (closedSpace : Set ThresholdHilbert).Nonempty from ⟨0, closedSpace.zero_mem⟩)).mpr hz
    rw [(show IsClosed (closedSpace : Set ThresholdHilbert) from isClosed_closure).closure_eq] at hm
    exact hm

#print axioms zero_one_mem_mixed_reflection_graph_closure
#print axioms rh_iff_reflectedRow_legalDistance_zero
end RiemannResearch.RH.MixedPacketReflectionLimits
