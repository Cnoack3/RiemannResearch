import RiemannResearch.RH.PacketReflectionTower
import RiemannResearch.RH.MixedConductorHilbertBasis
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Closure of periodic reflection on the mixed packets

A single tower at conductors 6 times powers of 2 supplies the vertical constant.
The reflection formula then determines every fibre of the graph closure.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.PacketReflectionTower
open PrimePowerSchur MixedConductorBasis

/-- Closure in the product of complete Pareto spaces of the linear span of
actual mixed packet / periodic reflection pairs. -/
def mixedReflectionRelation : Submodule ℝ (ThresholdHilbert × ThresholdHilbert) :=
  (Submodule.span ℝ (Set.range fun q : MixedConductorBasis.Index =>
    (ramanujanPacketHilbert q.val, reflectedPacket q.val))).topologicalClosure

private theorem reflection_pair_mem (q : MixedConductorBasis.Index) :
    (ramanujanPacketHilbert q.val, reflectedPacket q.val) ∈ mixedReflectionRelation :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨q, rfl⟩)

private theorem vertical (a : ℝ) :
    ((0, a • hilbertOne) : ThresholdHilbert × ThresholdHilbert) ∈ mixedReflectionRelation := by
  have hm : ¬ IsPrimePow 6 := by decide +kernel
  have hgen (k : ℕ) : (scaledPacket 2 6 k, scaledReflection 2 6 k) ∈ mixedReflectionRelation := by
    have h6 : 6 ∣ 2^k*6 := dvd_mul_left _ _
    have hgt : 1 < 2^k*6 := by have : 0 < 2^k := pow_pos (by decide) k; omega
    let i : MixedConductorBasis.Index := ⟨2^k*6, hgt, fun h => hm (h.dvd h6 (by decide))⟩
    exact mixedReflectionRelation.smul_mem ((2:ℝ)⁻¹^k) (reflection_pair_mem i)
  have hlim := (scaledPacket_tendsto_zero 2 6 Nat.prime_two (by decide) (by decide)).prodMk_nhds
    (scaledReflection_tendsto 2 6 Nat.prime_two (by decide) (by decide))
  have hc : IsClosed (mixedReflectionRelation : Set (ThresholdHilbert × ThresholdHilbert)) :=
    isClosed_closure
  have hpair := hc.mem_of_tendsto hlim (Eventually.of_forall hgen)
  have hφ : ((6 : ℕ).totient : ℝ) = 2 := by
    exact_mod_cast (show (6 : ℕ).totient = 2 by decide +kernel)
  rw [hφ] at hpair
  have he : a/2 * 2 = a := by ring
  simpa only [Prod.smul_mk, smul_zero, smul_smul, he] using
    mixedReflectionRelation.smul_mem (a/2) hpair

/-- The vertical ambiguity is exactly the constants, and the first coordinates
range over the entire mixed closure. -/
theorem mem_mixedReflectionRelation_iff (x y : ThresholdHilbert) :
    (x,y) ∈ mixedReflectionRelation ↔ x ∈ mixedClosure ∧
      y + hilbertBackwardShiftContinuous x ∈ Submodule.span ℝ {hilbertOne} := by
  let F := ContinuousLinearMap.fst ℝ ThresholdHilbert ThresholdHilbert
  let D := ContinuousLinearMap.snd ℝ ThresholdHilbert ThresholdHilbert +
    hilbertBackwardShiftContinuous.comp F
  let L := Submodule.span ℝ {hilbertOne}
  let W := (mixedClosure.comap F.toLinearMap) ⊓ (L.comap D.toLinearMap)
  have hW : IsClosed (W : Set (ThresholdHilbert × ThresholdHilbert)) :=
    (show IsClosed (mixedClosure : Set ThresholdHilbert) from isClosed_closure).preimage F.continuous |>.inter
      (L.closed_of_finiteDimensional.preimage D.continuous)
  have hincl : mixedReflectionRelation ≤ W := by
    apply Submodule.topologicalClosure_minimal _ _ hW
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    refine ⟨(MixedConductorBasis.packet q).property, ?_⟩
    change reflectedPacket q.val + hilbertBackwardShift (ramanujanPacketHilbert q.val) ∈ L
    rw [reflectedPacket, sub_add_cancel]
    exact L.smul_mem _ (Submodule.subset_span (Set.mem_singleton _))
  constructor
  · exact fun h => hincl h
  · rintro ⟨hx, hy⟩
    let B := (ContinuousLinearMap.id ℝ ThresholdHilbert).prod (-hilbertBackwardShiftContinuous)
    have hG : IsClosed (mixedReflectionRelation : Set (ThresholdHilbert × ThresholdHilbert)) :=
      isClosed_closure
    have hbase : mixedClosure ≤ mixedReflectionRelation.comap B.toLinearMap := by
      rw [← MixedConductorBasis.span_packets_closure]
      apply Submodule.topologicalClosure_minimal _ _ (hG.preimage B.continuous)
      apply Submodule.span_le.mpr
      rintro _ ⟨q, rfl⟩
      change (ramanujanPacketHilbert q.val, -hilbertBackwardShift (ramanujanPacketHilbert q.val)) ∈
        mixedReflectionRelation
      simpa only [reflectedPacket, Prod.mk_sub_mk, sub_zero, sub_sub_cancel_left] using
        mixedReflectionRelation.sub_mem (reflection_pair_mem q) (vertical (q.val.totient : ℝ))
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hy
    have hb : (x, -hilbertBackwardShiftContinuous x) ∈ mixedReflectionRelation := hbase hx
    have hadd := mixedReflectionRelation.add_mem hb (vertical a)
    simpa only [Prod.mk_add_mk, add_zero, ha, ← add_assoc, neg_add_cancel_comm] using hadd

/-- Legal membership of the second coordinates of the closed mixed graph is
equivalent to RH, already detected by its vertical fibre. -/
theorem rh_iff_mixedReflectionRelation_le_legal :
    RiemannHypothesis ↔
      mixedReflectionRelation ≤ mixedClosure.prod CoefficientStabilization.closedSpace := by
  have hx := CenteredMeanSnake.riemannHypothesis_iff_naturalApproximation.trans
    BaezDuarte.naturalApproximation_iff_one_mem
  constructor
  · intro h z hz
    have ht := CoefficientStabilization.closedSpace_eq_top_iff_one_mem.mpr (hx.mp h)
    refine ⟨((mem_mixedReflectionRelation_iff z.1 z.2).mp hz).1, ?_⟩
    rw [ht]
    exact Submodule.mem_top
  · intro h
    apply hx.mpr
    have hmem : (1 : ℝ) • hilbertOne ∈ CoefficientStabilization.closedSpace := (h (vertical 1)).2
    rwa [one_smul] at hmem

end RiemannResearch.RH.Pareto.PacketReflectionTower
