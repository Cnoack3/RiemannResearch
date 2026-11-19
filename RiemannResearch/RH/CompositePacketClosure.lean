import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.RamanujanCanonicalOptimizer
import RiemannResearch.RH.PrimePowerRamanujanLimits
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.NormNum

/-!
# The span of packets at all composite conductors

For the full Pareto packet dictionary, the mixed-conductor mean kernel and
the packet at four span the entire legal space. Screening against every
composite therefore annihilates every legal packet.

Source: Christian Noack's proposed composite-conductor splitting.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- Closed span of all composite conductors, including composite prime powers. -/
def compositePacketClosure : Submodule ℝ ThresholdHilbert :=
  (Submodule.span ℝ (Set.range fun q : {q : ℕ // 1 < q ∧ ¬ q.Prime} =>
    ramanujanPacketHilbert q.val)).topologicalClosure

instance : compositePacketClosure.HasOrthogonalProjection := by
  unfold compositePacketClosure
  infer_instance

theorem composite_packet_mem_closure {q : ℕ} (hq : 1 < q) (hc : ¬ q.Prime) :
    ramanujanPacketHilbert q ∈ compositePacketClosure :=
  Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨⟨q, hq, hc⟩, rfl⟩)

theorem mixedClosure_le_compositePacketClosure : mixedClosure ≤ compositePacketClosure := by
  apply Submodule.topologicalClosure_minimal
  · apply iSup_le
    intro N
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    obtain ⟨hI, hpow⟩ := Finset.mem_filter.mp q.property
    exact composite_packet_mem_closure
      (lt_of_lt_of_le (by decide : 1 < 2) (Finset.mem_Icc.mp hI).1)
      (fun hp => hpow hp.isPrimePow)
  · exact isClosed_closure

theorem packet_four_inner_one :
    inner ℝ (ramanujanPacketHilbert 4) hilbertOne = Real.log 2 := by
  rw [RiemannResearch.RH.RamanujanCanonicalOptimizer.packet_inner_one,
    show (4 : ℕ) = 2 ^ 2 by decide, ArithmeticFunction.vonMangoldt_apply_pow (by decide),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

theorem one_not_mem_compositePacketClosure_orthogonal :
    hilbertOne ∉ compositePacketClosureᗮ := by
  intro h
  have he := (compositePacketClosure.mem_orthogonal _).mp h _
    (composite_packet_mem_closure (by decide : 1 < 4) (by decide))
  rw [packet_four_inner_one] at he
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne' he

/-- A single legal vector of nonzero Pareto mean complements the mixed closure. -/
theorem mixedClosure_sup_span_of_mean_ne_zero {z : ThresholdHilbert}
    (hz : z ∈ closedSpace) (hmean : inner ℝ z hilbertOne ≠ 0) :
    mixedClosure ⊔ Submodule.span ℝ {z} = closedSpace := by
  apply le_antisymm
  · exact sup_le mixedClosure_le_closedSpace
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hz))
  · intro x hx
    let a := inner ℝ x hilbertOne / inner ℝ z hilbertOne
    have hm : x - a • z ∈ mixedClosure := by
      apply (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mpr
      refine ⟨closedSpace.sub_mem hx (closedSpace.smul_mem a hz), ?_⟩
      rw [inner_sub_left, real_inner_smul_left, sub_eq_zero]
      exact (div_mul_cancel₀ _ hmean).symm
    exact Submodule.mem_sup.mpr ⟨x - a • z, hm, a • z,
      Submodule.mem_span_singleton.mpr ⟨a, rfl⟩, sub_add_cancel _ _⟩

theorem compositePacketClosure_eq_closedSpace : compositePacketClosure = closedSpace := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨q, rfl⟩
      exact packet_mem_closedSpace q.val q.property.1
    · exact isClosed_closure
  · rw [← mixedClosure_sup_span_of_mean_ne_zero (packet_mem_closedSpace 4 (by decide))
      (packet_four_inner_one.trans_ne (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne')]
    exact sup_le mixedClosure_le_compositePacketClosure
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
        (composite_packet_mem_closure (by decide : 1 < 4) (by decide))))

theorem composite_screening_packet_eq_zero (q : ℕ) (hq : 1 < q) :
    ramanujanPacketHilbert q -
      compositePacketClosure.starProjection (ramanujanPacketHilbert q) = 0 := by
  have h : ramanujanPacketHilbert q ∈ compositePacketClosure :=
    compositePacketClosure_eq_closedSpace.symm ▸ packet_mem_closedSpace q hq
  rw [Submodule.starProjection_eq_self_iff.mpr h, sub_self]

theorem composite_screenedPrimeSpan_eq_bot :
    Submodule.span ℝ (Set.range fun q : {q : ℕ // 1 < q ∧ IsPrimePow q} =>
      ramanujanPacketHilbert q.val -
        compositePacketClosure.starProjection (ramanujanPacketHilbert q.val))
      = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨q, rfl⟩
  change ramanujanPacketHilbert q.val -
    compositePacketClosure.starProjection (ramanujanPacketHilbert q.val) = 0
  exact composite_screening_packet_eq_zero q.val q.property.1


end RiemannResearch.RH.Pareto.PrimePowerSchur
