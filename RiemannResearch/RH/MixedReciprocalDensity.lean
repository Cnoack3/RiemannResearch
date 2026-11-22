import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.NaturalMobiusSourceLimits
import RiemannResearch.RH.QFullTargetTotality
import RiemannResearch.RH.QConductorEstimates

/-!
# Full reciprocal density using only mixed conductors

The raw remainder r_a has Pareto mean log a, whereas its reciprocal image
r_a(n)/n has zeta-two norm at most one. Thus any prescribed Pareto mean
can be removed from a legal vector at arbitrarily small reciprocal cost.
The rank-one mean-kernel theorem identifies the correction as mixed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.MixedReciprocalDensity

open Pareto Pareto.CoefficientStabilization Pareto.PrimePowerSchur
open ZetaTwoProbability ZetaTwoHilbert ZetaTwoParetoTransfer QParetoEquivalence
open QFullResidueProjection QReciprocalMetric QDensityMetric QDensityMetricInverse

/-- The closed mixed-packet space in the physical zeta-two realization. -/
def mixed : Submodule ℝ QHilbert :=
  mixedClosure.comap paretoEquiv.toLinearEquiv.toLinearMap

theorem legal_iff (v : QHilbert) :
    v ∈ QFullResidueProjection.closure ↔ paretoEquiv v ∈ closedSpace := by
  change v ∈ (Submodule.span ℝ (Set.range (fun i : ℕ => qResidue (i+2)))).topologicalClosure ↔
    toPareto v ∈
      (Submodule.span ℝ (Set.range CoefficientStabilization.residueAtom)).topologicalClosure
  simpa only [toPareto_residueAtom] using
    mem_closure_span_iff (fun i : ℕ => qResidue (i+2)) v

theorem mem_mixed_iff (v : QHilbert) :
    v ∈ mixed ↔ v ∈ QFullResidueProjection.closure ∧ inner ℝ (paretoEquiv v) hilbertOne = 0 := by
  change paretoEquiv v ∈ mixedClosure ↔ _
  rw [mem_mixedClosure_iff_mem_closedSpace_and_mean_zero, legal_iff]

/-- Index n corresponds to conductor n+2. -/
def raw (n : ℕ) : QHilbert := ((n+2 : ℕ) : ℝ) • qResidue (n+2)

theorem raw_legal (n : ℕ) : raw n ∈ QFullResidueProjection.closure :=
  QFullResidueProjection.closure.smul_mem _ (legalSpan.le_topologicalClosure
    (Submodule.subset_span ⟨n, rfl⟩))

theorem raw_value (n k : ℕ) : qSequence (raw n) k = ((k % (n+2) : ℕ) : ℝ) := by
  change qSequenceLinear (((n+2 : ℕ):ℝ) • qResidue (n+2)) k = _
  rw [map_smul]
  change ((n+2 : ℕ):ℝ) * qSequence (qResidue (n+2)) k = _
  rw [qSequence_qResidue]
  unfold ArithmeticCumulative.residueFraction
  have ha : ((n+2 : ℕ):ℝ) ≠ 0 := by positivity
  field_simp [ha]

theorem raw_mean (n : ℕ) :
    inner ℝ (paretoEquiv (raw n)) hilbertOne = Real.log ((n+2 : ℕ):ℝ) := by
  have hn : 0 < n+2 := by omega
  rw [raw, map_smul, real_inner_smul_left, paretoEquiv_apply, toPareto_qResidue _ hn,
    BaezDuarte.residueVector, dif_pos hn, normalizedResidueHilbert_inner_one]
  have ha : ((n+2 : ℕ):ℝ) ≠ 0 := by positivity
  field_simp [ha]

theorem reciprocal_raw_bound (n : ℕ) : ‖D (raw n)‖ ≤ 1 := by
  apply qNorm_le_of_physical_bound _ 1 zero_le_one
  intro k
  rw [qSequence_D, raw_value]
  by_cases hk : k = 0
  · simp [hk]
  · have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hk'.le)]
    exact (div_le_one hk').2 (by exact_mod_cast Nat.mod_le k (n+2))

/-- Any legal vector is approximable in reciprocal norm by Pareto-mean-zero legal vectors. -/
theorem reciprocal_legal_mem {v : QHilbert} (hv : v ∈ QFullResidueProjection.closure) :
    D v ∈ (mixed.map D.toLinearMap).topologicalClosure := by
  let c := inner ℝ (paretoEquiv v) hilbertOne
  let t := fun n : ℕ => c / Real.log ((n+2 : ℕ):ℝ)
  have ha : Tendsto (fun n : ℕ => ((n+2 : ℕ):ℝ)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    have hc : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [tendsto_atTop.1 hc b] with n hn
    push_cast
    linarith
  have ht : Tendsto t atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp ha)
  have hm (n : ℕ) : v - t n • raw n ∈ mixed := by
    apply (mem_mixed_iff _).2
    refine ⟨QFullResidueProjection.closure.sub_mem hv
      (QFullResidueProjection.closure.smul_mem _ (raw_legal n)), ?_⟩
    rw [map_sub, map_smul, inner_sub_left, real_inner_smul_left, raw_mean]
    change c - (c / _) * _ = 0
    have hp : 1 < ((n+2 : ℕ):ℝ) := by exact_mod_cast (show 1 < n+2 by omega)
    rw [div_mul_cancel₀ _ (Real.log_pos hp).ne', sub_self]
  have hsmall : Tendsto (fun n => t n • D (raw n)) atTop (𝓝 0) := by
    have hnorm : Tendsto (fun n => ‖t n‖) atTop (𝓝 0) := by simpa only [norm_zero] using ht.norm
    apply squeeze_zero_norm _ hnorm
    intro n
    rw [norm_smul]
    exact le_trans (mul_le_mul_of_nonneg_left (reciprocal_raw_bound n) (norm_nonneg (t n)))
      (mul_one _).le
  have hlim : Tendsto (fun n => D (v - t n • raw n)) atTop (𝓝 (D v)) := by
    simpa only [map_sub, map_smul, sub_zero] using
      (tendsto_const_nhds (x := D v)).sub hsmall
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hlim
    (Eventually.of_forall fun n => Submodule.le_topologicalClosure _ ⟨_, hm n, rfl⟩)

/-- Reciprocal images of the mixed closure alone are total. -/
theorem mixed_reciprocal_dense : (mixed.map D.toLinearMap).topologicalClosure = ⊤ := by
  apply top_unique
  rw [← QDensityClosureTransfer.full_D_map_dense]
  apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_topologicalClosure _)
  rintro _ ⟨v, hv, rfl⟩
  exact reciprocal_legal_mem (legalSpan.le_topologicalClosure hv)

/-- Both original families may be restricted to the mixed packets simultaneously. -/
theorem mixed_augmented_dense : (mixed ⊔ mixed.map B.toLinearMap).topologicalClosure = ⊤ := by
  apply top_unique
  rw [← mixed_reciprocal_dense]
  apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_topologicalClosure _)
  rintro _ ⟨v, hv, rfl⟩
  apply Submodule.le_topologicalClosure
  change D v ∈ mixed ⊔ mixed.map B.toLinearMap
  rw [D_eq_density]
  exact (mixed ⊔ mixed.map B.toLinearMap).sub_mem
    ((mixed ⊔ mixed.map B.toLinearMap).smul_mem _ (show B v ∈ mixed ⊔ mixed.map B.toLinearMap
      from (show mixed.map B.toLinearMap ≤ mixed ⊔ mixed.map B.toLinearMap from le_sup_right)
        ⟨v,hv,rfl⟩))
    ((show mixed ≤ mixed ⊔ mixed.map B.toLinearMap from le_sup_left) hv)

/-- To discard either original family it suffices to test density images of mixed vectors. -/
theorem full_iff_density_preserves_mixed :
    QFullResidueProjection.closure = ⊤ ↔
      ∀ m ∈ mixed, B m ∈ QFullResidueProjection.closure := by
  constructor
  · intro h m _
    rw [h]
    trivial
  · intro h
    apply top_unique
    rw [← mixed_augmented_dense]
    apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_topologicalClosure _)
    apply sup_le
    · intro m hm
      exact ((mem_mixed_iff m).mp hm).1
    · rintro _ ⟨m,hm,rfl⟩
      exact h m hm

theorem density_only_iff_mixed_test :
    (legalSpan.map B.toLinearMap).topologicalClosure = ⊤ ↔
      ∀ m ∈ mixed, B m ∈ QFullResidueProjection.closure :=
  QDensityClosureTransfer.densityClosure_eq_top_iff.trans full_iff_density_preserves_mixed

theorem target_iff_mixed_test :
    qOne ∈ QFullResidueProjection.closure ↔
      ∀ m ∈ mixed, B m ∈ QFullResidueProjection.closure :=
  QFullTargetTotality.closure_eq_top_iff_one_mem.symm.trans full_iff_density_preserves_mixed

theorem riemannHypothesis_of_mixed_test
    (h : ∀ m ∈ mixed, B m ∈ QFullResidueProjection.closure) : RiemannHypothesis :=
  QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure (target_iff_mixed_test.mpr h)

/-- A closed target contains the entire mixed image exactly when it contains
the images of the individual mixed-conductor packets. -/
theorem mixed_image_le_iff (T : QHilbert →L[ℝ] QHilbert) (S : Submodule ℝ QHilbert)
    (hS : IsClosed (S : Set QHilbert)) :
    mixed.map T.toLinearMap ≤ S ↔ ∀ q : ℕ, 2 ≤ q → ¬ IsPrimePow q →
      T (toQ (ramanujanPacketHilbert q)) ∈ S := by
  classical
  constructor
  · intro h q hq hp
    have hqmem : q ∈ mixedConductors (Finset.Icc 2 q) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq,le_rfl⟩,hp⟩
    have hw : ramanujanPacketHilbert q ∈ mixedClosure :=
      mixedSpace_window_le_closure q (Submodule.subset_span
        ⟨(⟨q,hqmem⟩ : mixedConductors (Finset.Icc 2 q)),rfl⟩)
    apply h
    refine ⟨toQ (ramanujanPacketHilbert q), ?_, rfl⟩
    change toPareto (toQ _) ∈ mixedClosure
    simpa only [toPareto_toQ] using hw
  · intro h x hx
    obtain ⟨v,hv,rfl⟩ := hx
    let L := T.comp paretoEquiv.symm.toContinuousLinearMap
    let K := S.comap L.toLinearMap
    have hK : IsClosed (K : Set ThresholdHilbert) := hS.preimage L.continuous
    have hMK : mixedClosure ≤ K := by
      apply Submodule.topologicalClosure_minimal _ _ hK
      apply iSup_le
      intro N
      apply Submodule.span_le.mpr
      rintro _ ⟨q,rfl⟩
      have hq := Finset.mem_filter.mp q.property
      exact h q.val (Finset.mem_Icc.mp hq.1).1 hq.2
    have he := hMK (show paretoEquiv v ∈ mixedClosure from hv)
    change T (paretoEquiv.symm (paretoEquiv v)) ∈ S at he
    change T v ∈ S
    simpa only [paretoEquiv.symm_apply_apply] using he

/-- A single explicit family indexed only by non-prime-power conductors is total. -/
theorem mixed_packet_reciprocal_dense :
    (Submodule.span ℝ {f : QHilbert | ∃ q : ℕ, 2 ≤ q ∧ ¬ IsPrimePow q ∧
      f = D (toQ (ramanujanPacketHilbert q))}).topologicalClosure = ⊤ := by
  apply top_unique
  rw [← mixed_reciprocal_dense]
  apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_topologicalClosure _)
  apply (mixed_image_le_iff D _ (Submodule.isClosed_topologicalClosure _)).2
  intro q hq hp
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨q,hq,hp,rfl⟩)

/-- The original pure density assertion now requires testing only individual
mixed packets, with no separate test for a prime-power direction. -/
theorem full_iff_mixed_packet_test :
    QFullResidueProjection.closure = ⊤ ↔ ∀ q : ℕ, 2 ≤ q → ¬ IsPrimePow q →
      B (toQ (ramanujanPacketHilbert q)) ∈ QFullResidueProjection.closure := by
  have hmap : (∀ m ∈ mixed, B m ∈ QFullResidueProjection.closure) ↔
      mixed.map B.toLinearMap ≤ QFullResidueProjection.closure := by
    constructor
    · rintro h _ ⟨m,hm,rfl⟩
      exact h m hm
    · intro h m hm
      exact h ⟨m,hm,rfl⟩
  exact (full_iff_density_preserves_mixed.trans hmap).trans
    (mixed_image_le_iff B QFullResidueProjection.closure
      (Submodule.isClosed_topologicalClosure legalSpan))

#print axioms mixed_packet_reciprocal_dense
#print axioms full_iff_mixed_packet_test
#print axioms riemannHypothesis_of_mixed_test

end RiemannResearch.RH.MixedReciprocalDensity
