import RiemannResearch.RH.QPhysicalQuotientMetric
import RiemannResearch.RH.HausdorffSupportColimit
import RiemannResearch.RH.CenteredMeanSquarefreeConverse
import RiemannResearch.RH.ZetaTwoParitySignal
import RiemannResearch.RH.IntegratedRamanujanHilbert
import RiemannResearch.Analysis.NestedOrthogonalDecomposition
import RiemannResearch.Analysis.ClosedInvariantCalculus
import Mathlib.Tactic.Linarith

/-! # Change of measure for the infinite prime-support tower
The weight isometry transports the Pareto expansion. The same physical packets form
a native orthogonal tower under Q. Its terminal centered parity class detects RH.
Source: the user's infinite Parseval tower and quotient descent construction. -/

noncomputable section
open Filter CategoryTheory
open scoped Topology BigOperators
open RiemannResearch.RH.Pareto RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.RH.ZetaTwoParitySignal RiemannResearch.RH.QPhysicalQuotientMetric
open RiemannResearch.RH.QParetoEquivalence RiemannResearch.RH.QParetoIsometricTransport
open RiemannResearch.Analysis.NestedOrthogonalDecomposition
open RiemannResearch.Analysis.ClosedInvariantCalculus
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis.MeasureChange
open CoefficientStabilization

/-- All transition squares commute, also when the larger denominator is the full mixed space. -/
theorem physicalQuotient_natural {S W : Submodule ℝ ThresholdHilbert} (h : S ≤ W)
    (x : ThresholdHilbert ⧸ S) :
    physicalQuotientEquiv W (supportQuotientTransition h x) =
      supportQuotientTransition (show physicalSpace S ≤ physicalSpace W from
        Submodule.comap_mono h) (physicalQuotientEquiv S x) := by
  obtain ⟨v, rfl⟩ := S.mkQ_surjective x
  rfl

/-- The complete infinite Pareto Parseval expansion in the isometric Q realization. -/
theorem weighted_layer_parseval (m : mixedClosure) :
    HasSum (fun k => ‖A.symm (((supportLayer k).starProjection m : mixedClosure) :
      ThresholdHilbert)‖ ^ 2) (‖A.symm (m : ThresholdHilbert)‖ ^ 2) := by
  simpa only [LinearIsometryEquiv.norm_map, Submodule.coe_norm] using hasSum_supportLayer_energy m

/-- The native zeta-two support stages retain all conductors of the specified support size. -/
abbrev qStage (n : ℕ) : Submodule ℝ QHilbert := physicalSpace (ambientSupport n)

abbrev qMixed : Submodule ℝ QHilbert := physicalSpace mixedClosure

theorem qStage_mono : Monotone qStage :=
  fun _ _ h => Submodule.comap_mono (Submodule.map_mono (supportSpace_mono h))

/-- The two physical quotient functors are naturally isomorphic at every support depth. -/
def physicalSupportTowerIso :
    supportQuotientFunctor ambientSupport (fun _ _ h => Submodule.map_mono (supportSpace_mono h)) ≅
      supportQuotientFunctor qStage qStage_mono :=
  NatIso.ofComponents (fun n => TopModuleCat.ofIso (physicalQuotientEquiv (ambientSupport n))) (by
    intro i j f
    apply ConcreteCategory.hom_ext
    intro q
    exact physicalQuotient_natural (Submodule.map_mono (supportSpace_mono (leOfHom f))) q)

theorem qStage_le_mixed (n : ℕ) : qStage n ≤ qMixed := by
  intro x hx
  obtain ⟨m, _, hm⟩ := hx
  change paretoEquiv x ∈ mixedClosure
  change (m : ThresholdHilbert) = paretoEquiv x at hm
  rw [← hm]
  exact m.property

instance qStage_isClosed (n : ℕ) : IsClosed (qStage n : Set QHilbert) :=
  (ambientSupport_isClosed n).preimage paretoEquiv.continuous

instance qMixed_isClosed : IsClosed (qMixed : Set QHilbert) :=
  (show IsClosed (mixedClosure : Set ThresholdHilbert) from isClosed_closure).preimage
    paretoEquiv.continuous

instance qStage_projection (n : ℕ) : (qStage n).HasOrthogonalProjection := by
  let : CompleteSpace (qStage n) := (qStage_isClosed n).completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

instance qMixed_projection : qMixed.HasOrthogonalProjection := by
  let : CompleteSpace qMixed := qMixed_isClosed.completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

theorem qStage_zero : qStage 0 = ⊥ := by
  have hs : supportSpace 0 = ⊥ := le_antisymm
    ((supportSpace_mono (by decide : 0 ≤ 1)).trans supportSpace_one.le) bot_le
  have ha : ambientSupport 0 = ⊥ := by simp [ambientSupport, hs]
  ext x
  change paretoEquiv x ∈ ambientSupport 0 ↔ x ∈ (⊥ : Submodule ℝ QHilbert)
  rw [ha]
  change paretoEquiv x = 0 ↔ x = 0
  constructor
  · intro h
    apply paretoEquiv.injective
    simpa only [map_zero] using h
  · rintro rfl
    exact map_zero paretoEquiv

/-- Exhaustion is preserved for the untwisted physical packet tower. -/
theorem qStage_dense : (⨆ n, qStage n).topologicalClosure = qMixed := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (iSup_le qStage_le_mixed) qMixed_isClosed
  · intro x hx
    let m : mixedClosure := ⟨paretoEquiv x, hx⟩
    let f := paretoEquiv.symm.toContinuousLinearMap.comp mixedClosure.subtypeL
    have h := tendsto_sum_supportLayer_projection m
    simp_rw [sum_supportLayer_projection] at h
    have ht : Tendsto (fun n => f ((supportSpace n).starProjection m)) atTop (𝓝 (f m)) :=
      f.continuous.continuousAt.tendsto.comp h
    have hfm : f m = x := paretoEquiv.symm_apply_apply x
    rw [← hfm]
    apply isClosed_closure.mem_of_tendsto ht
    apply Filter.Eventually.of_forall
    intro n
    apply Submodule.le_topologicalClosure
    apply le_iSup qStage n
    change paretoEquiv (paretoEquiv.symm _) ∈ ambientSupport n
    rw [paretoEquiv.apply_symm_apply]
    exact ⟨_, (supportSpace n).starProjection_apply_mem m, rfl⟩

theorem qStage_projection_tendsto (x : QHilbert) :
    Tendsto (fun n => (qStage n).starProjection x) atTop (𝓝 (qMixed.starProjection x)) := by
  simpa only [qStage_dense] using
    Submodule.starProjection_tendsto_closure_iSup qStage qStage_mono x

/-- Native orthogonal layers are formed with the Q inner product. -/
abbrev qLayer (n : ℕ) : Submodule ℝ QHilbert := qStage (n+1) ⊓ (qStage n)ᗮ

instance qLayer_projection (n : ℕ) : (qLayer n).HasOrthogonalProjection :=
  carry_hasOrthogonalProjection (qStage_mono (Nat.le_succ n))

theorem qLayer_projection_difference (n : ℕ) (x : QHilbert) :
    (qLayer n).starProjection x =
      (qStage (n+1)).starProjection x - (qStage n).starProjection x :=
  carry_projection_apply (qStage_mono (Nat.le_succ n)) x

private theorem qStage_zero_projection (x : QHilbert) : (qStage 0).starProjection x = 0 := by
  have h := (qStage 0).starProjection_apply_mem x
  exact (Submodule.mem_bot ℝ).mp (qStage_zero.le h)

/-- Orthogonal Q layer sums reconstruct the full Q mixed projection. -/
theorem qLayer_reconstruction (x : QHilbert) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, (qLayer k).starProjection x) atTop
      (𝓝 (qMixed.starProjection x)) := by
  have finiteSum (n : ℕ) : (∑ k ∈ Finset.range n, (qLayer k).starProjection x) =
      (qStage n).starProjection x := by
    induction n with
    | zero => simp [qStage_zero_projection]
    | succ n ih => rw [Finset.sum_range_succ, ih, qLayer_projection_difference]; abel
  simpa only [finiteSum] using qStage_projection_tendsto x

/-- One step of quotient descent loses exactly one native layer energy. -/
theorem q_quotient_step (n : ℕ) (x : QHilbert) :
    ‖(qStage n).mkQ x‖ ^ 2 =
      ‖(qStage (n+1)).mkQ x‖ ^ 2 + ‖(qLayer n).starProjection x‖ ^ 2 := by
  have ho : inner ℝ ((qLayer n).starProjection x) (x - (qStage (n+1)).starProjection x) = 0 :=
    ((qStage (n+1)).sub_starProjection_mem_orthogonal x) _ ((qLayer n).starProjection_apply_mem x).1
  have hs : x - (qStage n).starProjection x =
      (qLayer n).starProjection x + (x - (qStage (n+1)).starProjection x) := by
    rw [qLayer_projection_difference]
    abel
  rw [quotient_norm, quotient_norm, hs, norm_add_sq_real, ho]
  ring

theorem q_quotient_parseval (n : ℕ) (x : QHilbert) :
    ‖(qStage n).mkQ x‖ ^ 2 + (∑ k ∈ Finset.range n, ‖(qLayer k).starProjection x‖ ^ 2) =
      ‖x‖ ^ 2 := by
  induction n with
  | zero =>
    rw [quotient_norm (qStage 0), qStage_zero_projection, sub_zero, Finset.range_zero,
      Finset.sum_empty, add_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    linarith only [ih, q_quotient_step n x]

/-- The stage quotient norms converge to the norm in the Hausdorff mixed quotient. -/
theorem tendsto_q_quotient_norm_sq (x : QHilbert) :
    Tendsto (fun n => ‖(qStage n).mkQ x‖ ^ 2) atTop (𝓝 (‖qMixed.mkQ x‖ ^ 2)) := by
  simpa only [quotient_norm] using
    ((tendsto_const_nhds (x := x)).sub (qStage_projection_tendsto x)).norm.pow 2

theorem q_layer_energy_hasSum (x : QHilbert) :
    HasSum (fun k => ‖(qLayer k).starProjection x‖ ^ 2) (‖x‖ ^ 2 - ‖qMixed.mkQ x‖ ^ 2) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => sq_nonneg _) _).2
  have h := (tendsto_const_nhds (x := ‖x‖ ^ 2)).sub (tendsto_q_quotient_norm_sq x)
  exact h.congr' (Filter.Eventually.of_forall fun n => by
    change ‖x‖ ^ 2 - ‖(qStage n).mkQ x‖ ^ 2 =
      ∑ k ∈ Finset.range n, ‖(qLayer k).starProjection x‖ ^ 2
    linarith only [q_quotient_parseval n x])

/-- Ambient Pareto stages are closed images of the closed stages inside the mixed space. -/
local instance paretoStageProjection (n : ℕ) : (ambientSupport n).HasOrthogonalProjection := by
  let : CompleteSpace (ambientSupport n) := (ambientSupport_isClosed n).completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

private theorem paretoStage_projection_tendsto (x : ThresholdHilbert) :
    Tendsto (fun n => (ambientSupport n).starProjection x) atTop
      (𝓝 (mixedClosure.starProjection x)) := by
  have hd : (⨆ n, ambientSupport n).topologicalClosure = mixedClosure := by
    apply le_antisymm
    · apply Submodule.topologicalClosure_minimal _ _ isClosed_closure
      refine iSup_le fun n v hv => ?_
      obtain ⟨m, _, rfl⟩ := hv
      exact m.property
    · intro v hv
      let m : mixedClosure := ⟨v, hv⟩
      have h := tendsto_sum_supportLayer_projection m
      simp_rw [sum_supportLayer_projection] at h
      have ht : Tendsto (fun n => mixedClosure.subtypeL ((supportSpace n).starProjection m))
          atTop (𝓝 v) := mixedClosure.subtypeL.continuous.continuousAt.tendsto.comp h
      apply isClosed_closure.mem_of_tendsto ht
      exact Filter.Eventually.of_forall fun n => Submodule.le_topologicalClosure _
        ((le_iSup ambientSupport n) ⟨_, (supportSpace n).starProjection_apply_mem m, rfl⟩)
  simpa only [hd] using Submodule.starProjection_tendsto_closure_iSup ambientSupport
    (fun _ _ h => Submodule.map_mono (supportSpace_mono h)) x

/-- The Q-only Neumann computations along the support filtration converge to the actual
mean-one Pareto screened vector, with its physical sequence preserved. -/
theorem q_neumann_screened_parity_tendsto :
    let g := (Real.log 2)⁻¹ • ramanujanPacketHilbert 2
    let x := paretoEquiv.symm g
    Tendsto (fun n => x - neumann (feedback (ambientSupport n))
      ((qStage n).starProjection (x - QShiftedReciprocal.B x))) atTop
      (𝓝 (paretoEquiv.symm normalizedScreenedTwo)) := by
  let g := (Real.log 2)⁻¹ • ramanujanPacketHilbert 2
  have hu : normalizedScreenedTwo = g - mixedClosure.starProjection g := by
    have h := CenteredMeanSnake.normalizedScreenedTwo_eq_projected_packet
    rw [Submodule.starProjection_orthogonal_val, smul_sub] at h
    simpa only [g, map_smul] using h
  have ht := paretoEquiv.symm.continuous.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := g)).sub (paretoStage_projection_tendsto g))
  rw [hu]
  apply ht.congr'
  apply Filter.Eventually.of_forall
  intro n
  change paretoEquiv.symm (g - (ambientSupport n).starProjection g) = _
  rw [map_sub]
  have hn := physical_projection_neumann (ambientSupport n) (paretoEquiv.symm g)
  rw [paretoEquiv.apply_symm_apply] at hn
  rw [hn]

/-- Pareto-mean-normalized parity minus the ambient constant. -/
def centeredParity : ThresholdHilbert := (Real.log 2)⁻¹ • ramanujanPacketHilbert 2 - hilbertOne

abbrev qParity : QHilbert := paretoEquiv.symm centeredParity

/-- The square-root-density realization retains the Pareto boundary norm at the limit. -/
theorem weighted_parity_quotient_tendsto :
    Tendsto (fun n => ‖(weightedSpace (ambientSupport n)).mkQ (A.symm centeredParity)‖ ^ 2)
      atTop (𝓝 (‖CenteredMeanSnake.boundary‖ ^ 2)) := by
  simp_rw [weighted_quotient_norm]
  exact tendsto_parityQuotientClass_norm_sq

/-- All physical Q stage boundaries descend to the same class of u minus one. -/
theorem q_parity_descends (n : ℕ) :
    supportQuotientTransition (qStage_le_mixed n) ((qStage n).mkQ qParity) =
      qMixed.mkQ (paretoEquiv.symm (normalizedScreenedTwo - hilbertOne)) := by
  exact congrArg (physicalQuotientEquiv mixedClosure) (supportCocone_parity_eq_defect n)

theorem q_terminal_parity_zero_iff_rh : qMixed.mkQ qParity = 0 ↔ RiemannHypothesis := by
  let : IsClosed (mixedClosure : Set ThresholdHilbert) := isClosed_closure
  have htransport : qMixed.mkQ qParity = 0 ↔ mixedClosure.mkQ centeredParity = 0 := by
    change physicalQuotientEquiv mixedClosure (mixedClosure.mkQ centeredParity) = 0 ↔ _
    constructor
    · intro h
      apply (physicalQuotientEquiv mixedClosure).injective
      simpa only [map_zero] using h
    · intro h
      rw [h, map_zero]
  have hnorm : ‖mixedClosure.mkQ centeredParity‖ = ‖CenteredMeanSnake.boundary‖ :=
    norm_supportCocone_parity 0
  calc
    _ ↔ mixedClosure.mkQ centeredParity = 0 := htransport
    _ ↔ ‖mixedClosure.mkQ centeredParity‖ = 0 := norm_eq_zero.symm
    _ ↔ ‖CenteredMeanSnake.boundary‖ = 0 := by rw [hnorm]
    _ ↔ CenteredMeanSnake.boundary = 0 := norm_eq_zero
    _ ↔ RiemannHypothesis := CenteredMeanSnake.boundary_eq_zero_iff_naturalApproximation.trans
      CenteredMeanSnake.riemannHypothesis_iff_naturalApproximation.symm

theorem riemannHypothesis_iff_q_parity_descent :
    RiemannHypothesis ↔ Tendsto (fun n => ‖(qStage n).mkQ qParity‖ ^ 2) atTop (𝓝 0) := by
  have ht := tendsto_q_quotient_norm_sq qParity
  constructor
  · intro h
    simpa only [q_terminal_parity_zero_iff_rh.mpr h, norm_zero,
      zero_pow (by decide : 2 ≠ 0)] using ht
  · intro h
    apply q_terminal_parity_zero_iff_rh.mp
    apply norm_eq_zero.mp
    exact (sq_eq_zero_iff).mp (tendsto_nhds_unique ht h)

/-- The physical target has only its constant and dyadic parity observations. -/
theorem qParity_eq_odd : qParity = (Real.log 2)⁻¹ • ZetaTwoParitySignal.qOdd - qOne := by
  have hOdd : paretoEquiv.symm (ramanujanPacketHilbert 2) = ZetaTwoParitySignal.qOdd := by
    apply qSequence_injective
    simpa only [paretoEquiv_symm_apply, toQ_sequence, hilbertSequence_ramanujanPacketHilbert,
      ZetaTwoParitySignal.qSequence_qOdd_mod, ramanujanPacket_prime_eq_residue 2 (by decide)]
      using (show residue 2 = (fun n : ℕ => ((n % 2 : ℕ) : ℝ)) from rfl)
  change paretoEquiv.symm ((Real.log 2)⁻¹ • ramanujanPacketHilbert 2 - hilbertOne) = _
  rw [map_sub, map_smul, hOdd, paretoEquiv_symm_apply, toQ_hilbertOne]

theorem qParity_norm_sq :
    ‖qParity‖ ^ 2 = (3 / 4 : ℝ) * ((Real.log 2)⁻¹ - 1) ^ 2 + 1 / 4 := by
  have hmean : inner ℝ qOdd qOne = (3/4 : ℝ) := by
    rw [← qEven_add_qOdd, inner_add_right, qOdd_inner_qEven,
      real_inner_self_eq_norm_sq, qOdd_norm_sq]
    norm_num
  rw [qParity_eq_odd, norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    ZetaTwoParitySignal.qOdd_norm_sq, qOne_norm_sq, real_inner_smul_left, hmean]
  ring

/-- RH is equivalent to exhausting the explicit arithmetic target in the native Q Parseval sum. -/
theorem riemannHypothesis_iff_q_layer_saturation :
    RiemannHypothesis ↔ (∑' k, ‖(qLayer k).starProjection qParity‖ ^ 2) =
      (3 / 4 : ℝ) * ((Real.log 2)⁻¹ - 1) ^ 2 + 1 / 4 := by
  rw [(q_layer_energy_hasSum qParity).tsum_eq, ← qParity_norm_sq]
  constructor
  · intro h
    rw [q_terminal_parity_zero_iff_rh.mpr h, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero]
  · intro h
    apply q_terminal_parity_zero_iff_rh.mp
    apply norm_eq_zero.mp
    nlinarith only [h, norm_nonneg (qMixed.mkQ qParity)]


/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis.MeasureChange.physicalSupportTowerIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms physicalSupportTowerIso

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis.MeasureChange.q_layer_energy_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms q_layer_energy_hasSum

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis.MeasureChange.riemannHypothesis_iff_q_layer_saturation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms riemannHypothesis_iff_q_layer_saturation

end RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis.MeasureChange
