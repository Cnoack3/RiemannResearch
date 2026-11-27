import RiemannResearch.RH.PacketReflectionQuotients
import RiemannResearch.Analysis.HilbertConstraintReconstruction
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # Inverse quotients inside the reflection graph

These quotients sample the residual after orthogonal projection onto the legal
space. Their decreasing kernels intersect in the legal pullback of the graph.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PacketReflectionTower
open PrimePowerSchur CoefficientStabilization

/-- The orthogonal representative of the second coordinate in H/V. -/
def graphResidual : mixedReflectionRelation →L[ℝ] ThresholdHilbert :=
  ((ContinuousLinearMap.id ℝ ThresholdHilbert) - closedSpace.starProjection).comp
    ((ContinuousLinearMap.snd ℝ ThresholdHilbert ThresholdHilbert).comp
      mixedReflectionRelation.subtypeL)

/-- The first n positive physical residual coordinates. -/
def graphResidualHead (n : ℕ) : mixedReflectionRelation →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.pi fun j => ((anchoredEvaluationCLM (j.val + 1)).comp graphResidual).toLinearMap

theorem graphHeadKer_antitone : Antitone (fun n => (graphResidualHead n).ker) := by
  intro a b hab z hz
  apply funext
  intro j
  exact congrFun hz (⟨j.val, lt_of_lt_of_le j.isLt hab⟩ : Fin b)

/-- The descending graph kernels recover the whole legal pullback. -/
theorem iInf_graphHeadKer :
    (⨅ n, (graphResidualHead n).ker) = (reflectionDefect closedSpace).ker := by
  ext z
  rw [Submodule.mem_iInf]
  constructor
  · intro hz
    have hres : graphResidual z = 0 := by
      apply hilbertSequence_injective
      funext k
      cases k with
      | zero => simp
      | succ k =>
        have he : anchoredEvaluationCLM (k+1) (graphResidual z) = 0 :=
          congrFun (hz (k+1)) (⟨k, Nat.lt_succ_self k⟩ : Fin (k+1))
        rw [anchoredEvaluationCLM_apply] at he
        exact he.trans (congrFun hilbertSequenceLinear.map_zero (k+1)).symm
    change z.val.2 - closedSpace.starProjection z.val.2 = 0 at hres
    exact (reflectionDefect_zero_iff _ z).mpr
      (Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hres).symm)
  · intro hz n
    have hv := (reflectionDefect_zero_iff _ z).mp hz
    have hres : graphResidual z = 0 :=
      sub_eq_zero.mpr (Submodule.starProjection_eq_self_iff.mpr hv).symm
    funext j
    change anchoredEvaluationCLM (j.val+1) (graphResidual z) = 0
    rw [hres, map_zero]

/-- Forget residual sites beyond the smaller head. -/
def graphHeadTransition {n m : ℕ} (h : n ≤ m) :
    (mixedReflectionRelation ⧸ (graphResidualHead m).ker) →ₗ[ℝ]
      (mixedReflectionRelation ⧸ (graphResidualHead n).ker) :=
  (graphResidualHead m).ker.mapQ (graphResidualHead n).ker LinearMap.id (graphHeadKer_antitone h)

/-- A graph obstruction is determined by all its finite quotient classes. -/
def graphQuotientHeads : (mixedReflectionRelation ⧸ (reflectionDefect closedSpace).ker) →ₗ[ℝ]
    (∀ n : ℕ, mixedReflectionRelation ⧸ (graphResidualHead n).ker) :=
  LinearMap.pi fun n =>
    (reflectionDefect closedSpace).ker.mapQ (graphResidualHead n).ker LinearMap.id
      (iInf_graphHeadKer ▸ iInf_le _ n)

theorem graphQuotientHeads_injective : Function.Injective graphQuotientHeads := by
  apply (LinearMap.ker_eq_bot.mp _)
  apply le_antisymm _ bot_le
  intro q hq
  obtain ⟨z, rfl⟩ := (reflectionDefect closedSpace).ker.mkQ_surjective q
  apply (Submodule.mem_bot ℝ).mpr
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [← iInf_graphHeadKer,Submodule.mem_iInf]
  intro n
  exact (Submodule.Quotient.mk_eq_zero _).mp (congrFun hq n)

theorem graphQuotientHeads_compatible {n m : ℕ} (h : n ≤ m)
    (q : mixedReflectionRelation ⧸ (reflectionDefect closedSpace).ker) :
    graphHeadTransition h (graphQuotientHeads q m) = graphQuotientHeads q n := by
  obtain ⟨z, rfl⟩ := (reflectionDefect closedSpace).ker.mkQ_surjective q
  rfl

/-- The physical site tests retain the complete squared quotient norm. -/
theorem graphResidual_parseval (z : mixedReflectionRelation) :
    ‖reflectionDefect closedSpace z‖ ^ 2 =
      ∑' n : ℕ, positiveWeight n * (hilbertSequence (graphResidual z) n) ^ 2 := by
  rw [← hilbert_norm_weighted_sq]
  have he := (QuotientAddGroup.norm_mk (S := closedSpace.toAddSubgroup) z.val.2).trans
    (closedSpace.infDist_eq_norm_sub_starProjection z.val.2)
  exact congrArg (fun t : ℝ => t^2) he

private abbrev LiftSpace := WithLp 2 (mixedClosure × constantLine)

private def liftCoordinates : LiftSpace ≃L[ℝ] mixedClosure × constantLine :=
  WithLp.prodContinuousLinearEquiv 2 ℝ _ _

/-- The Hilbert norm of the two split coordinates, including the vertical part. -/
def graphLiftNorm (z : mixedReflectionRelation) : ℝ :=
  ‖liftCoordinates.symm (reflectionCoordinates z)‖

private def liftSecond : LiftSpace →L[ℝ] ThresholdHilbert :=
  (constantLine.subtypeL.comp (ContinuousLinearMap.snd ℝ mixedClosure constantLine) -
    hilbertBackwardShiftContinuous.comp
      (mixedClosure.subtypeL.comp (ContinuousLinearMap.fst ℝ mixedClosure constantLine))).comp
    liftCoordinates.toContinuousLinearMap

private def liftTest (i : ℕ) : LiftSpace →L[ℝ] ℝ :=
  (anchoredEvaluationCLM (i+1)).comp
    (((ContinuousLinearMap.id ℝ ThresholdHilbert) - closedSpace.starProjection).comp liftSecond)

private theorem liftTest_at (z : mixedReflectionRelation) (i : ℕ) :
    liftTest i (liftCoordinates.symm (reflectionCoordinates z)) =
      anchoredEvaluationCLM (i+1) (graphResidual z) := by
  change anchoredEvaluationCLM (i+1) (_ - closedSpace.starProjection _) = _
  have h : liftSecond (liftCoordinates.symm (reflectionCoordinates z)) = z.val.2 := by
    change (liftCoordinates (liftCoordinates.symm (reflectionCoordinates z))).2.val -
      hilbertBackwardShiftContinuous
        (liftCoordinates (liftCoordinates.symm (reflectionCoordinates z))).1.val = _
    rw [liftCoordinates.apply_symm_apply]
    exact add_sub_cancel_right _ _
  exact congrArg (fun t : ThresholdHilbert =>
    anchoredEvaluationCLM (i+1) (t - closedSpace.starProjection t)) h

/-- A compatible residual profile has a graph lift of bounded Hilbert norm
exactly when all positive heads have lifts with the same bound. -/
theorem bounded_graph_head_lifts_iff (b : ℕ → ℝ) (C : ℝ) :
    (∀ n : ℕ, ∃ z : mixedReflectionRelation, graphLiftNorm z ≤ C ∧
      ∀ j : Fin n, graphResidualHead n z j = b j.val) ↔
    ∃ z : mixedReflectionRelation, graphLiftNorm z ≤ C ∧
      ∀ i, anchoredEvaluationCLM (i+1) (graphResidual z) = b i := by
  constructor
  · intro hf
    choose z hbound hhead using hf
    let F := fun n => liftCoordinates.symm (reflectionCoordinates (z n))
    have hlim (i : ℕ) : Filter.Tendsto (fun n => liftTest i (F n)) Filter.atTop (nhds (b i)) := by
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [Filter.eventually_gt_atTop i] with n hn
      rw [show liftTest i (F n) = _ from liftTest_at (z n) i]
      exact (hhead n (⟨i,hn⟩ : Fin n)).symm
    letI : CompleteSpace mixedClosure :=
      (show IsClosed (mixedClosure : Set ThresholdHilbert) from isClosed_closure).completeSpace_coe
    letI : CompleteSpace constantLine := constantLine.closed_of_finiteDimensional.completeSpace_coe
    letI : CompleteSpace (⊤ : Submodule ℝ LiftSpace) :=
      (isClosed_univ : IsClosed (Set.univ : Set LiftSpace)).isComplete.completeSpace_coe
    obtain ⟨f, _, hfb, hits⟩ := Submodule.exists_mem_of_bounded_test_net (l := Filter.atTop)
      (⊤ : Submodule ℝ LiftSpace) C F (fun _ => Submodule.mem_top) hbound liftTest b hlim
    let w := reflectionCoordinates.symm (liftCoordinates f)
    have hw : liftCoordinates.symm (reflectionCoordinates w) = f := by
      simp [w]
    refine ⟨w, ?_, fun i => ?_⟩
    · simpa only [graphLiftNorm, hw] using hfb
    · rw [← liftTest_at w i, hw]
      exact hits i
  · rintro ⟨z, hz, hits⟩ n
    exact ⟨z,hz,fun j => hits j.val⟩

end RiemannResearch.RH.Pareto.PacketReflectionTower
