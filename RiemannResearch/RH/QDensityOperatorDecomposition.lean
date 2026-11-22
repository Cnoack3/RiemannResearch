import RiemannResearch.RH.SquarefreeAffineReciprocal
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.ParetoDensityDilation
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# Recovering the density operator and its image from the reciprocal decomposition

The affine inverse on operators is B = (I+D)/ζ(2). Its compression adds
the identity on each diagonal block. For every closed subspace the image
under B is exactly a graph over that subspace.
-/

noncomputable section
namespace RiemannResearch.RH.QDensityOperatorDecomposition

open ZetaTwoProbability ZetaTwoHilbert QReciprocalMetric QDensityMetric QDivisorHilbert
open QDensityMetricInverse ZetaTwoParetoTransfer

theorem recover (v : QHilbert) : B v = (1 / zetaTwo) • (v + D v) := rfl

/-- In any projection block the identity term projects with the original input. -/
theorem projected (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection] (v : QHilbert) :
    S.starProjection (B v) =
      (1 / zetaTwo) • (S.starProjection v + S.starProjection (D v)) := by
  rw [recover, map_smul, map_add]

/-- All entries in the full divisor-wavelet orthonormal basis. -/
theorem wavelet_entry (r s : ℕ+) :
    inner ℝ (normalizedDivisorWavelet r) (B (normalizedDivisorWavelet s)) =
      ((if r = s then 1 else 0) +
        inner ℝ (normalizedDivisorWavelet r) (D (normalizedDivisorWavelet s))) / zetaTwo := by
  rw [recover, real_inner_smul_right, inner_add_right,
    (orthonormal_iff_ite.mp normalizedDivisorWavelet_orthonormal) r s]
  ring

theorem reciprocal_positive (v : QHilbert) : 0 ≤ inner ℝ v (D v) := by
  rw [lp.inner_eq_tsum]
  apply tsum_nonneg
  intro n
  simp only [RCLike.inner_apply, conj_trivial, D_apply]
  convert div_nonneg (sq_nonneg (v n)) (show 0 ≤ (n : ℝ)+1 by positivity) using 1
  ring

section
variable (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection] [CompleteSpace S]

/-- The diagonal block I + P_S D restricted to S. -/
def diagonal : S →L[ℝ] S :=
  S.orthogonalProjectionOnto.comp ((ContinuousLinearMap.id ℝ QHilbert + D).comp S.subtypeL)

omit [CompleteSpace S] in
theorem diagonal_pair (v w : S) :
    inner ℝ (diagonal S v) w = inner ℝ ((v : QHilbert) + D v) (w : QHilbert) := by
  let x := (v : QHilbert) + D v
  change inner ℝ (S.starProjection x) (w : QHilbert) = inner ℝ x (w : QHilbert)
  have h := S.sub_starProjection_mem_orthogonal x w.val w.property
  rw [inner_sub_right, sub_eq_zero] at h
  calc
    _ = inner ℝ (w : QHilbert) (S.starProjection x) := real_inner_comm _ _
    _ = inner ℝ (w : QHilbert) x := h.symm
    _ = _ := real_inner_comm _ _

private def form : S →L[ℝ] S →L[ℝ] ℝ := (innerSL ℝ).comp (diagonal S)

omit [CompleteSpace S] in
private theorem form_coercive : IsCoercive (form S) := by
  refine ⟨1, zero_lt_one, fun v => ?_⟩
  change 1 * ‖v‖ * ‖v‖ ≤ inner ℝ (diagonal S v) v
  rw [diagonal_pair, inner_add_left, real_inner_self_eq_norm_sq, one_mul]
  change ‖(v : QHilbert)‖ * ‖(v : QHilbert)‖ ≤
    ‖(v : QHilbert)‖^2 + inner ℝ (D (v : QHilbert)) (v : QHilbert)
  have h := reciprocal_positive (v : QHilbert)
  rw [real_inner_comm] at h
  nlinarith only [h]

/-- Invertibility of the diagonal block follows from the unit coercivity bound. -/
def diagonalEquiv : S ≃L[ℝ] S := (form_coercive S).continuousLinearEquivOfBilin

theorem diagonalEquiv_apply (v : S) : diagonalEquiv S v = diagonal S v := by
  symm
  apply (form_coercive S).unique_continuousLinearEquivOfBilin
  intro w
  rfl

/-- The graph operator is (I-P_S) D (I+P_S D)⁻¹ on S. -/
def graphMap : S →L[ℝ] QHilbert :=
  ((ContinuousLinearMap.id ℝ QHilbert - S.starProjection).comp
    (D.comp S.subtypeL)).comp (diagonalEquiv S).symm.toContinuousLinearMap

theorem graphMap_apply (x : S) :
    graphMap S x = D ((diagonalEquiv S).symm x : S) -
      S.starProjection (D ((diagonalEquiv S).symm x : S)) := rfl

omit [S.HasOrthogonalProjection] [CompleteSpace S] in
/-- Scalar normalization does not change the image of a linear subspace. -/
theorem image_iff_sum (y : QHilbert) :
    y ∈ S.map B.toLinearMap ↔ ∃ v : S, y = (v : QHilbert) + D v := by
  constructor
  · rintro ⟨v,hv,rfl⟩
    refine ⟨(1 / zetaTwo) • (⟨v,hv⟩ : S),?_⟩
    change B v = (1 / zetaTwo) • v + D ((1 / zetaTwo) • v)
    rw [recover, smul_add, map_smul]
  · rintro ⟨v,rfl⟩
    refine ⟨zetaTwo • (v : QHilbert),S.smul_mem _ v.property,?_⟩
    change B (zetaTwo • (v : QHilbert)) = _
    rw [map_smul, recover, smul_smul, mul_one_div_cancel zetaTwo_pos.ne', one_smul]

/-- An ambient vector belongs to B(S) exactly when its complementary
component is the graph map applied to its S component. -/
theorem image_iff_graph (y : QHilbert) :
    y ∈ S.map B.toLinearMap ↔
      y - S.starProjection y = graphMap S (S.orthogonalProjectionOnto y) := by
  rw [image_iff_sum]
  have split (v : S) :
      (v : QHilbert) + D v - S.starProjection ((v : QHilbert) + D v) =
        D v - S.starProjection (D v) := by
    rw [map_add, Submodule.starProjection_eq_self_iff.mpr v.property]
    abel
  constructor
  · rintro ⟨v,rfl⟩
    have h : (diagonalEquiv S).symm
        (S.orthogonalProjectionOnto ((v : QHilbert) + D v)) = v := by
      change (diagonalEquiv S).symm (diagonal S v) = v
      rw [← diagonalEquiv_apply, ContinuousLinearEquiv.symm_apply_apply]
    rw [graphMap_apply, h, split]
  · intro h
    let v := (diagonalEquiv S).symm (S.orthogonalProjectionOnto y)
    refine ⟨v, ?_⟩
    have hv : diagonal S v = S.orthogonalProjectionOnto y := by
      rw [← diagonalEquiv_apply]
      exact (diagonalEquiv S).apply_symm_apply _
    have hp : S.starProjection ((v : QHilbert)+D v) = S.starProjection y :=
      congrArg ((↑) : S → QHilbert) hv
    rw [graphMap_apply] at h
    change y - S.starProjection y = D (v : QHilbert) - S.starProjection (D v) at h
    rw [← split v, hp] at h
    simpa only [sub_add_cancel] using congrArg (fun x => x + S.starProjection y) h

/-- If the reciprocal image of S is dense, the complementary components of B(S)
are dense in the whole orthogonal complement of S. -/
theorem graphMap_range_closure
    (hd : (S.map D.toLinearMap).topologicalClosure = ⊤) :
    (graphMap S).range.topologicalClosure = Sᗮ := by
  let K := (graphMap S).range.topologicalClosure
  let T : QHilbert →L[ℝ] QHilbert := ContinuousLinearMap.id ℝ _ - S.starProjection
  have hK : IsClosed (K : Set QHilbert) := Submodule.isClosed_topologicalClosure _
  have hv (v : S) : T (D v) ∈ K := by
    apply Submodule.le_topologicalClosure
    refine ⟨diagonalEquiv S v, ?_⟩
    change graphMap S (diagonalEquiv S v) = D v - S.starProjection (D v)
    rw [graphMap_apply, ContinuousLinearEquiv.symm_apply_apply]
  have hpre : (S.map D.toLinearMap).topologicalClosure ≤ K.comap T.toLinearMap := by
    apply Submodule.topologicalClosure_minimal _ _ (hK.preimage T.continuous)
    rintro _ ⟨v, hvS, rfl⟩
    exact hv ⟨v, hvS⟩
  rw [hd] at hpre
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal _ _ S.isClosed_orthogonal
    rintro _ ⟨x, rfl⟩
    change graphMap S x ∈ Sᗮ
    rw [graphMap_apply]
    exact S.sub_starProjection_mem_orthogonal _
  · intro y hy
    have hh : T y ∈ K := hpre (show y ∈ (⊤ : Submodule ℝ QHilbert) by trivial)
    change y - S.starProjection y ∈ K at hh
    have hz : S.starProjection y = 0 := (S.starProjection_apply_eq_zero_iff).mpr hy
    simpa only [hz, sub_zero] using hh

omit [CompleteSpace S] in
/-- The orthogonal characterization uses the same physical sequences in P and Q. -/
theorem complementary_characterization (y : QHilbert) :
    y ∈ S.map B.toLinearMap ↔
      toPareto y ∈ ((Sᗮ).map toParetoCLM.toLinearMap)ᗮ := by
  constructor
  · rintro ⟨v,hv,rfl⟩
    apply (ParetoDensityDilation.density_orthogonal_transport_iff Sᗮ v).mp
    rw [Submodule.orthogonal_orthogonal]
    exact hv
  · intro hy
    have hy' : toPareto (B (inverse y)) ∈ ((Sᗮ).map toParetoCLM.toLinearMap)ᗮ := by
      simpa only [B_inverse] using hy
    have h := (ParetoDensityDilation.density_orthogonal_transport_iff Sᗮ (inverse y)).mpr hy'
    rw [Submodule.orthogonal_orthogonal] at h
    exact ⟨inverse y,h,B_inverse y⟩
end

/-- The full legal space has dense complementary component in its density image. -/
theorem full_graph_range_closure :
    (graphMap QFullResidueProjection.closure).range.topologicalClosure =
      QFullResidueProjection.closureᗮ :=
  graphMap_range_closure _ SquarefreeAffineReciprocal.full_closed_reciprocal_range

#print axioms full_graph_range_closure
#print axioms wavelet_entry
#print axioms image_iff_graph
#print axioms complementary_characterization
end RiemannResearch.RH.QDensityOperatorDecomposition
