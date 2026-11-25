import RiemannResearch.RH.QDensityMetricInverse
import RiemannResearch.RH.QParetoIsometricTransport
import RiemannResearch.RH.QShiftedReciprocalBounds
import RiemannResearch.Analysis.ClosedInvariantCalculus
import RiemannResearch.Analysis.OrthogonalDistanceBound
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Tactic.Linarith

/-! # Pareto and zeta-two Hilbert quotients
The physical change of weights induces bounded quotient equivalences and an exact
projection-energy balance. The square-root-density isometry preserves quotient norms.
Source: the user's change-of-measure construction for mixed-packet descent. -/

noncomputable section
open RiemannResearch.RH.Pareto RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.RH.ZetaTwoProbability RiemannResearch.RH.QParetoEquivalence
open RiemannResearch.RH.QDensityMetricInverse RiemannResearch.RH.QParetoIsometricTransport
open RiemannResearch.Analysis.ClosedInvariantCalculus
namespace RiemannResearch.RH.QPhysicalQuotientMetric

/-- The same physical profiles, encoded with the zeta-two weights. -/
abbrev physicalSpace (S : Submodule ℝ ThresholdHilbert) : Submodule ℝ QHilbert :=
  S.comap paretoEquiv.toLinearMap

/-- Change of physical weights on every ambient quotient, including the limiting quotient. -/
def physicalQuotientEquiv (S : Submodule ℝ ThresholdHilbert) :
    (ThresholdHilbert ⧸ S) ≃L[ℝ] (QHilbert ⧸ physicalSpace S) := by
  let f := S.liftQL ((physicalSpace S).mkQL.comp paretoEquiv.symm.toContinuousLinearMap) (by
    intro v hv
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change paretoEquiv (paretoEquiv.symm v) ∈ S
    simpa only [paretoEquiv.apply_symm_apply] using hv)
  let g := (physicalSpace S).liftQL (S.mkQL.comp paretoEquiv.toContinuousLinearMap) (by
    intro v hv
    exact (Submodule.Quotient.mk_eq_zero _).mpr hv)
  exact
    { toLinearEquiv :=
        { f.toLinearMap with
          invFun := g
          left_inv := by
            intro q
            obtain ⟨v, rfl⟩ := S.mkQ_surjective q
            change S.mkQ (paretoEquiv (paretoEquiv.symm v)) = S.mkQ v
            rw [paretoEquiv.apply_symm_apply]
          right_inv := by
            intro q
            obtain ⟨v, rfl⟩ := (physicalSpace S).mkQ_surjective q
            change (physicalSpace S).mkQ (paretoEquiv.symm (paretoEquiv v)) = _
            rw [paretoEquiv.symm_apply_apply] }
      continuous_toFun := f.continuous
      continuous_invFun := g.continuous }

@[simp] theorem physicalQuotientEquiv_mk (S : Submodule ℝ ThresholdHilbert) (x : ThresholdHilbert) :
    physicalQuotientEquiv S (S.mkQ x) = (physicalSpace S).mkQ (paretoEquiv.symm x) := rfl

/-- Restricting the quotient comparison to the image of any subspace gives the legal,
mixed and centered rows of the descent diagram. -/
theorem physicalQuotient_subspace (S W : Submodule ℝ ThresholdHilbert) :
    (W.map S.mkQ).map (physicalQuotientEquiv S).toLinearMap =
      (physicalSpace W).map (physicalSpace S).mkQ := by
  ext t
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨paretoEquiv.symm v, ?_, rfl⟩
    change paretoEquiv (paretoEquiv.symm v) ∈ W
    rwa [paretoEquiv.apply_symm_apply]
  · rintro ⟨v, hv, rfl⟩
    refine ⟨S.mkQ (paretoEquiv v), ⟨_, hv, rfl⟩, ?_⟩
    change (physicalSpace S).mkQ (paretoEquiv.symm (paretoEquiv v)) = _
    rw [paretoEquiv.symm_apply_apply]

/-- The quotient norm in a Hilbert space is the norm of the perpendicular representative. -/
theorem quotient_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Submodule ℝ E) [S.HasOrthogonalProjection] (x : E) :
    ‖S.mkQ x‖ = ‖x - S.starProjection x‖ :=
  (QuotientAddGroup.norm_mk (S := S.toAddSubgroup) x).trans (S.infDist_eq_norm_sub_starProjection x)

private theorem quotient_norm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Submodule ℝ E) (x : E) {v : E} (hv : v ∈ S) :
    ‖S.mkQ x‖ ≤ ‖x-v‖ := by
  have h := Metric.infDist_le_dist_of_mem (x := x) hv
  calc
    ‖S.mkQ x‖ = Metric.infDist x (S : Set E) := QuotientAddGroup.norm_mk (S := S.toAddSubgroup) x
    _ ≤ ‖x-v‖ := by simpa only [dist_eq_norm] using h

/-- The uniform density constants survive taking infima over closed subspaces. -/
theorem physical_quotient_norm_sq_comparison (S : Submodule ℝ ThresholdHilbert)
    [S.HasOrthogonalProjection] [(physicalSpace S).HasOrthogonalProjection] (x : QHilbert) :
    zetaTwo / 2 * ‖(physicalSpace S).mkQ x‖ ^ 2 ≤ ‖S.mkQ (paretoEquiv x)‖ ^ 2 ∧
      ‖S.mkQ (paretoEquiv x)‖ ^ 2 ≤ zetaTwo * ‖(physicalSpace S).mkQ x‖ ^ 2 := by
  let p := S.starProjection (paretoEquiv x)
  let q := (physicalSpace S).starProjection x
  have hp : paretoEquiv.symm p ∈ physicalSpace S := by
    change paretoEquiv (paretoEquiv.symm p) ∈ S
    rw [paretoEquiv.apply_symm_apply]
    exact S.starProjection_apply_mem _
  have hq : paretoEquiv q ∈ S := (physicalSpace S).starProjection_apply_mem x
  have h₁ := quotient_norm_le (physicalSpace S) x hp
  have h₂ := quotient_norm_le S (paretoEquiv x) hq
  have h₃ := (norm_comparison (x - paretoEquiv.symm p)).1
  change zetaTwo / 2 * ‖x - paretoEquiv.symm p‖ ^ 2 ≤
    ‖paretoEquiv (x - paretoEquiv.symm p)‖ ^ 2 at h₃
  rw [map_sub, paretoEquiv.apply_symm_apply] at h₃
  have h₄ := (norm_comparison (x-q)).2
  change ‖paretoEquiv (x-q)‖ ^ 2 ≤ zetaTwo * ‖x-q‖ ^ 2 at h₄
  rw [map_sub] at h₄
  constructor
  · rw [quotient_norm S]
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h₁ 2)
      (div_nonneg zetaTwo_pos.le (by norm_num))).trans h₃
  · rw [quotient_norm (physicalSpace S)]
    exact (pow_le_pow_left₀ (norm_nonneg _) h₂ 2).trans h₄


/-- Exact metric correction. The reciprocal term and the displacement between the two
optimal representatives are retained at every stage and at the closed limit. -/
theorem physical_quotient_energy_balance (S : Submodule ℝ ThresholdHilbert)
    [S.HasOrthogonalProjection] [(physicalSpace S).HasOrthogonalProjection] (x : QHilbert) :
    let q := (physicalSpace S).starProjection x
    let p := S.starProjection (paretoEquiv x)
    ‖S.mkQ (paretoEquiv x)‖ ^ 2 + ‖p - paretoEquiv q‖ ^ 2 =
      zetaTwo * (‖(physicalSpace S).mkQ x‖ ^ 2 -
        inner ℝ (x - q) (QShiftedReciprocal.B (x - q))) := by
  let q := (physicalSpace S).starProjection x
  let p := S.starProjection (paretoEquiv x)
  have hd : p - paretoEquiv q ∈ S := S.sub_mem (S.starProjection_apply_mem _)
    ((physicalSpace S).starProjection_apply_mem x)
  have ho : inner ℝ (p - paretoEquiv q) (paretoEquiv x - p) = 0 :=
    (S.sub_starProjection_mem_orthogonal (paretoEquiv x)) _ hd
  have split : paretoEquiv (x - q) = (p - paretoEquiv q) + (paretoEquiv x - p) := by
    rw [map_sub]
    abel
  have hw := QShiftedReciprocal.pareto_inner_identity (x-q) (x-q)
  simp only [real_inner_self_eq_norm_sq] at hw
  change ‖paretoEquiv (x-q)‖ ^ 2 = _ at hw
  rw [split, norm_add_sq_real, ho] at hw
  dsimp only
  rw [quotient_norm S, quotient_norm (physicalSpace S)]
  change ‖paretoEquiv x - p‖ ^ 2 + ‖p - paretoEquiv q‖ ^ 2 = _
  linarith only [hw]

/-- Multiplication by the square root of dP/dQ transports a Pareto denominator isometrically. -/
abbrev weightedSpace (S : Submodule ℝ ThresholdHilbert) : Submodule ℝ QHilbert :=
  S.map A.symm.toLinearEquiv.toLinearMap

theorem weighted_projection (S : Submodule ℝ ThresholdHilbert) [S.HasOrthogonalProjection]
    (x : ThresholdHilbert) : (weightedSpace S).starProjection (A.symm x) =
      A.symm (S.starProjection x) := by
  simpa only [LinearIsometryEquiv.symm_apply_apply] using
    (Submodule.starProjection_map_apply A.symm S (A.symm x))

theorem weighted_quotient_norm (S : Submodule ℝ ThresholdHilbert) (x : ThresholdHilbert) :
    ‖(weightedSpace S).mkQ (A.symm x)‖ = ‖S.mkQ x‖ := by
  calc
    _ = Metric.infDist (A.symm x) (weightedSpace S : Set QHilbert) :=
      QuotientAddGroup.norm_mk (S := (weightedSpace S).toAddSubgroup) _
    _ = Metric.infDist x (S : Set ThresholdHilbert) := by
      change Metric.infDist (A.symm x) (A.symm '' (S : Set ThresholdHilbert)) = _
      exact Metric.infDist_image A.symm.isometry
    _ = ‖S.mkQ x‖ := (QuotientAddGroup.norm_mk (S := S.toAddSubgroup) x).symm

/-- Switching the perpendicular representative to the other metric and back recovers
the original representative. Restriction to successive subspaces identifies their layers. -/
theorem physical_layer_roundtrip (S : Submodule ℝ ThresholdHilbert)
    [S.HasOrthogonalProjection] [(physicalSpace S).HasOrthogonalProjection] (x : QHilbert) :
    let q := (physicalSpace S).starProjection x
    let p := S.starProjection (paretoEquiv x)
    (paretoEquiv (x-q) - S.starProjection (paretoEquiv (x-q)) = paretoEquiv x - p) ∧
      ((x - paretoEquiv.symm p) - (physicalSpace S).starProjection (x - paretoEquiv.symm p) =
        x - q) := by
  have hq : paretoEquiv ((physicalSpace S).starProjection x) ∈ S :=
    (physicalSpace S).starProjection_apply_mem x
  have hp : paretoEquiv.symm (S.starProjection (paretoEquiv x)) ∈ physicalSpace S := by
    change paretoEquiv (paretoEquiv.symm _) ∈ S
    rw [paretoEquiv.apply_symm_apply]
    exact S.starProjection_apply_mem _
  dsimp only
  simp only [map_sub, Submodule.starProjection_eq_self_iff.mpr hq,
    Submodule.starProjection_eq_self_iff.mpr hp]
  constructor <;> abel

/-- The reciprocal multiplier followed by native Q projection has norm at most one half,
uniformly in the denominator. -/
def feedback (S : Submodule ℝ ThresholdHilbert) [(physicalSpace S).HasOrthogonalProjection] :
    QHilbert →L[ℝ] QHilbert :=
  (physicalSpace S).starProjection.comp QShiftedReciprocal.B

theorem feedback_norm_le (S : Submodule ℝ ThresholdHilbert)
    [(physicalSpace S).HasOrthogonalProjection] : ‖feedback S‖ ≤ (1/2 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  exact (Submodule.norm_starProjection_apply_le (physicalSpace S) _).trans
    (QShiftedReciprocal.B_norm_le_half v)

/-- Recover the actual Pareto projection on any closed denominator by a Q Neumann series. -/
theorem physical_projection_neumann (S : Submodule ℝ ThresholdHilbert)
    [S.HasOrthogonalProjection] [(physicalSpace S).HasOrthogonalProjection] (x : QHilbert) :
    paretoEquiv.symm (S.starProjection (paretoEquiv x)) =
      neumann (feedback S) ((physicalSpace S).starProjection (x - QShiftedReciprocal.B x)) := by
  let p := paretoEquiv.symm (S.starProjection (paretoEquiv x))
  have hep : paretoEquiv p = S.starProjection (paretoEquiv x) := paretoEquiv.apply_symm_apply _
  have hp : p ∈ physicalSpace S := by
    change paretoEquiv p ∈ S
    rw [hep]
    exact S.starProjection_apply_mem _
  have ho : (x-p) - QShiftedReciprocal.B (x-p) ∈ (physicalSpace S)ᗮ := by
    intro v hv
    rw [inner_sub_right]
    have hvp : inner ℝ (paretoEquiv v) (paretoEquiv x - S.starProjection (paretoEquiv x)) = 0 :=
      (S.sub_starProjection_mem_orthogonal (paretoEquiv x)) _ hv
    have h := QShiftedReciprocal.pareto_inner_identity v (x-p)
    change inner ℝ (paretoEquiv v) (paretoEquiv (x-p)) = _ at h
    rw [map_sub, hep, hvp] at h
    exact (mul_eq_zero.mp h.symm).resolve_left zetaTwo_pos.ne'
  have hzero := ((physicalSpace S).starProjection_apply_eq_zero_iff).mpr ho
  simp only [map_sub, Submodule.starProjection_eq_self_iff.mpr hp] at hzero
  have he : (1 - feedback S) p = (physicalSpace S).starProjection (x - QShiftedReciprocal.B x) := by
    change p - (physicalSpace S).starProjection (QShiftedReciprocal.B p) = _
    rw [map_sub]
    calc
      _ = (physicalSpace S).starProjection x -
          (physicalSpace S).starProjection (QShiftedReciprocal.B x) -
          (((physicalSpace S).starProjection x - p) -
            ((physicalSpace S).starProjection (QShiftedReciprocal.B x) -
              (physicalSpace S).starProjection (QShiftedReciprocal.B p))) := by abel
      _ = _ := by rw [hzero, sub_zero]
  have hnorm : ‖feedback S‖ < 1 := lt_of_le_of_lt (feedback_norm_le S) (by norm_num)
  have hi := neumann_mul_one_sub (summable_geometric_of_norm_lt_one hnorm)
  rw [← he]
  change p = (neumann (feedback S) * (1 - feedback S)) p
  exact (congrArg (fun L : QHilbert →L[ℝ] QHilbert => L p) hi).symm

/--
info: 'RiemannResearch.RH.QPhysicalQuotientMetric.physical_quotient_energy_balance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms physical_quotient_energy_balance

/--
info: 'RiemannResearch.RH.QPhysicalQuotientMetric.physical_projection_neumann' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms physical_projection_neumann

end RiemannResearch.RH.QPhysicalQuotientMetric
