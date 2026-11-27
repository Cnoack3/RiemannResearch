import RiemannResearch.RH.PacketReflectionRelation
import RiemannResearch.RH.MixedDifferenceDensity
import RiemannResearch.RH.CenteredMeanQuotients
import RiemannResearch.Analysis.NestedOrthogonalDecomposition

/-! # The legal pullback of the closed mixed reflection relation

The horizontal coordinate is mixed, and the independent vertical coordinate
is a constant. Quotienting the second coordinate tests legality. Killing the
constant line as well gives the obstruction to the existence of a legal lift.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.PacketReflectionTower
open PrimePowerSchur CoefficientStabilization

private abbrev H := ThresholdHilbert

/-- The ambiguity in the reflected coordinate. -/
abbrev constantLine : Submodule ℝ ThresholdHilbert := Submodule.span ℝ {hilbertOne}

/-- Addition and removal of the anchored shift split the reflection relation. -/
def reflectionCoordinates : mixedReflectionRelation ≃ₗ[ℝ] mixedClosure × constantLine where
  toFun z := (⟨z.val.1, ((mem_mixedReflectionRelation_iff _ _).mp z.property).1⟩,
    ⟨z.val.2 + hilbertBackwardShiftContinuous z.val.1,
      ((mem_mixedReflectionRelation_iff _ _).mp z.property).2⟩)
  invFun w := ⟨(w.1.val, w.2.val - hilbertBackwardShiftContinuous w.1.val),
    (mem_mixedReflectionRelation_iff _ _).mpr ⟨w.1.property, by simpa only [sub_add_cancel] using w.2.property⟩⟩
  left_inv z := by ext <;> simp
  right_inv w := by ext <;> simp
  map_add' z w := by
    apply Prod.ext
    · rfl
    apply Subtype.ext
    change _ + hilbertBackwardShiftContinuous (z.val.1 + w.val.1) = _
    rw [map_add]
    change (z.val.2 + w.val.2) + (_ + _) = (_ + _) + (_ + _)
    abel
  map_smul' a z := by ext <;> simp [smul_add]

/-- The map to the quotient of the second coordinate. Its kernel is intrinsic
to the graph. -/
def reflectionDefect (K : Submodule ℝ H) : mixedReflectionRelation →L[ℝ] H ⧸ K :=
  K.mkQL.comp ((ContinuousLinearMap.snd ℝ H H).comp mixedReflectionRelation.subtypeL)

theorem reflectionDefect_zero_iff (K : Submodule ℝ H) (z : mixedReflectionRelation) :
    reflectionDefect K z = 0 ↔ z.val.2 ∈ K :=
  Submodule.Quotient.mk_eq_zero _

/-- Quotienting by the kernel identifies the intrinsic quotient with the
algebraic image in the ambient quotient. -/
def reflectionQuotientEquivRange (K : Submodule ℝ H) :
    (mixedReflectionRelation ⧸ (reflectionDefect K).ker) ≃ₗ[ℝ]
      LinearMap.range (reflectionDefect K).toLinearMap :=
  (reflectionDefect K).toLinearMap.quotKerEquivRange

/-- Mixed first coordinates having a lift with second coordinate in K. -/
def liftableMixed (K : Submodule ℝ H) : Submodule ℝ mixedClosure :=
  (K ⊔ constantLine).comap
    (hilbertBackwardShiftContinuous.comp mixedClosure.subtypeL).toLinearMap

theorem exists_reflection_lift_iff (K : Submodule ℝ H) (x : mixedClosure) :
    (∃ y ∈ K, (x.val, y) ∈ mixedReflectionRelation) ↔ x ∈ liftableMixed K := by
  change _ ↔ hilbertBackwardShiftContinuous x.val ∈ K ⊔ constantLine
  constructor
  · rintro ⟨y, hy, hg⟩
    have hc := ((mem_mixedReflectionRelation_iff _ _).mp hg).2
    exact Submodule.mem_sup.mpr ⟨-y, K.neg_mem hy, _, hc, by abel⟩
  · intro h
    obtain ⟨v, hv, l, hl, he⟩ := Submodule.mem_sup.mp h
    exact ⟨-v, K.neg_mem hv, (mem_mixedReflectionRelation_iff _ _).mpr
      ⟨x.property, by rw [← he]; simpa using hl⟩⟩

/-- The square from the second-coordinate defect to the obstruction on the
mixed first coordinate commutes after also killing the vertical constants. -/
theorem reflectionDefect_mod_constants (K : Submodule ℝ H) (z : mixedReflectionRelation) :
    (K.mapQ (K ⊔ constantLine) LinearMap.id le_sup_left) (reflectionDefect K z) =
      (K ⊔ constantLine).mkQ (-hilbertBackwardShiftContinuous z.val.1) := by
  change (K ⊔ constantLine).mkQ z.val.2 = _
  apply sub_eq_zero.mp
  rw [← map_sub, sub_neg_eq_add]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ((le_sup_right : constantLine ≤ K ⊔ constantLine)
      (((mem_mixedReflectionRelation_iff _ _).mp z.property).2))

/-- Projection to the mixed first coordinate of a graph point passing the test. -/
def legalFirst (K : Submodule ℝ H) : (reflectionDefect K).ker →ₗ[ℝ] liftableMixed K where
  toFun z := ⟨(reflectionCoordinates z.val).1,
    (exists_reflection_lift_iff K _).mp
      ⟨z.val.val.2, (reflectionDefect_zero_iff K _).mp z.property, z.val.property⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem legalFirst_surjective (K : Submodule ℝ H) : Function.Surjective (legalFirst K) := by
  intro x
  obtain ⟨y, hy, hg⟩ := (exists_reflection_lift_iff K x.val).mpr x.property
  exact ⟨⟨⟨(_,y), hg⟩, (reflectionDefect_zero_iff K _).mpr hy⟩, rfl⟩

/-- Insert a vertical constant lying in K into the tested graph. -/
def legalVertical (K : Submodule ℝ H) : (constantLine ⊓ K : Submodule ℝ H) →ₗ[ℝ]
    (reflectionDefect K).ker where
  toFun l := ⟨⟨(0, l.val), (mem_mixedReflectionRelation_iff _ _).mpr
    ⟨mixedClosure.zero_mem, by
      change l.val + hilbertBackwardShiftContinuous (0 : H) ∈ constantLine
      rw [map_zero, add_zero]
      exact l.property.1⟩⟩,
    (reflectionDefect_zero_iff K _).mpr l.property.2⟩
  map_add' _ _ := by apply Subtype.ext; apply Subtype.ext; simp
  map_smul' _ _ := by apply Subtype.ext; apply Subtype.ext; simp

theorem legalVertical_injective (K : Submodule ℝ H) : Function.Injective (legalVertical K) :=
  fun _ _ h => Subtype.ext (congrArg (fun z : (reflectionDefect K).ker => z.val.val.2) h)

theorem reflection_pullback_exact (K : Submodule ℝ H) :
    Function.Exact (legalVertical K) (legalFirst K) := by
  intro z
  constructor
  · intro h
    have hx : z.val.val.1 = 0 := congrArg (fun x : liftableMixed K => x.val.val) h
    have hc := ((mem_mixedReflectionRelation_iff _ _).mp z.val.property).2
    rw [hx, map_zero, add_zero] at hc
    refine ⟨⟨z.val.val.2, hc, (reflectionDefect_zero_iff K _).mp z.property⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hx.symm rfl
  · rintro ⟨v, rfl⟩
    rfl

/-- The vertical generator recovers the negative of the transported centering boundary. -/
theorem vertical_defect_eq_neg_boundary (a : ℝ) :
    reflectionDefect closedSpace
      (reflectionCoordinates.symm (0, ⟨a • hilbertOne,
        constantLine.smul_mem a (Submodule.subset_span (Set.mem_singleton _))⟩)) =
      -CenteredMeanSnake.boundaryTargetEquivLegalQuotient (CenteredMeanSnake.boundary a) := by
  change closedSpace.mkQ (a • hilbertOne - hilbertBackwardShiftContinuous 0) = _
  rw [map_zero, sub_zero, map_smul, CenteredMeanSnake.boundaryTargetEquivLegalQuotient_boundary,
    neg_neg]

theorem rh_iff_reflectionDefect_zero :
    RiemannHypothesis ↔ reflectionDefect closedSpace = 0 := by
  rw [rh_iff_mixedReflectionRelation_le_legal]
  constructor
  · intro h
    exact ContinuousLinearMap.ext fun z => (reflectionDefect_zero_iff _ z).mpr (h z.property).2
  · intro h z hz
    exact ⟨((mem_mixedReflectionRelation_iff _ _).mp hz).1,
      (reflectionDefect_zero_iff _ ⟨z,hz⟩).mp (by rw [h]; rfl)⟩

private theorem defect_norm (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    (z : mixedReflectionRelation) : ‖reflectionDefect K z‖ = ‖z.val.2 - K.starProjection z.val.2‖ :=
  (QuotientAddGroup.norm_mk (S := K.toAddSubgroup) z.val.2).trans
    (K.infDist_eq_norm_sub_starProjection z.val.2)

/-- Exact decrease of the ambient quotient obstruction along nested denominators. -/
theorem reflection_quotient_step {A B : Submodule ℝ H} [A.HasOrthogonalProjection]
    [B.HasOrthogonalProjection] (hab : A ≤ B) (z : mixedReflectionRelation) :
    ‖reflectionDefect A z‖ ^ 2 = ‖reflectionDefect B z‖ ^ 2 +
      ‖B.starProjection z.val.2 - A.starProjection z.val.2‖ ^ 2 := by
  let y := z.val.2
  have hp := RiemannResearch.Analysis.NestedOrthogonalDecomposition.projection_difference_mem hab y
  have ho := inner_eq_zero_symm.mp ((B.sub_starProjection_mem_orthogonal y) _ hp.1)
  rw [defect_norm, defect_norm]
  change ‖y - A.starProjection y‖ ^ 2 = _
  rw [show y - A.starProjection y = (y - B.starProjection y) +
    (B.starProjection y - A.starProjection y) by abel]
  rw [norm_add_sq_real, ho]
  ring

theorem reflection_quotient_tendsto (K : ℕ → Submodule ℝ H)
    [∀ n, (K n).HasOrthogonalProjection] (hm : Monotone K)
    (hV : (⨆ n, K n).topologicalClosure = closedSpace) (z : mixedReflectionRelation) :
    Tendsto (fun n => ‖reflectionDefect (K n) z‖) atTop (𝓝 ‖reflectionDefect closedSpace z‖) := by
  have h := Submodule.starProjection_tendsto_closure_iSup K hm z.val.2
  have h' : Tendsto (fun n => ‖reflectionDefect (K n) z‖) atTop
      (𝓝 ‖reflectionDefect (⨆ n, K n).topologicalClosure z‖) := by
    simpa only [defect_norm] using (tendsto_const_nhds.sub h).norm
  rwa [hV] at h'

/-- Exact reflected tower energy in an arbitrary closed quotient, retaining
both the projected shift and the loss caused by the physical shift. -/
theorem reflected_tower_quotient_energy (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    (p q k : ℕ) (hp : p.Prime) (hq : 1 < q) (hd : p ∣ q) :
    let f := scaledPacket p q k
    ‖K.mkQ (scaledReflection p q k) - (q.totient : ℝ) • K.mkQ hilbertOne‖^2 +
      ‖K.starProjection (hilbertBackwardShiftContinuous f)‖^2 +
      PrimitiveEnergy.shiftDefect (hilbertSequence f) =
      (p : ℝ)⁻¹ ^ k * ‖ramanujanPacketHilbert q‖^2 := by
  dsimp only
  let s := hilbertBackwardShiftContinuous (scaledPacket p q k)
  have hn : ‖K.mkQ s‖ = ‖s - K.starProjection s‖ :=
    (QuotientAddGroup.norm_mk (S := K.toAddSubgroup) s).trans
      (K.infDist_eq_norm_sub_starProjection s)
  have he := reflected_tower_energy p q k hp hq hd
  rw [scaledReflection_eq p q k hp hd, sub_sub_cancel_left, norm_neg] at he
  rw [scaledReflection_eq p q k hp hd, map_sub, map_smul, sub_sub_cancel_left, norm_neg]
  have hpy := Submodule.norm_sq_eq_add_norm_sq_starProjection s K
  rw [Submodule.starProjection_orthogonal_val] at hpy
  change ‖K.mkQ s‖ ^ 2 + ‖K.starProjection s‖ ^ 2 + _ = _
  rw [hn, add_comm (‖s - K.starProjection s‖^2), ← hpy]
  exact he

/-- The quotient arrows commute with reflection on its closed graph. -/
theorem reflectionDefect_transition {A B : Submodule ℝ H} (hab : A ≤ B)
    (z : mixedReflectionRelation) :
    (A.mapQ B LinearMap.id hab) (reflectionDefect A z) = reflectionDefect B z := rfl

/-- An exact block descent criterion for each individual graph point. -/
theorem legal_iff_frequent_quotient_contraction (K : ℕ → Submodule ℝ H)
    [∀ n, (K n).HasOrthogonalProjection] (hm : Monotone K)
    (hV : (⨆ n, K n).topologicalClosure = closedSpace) (z : mixedReflectionRelation)
    {c : ℝ} (hc₀ : 0 < c) (hc : c < 1) :
    z.val.2 ∈ closedSpace ↔ ∃ᶠ n in atTop, ∃ m, n ≤ m ∧
      ‖reflectionDefect (K m) z‖ ^ 2 ≤ c * ‖reflectionDefect (K n) z‖ ^ 2 := by
  let e := fun n => ‖reflectionDefect (K n) z‖ ^ 2
  let L := ‖reflectionDefect closedSpace z‖ ^ 2
  have ht : Tendsto e atTop (𝓝 L) := (reflection_quotient_tendsto K hm hV z).pow 2
  have floor (n) : L ≤ e n := by
    have hsub : K n ≤ closedSpace := hV ▸
      (le_iSup K n).trans (Submodule.le_topologicalClosure _)
    have he := reflection_quotient_step hsub z
    change ‖reflectionDefect closedSpace z‖ ^ 2 ≤ ‖reflectionDefect (K n) z‖ ^ 2
    rw [he]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hzero : z.val.2 ∈ closedSpace ↔ L = 0 := by
    change _ ↔ ‖reflectionDefect closedSpace z‖ ^ 2 = 0
    rw [defect_norm, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero]
    exact ⟨fun h => (Submodule.starProjection_eq_self_iff.mpr h).symm,
      fun h => Submodule.starProjection_eq_self_iff.mp h.symm⟩
  rw [hzero]
  constructor
  · intro hz
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro n
    by_cases hn : e n = 0
    · exact ⟨n, le_rfl, by change e n ≤ c * e n; rw [hn, mul_zero]⟩
    · have hp : 0 < e n := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hn)
      obtain ⟨m, hm', he⟩ := ((eventually_ge_atTop n).and
        ((tendsto_order.mp (hz ▸ ht)).2 _ (mul_pos hc₀ hp))).exists
      exact ⟨m, hm', he.le⟩
  · intro h
    have hf : ∃ᶠ n in atTop, L ≤ c * e n :=
      h.mono fun n ⟨m, _, he⟩ => (floor m).trans he
    by_contra hn
    have hp : 0 < L := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hn)
    have hlt : c * L < L := by simpa only [one_mul] using mul_lt_mul_of_pos_right hc hp
    have he := (tendsto_order.mp ((tendsto_const_nhds (x := c)).mul ht)).2 _ hlt
    obtain ⟨n, hn, hn'⟩ := (hf.and_eventually he).exists
    exact (not_lt_of_ge hn) hn'

/-- Every mixed first difference represents the defect of an actual graph point:
the canonical lift has second coordinate minus the shift, and its first
coordinate already vanishes in the legal quotient. -/
theorem mixedDifference_in_defect_range (m : mixedClosure) :
    closedSpace.mkQ (hilbertDifference m.val) ∈
      LinearMap.range (reflectionDefect closedSpace).toLinearMap := by
  refine ⟨reflectionCoordinates.symm (m,0), ?_⟩
  change closedSpace.mkQ (0 - hilbertBackwardShiftContinuous m.val) =
    closedSpace.mkQ (m.val - hilbertBackwardShiftContinuous m.val)
  have hm : closedSpace.mkQ m.val = 0 := (Submodule.Quotient.mk_eq_zero _).mpr
    (mixedClosure_le_closedSpace m.property)
  rw [map_sub, map_sub, hm, map_zero]

/-- The legal obstruction has dense range, hence its Hausdorff cokernel
vanishes irrespective of the value of the vertical boundary. -/
theorem reflectionDefect_dense : DenseRange (reflectionDefect closedSpace) := by
  intro q
  obtain ⟨x, rfl⟩ := closedSpace.mkQ_surjective q
  have hx := mem_closure_image closedSpace.mkQL.continuous.continuousAt (mixedDifference_dense x)
  apply closure_mono _ hx
  rintro _ ⟨_, ⟨m,rfl⟩, rfl⟩
  exact mixedDifference_in_defect_range m

end RiemannResearch.RH.Pareto.PacketReflectionTower
