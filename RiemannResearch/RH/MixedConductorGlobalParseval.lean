import RiemannResearch.RH.MixedConductorHilbertBasis
import RiemannResearch.RH.MixedConductorPrimeSupport
import RiemannResearch.RH.MixedConductorSplitExact
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.MixedCaptureLegalTrials
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The legal mean and the Hilbert sum of prime-support layers

The scalar coordinate is represented by its vector in the screened line, with the
inherited Pareto norm. The second factor is mathlib's external Hilbert sum of
the layers. The legal mean splitting gives analysis and synthesis at the first
step and the orthogonal-family construction gives them on the mixed factor.

The Hilbert-sum construction uses Mathlib.Analysis.InnerProductSpace.l2Space.
The arithmetic specialization uses the full conductor-two capture identity.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis
open CoefficientStabilization

/-- The retraction in the split legal-mean sequence is the mixed orthogonal projection. -/
theorem legalMixedRetraction_eq_projection (v : closedSpace) :
    legalMixedRetraction v = mixedClosure.orthogonalProjectionOnto (v : ThresholdHilbert) := by
  apply Subtype.ext
  have h := fullScreening_eq_mean_smul v.property
  change (v : ThresholdHilbert) - mixedClosure.starProjection v =
    legalPacketMean v • normalizedScreenedTwo at h
  change (v : ThresholdHilbert) - legalPacketMean v • normalizedScreenedTwo =
    mixedClosure.starProjection v
  rw [← h, sub_sub_cancel]

theorem inner_mixed_screened (m : mixedClosure) (a : ℝ) :
    inner ℝ (legalMixedInclusion m) (screenedMeanSection a) = 0 := by
  have hu := normalizedScreenedTwo_mem_screenedPrimeClosure
  rw [screenedPrimeClosure_eq_inf_orthogonal] at hu
  change inner ℝ (m : ThresholdHilbert) (a • normalizedScreenedTwo) = 0
  rw [real_inner_smul_right, hu.2 m m.property, mul_zero]

private theorem reassemble (v : closedSpace) :
    legalMixedInclusion (legalMixedRetraction v) +
      screenedMeanSection (legalPacketMean v) = v := by
  rw [legalMixedInclusion_legalMixedRetraction, sub_add_cancel]

theorem legal_norm_sq_split (v : closedSpace) :
    ‖v‖ ^ 2 = |legalPacketMean v| ^ 2 * ‖normalizedScreenedTwo‖ ^ 2 +
      ‖legalMixedRetraction v‖ ^ 2 := by
  calc
    ‖v‖ ^ 2 = ‖legalMixedInclusion (legalMixedRetraction v) +
        screenedMeanSection (legalPacketMean v)‖ ^ 2 :=
      congrArg (fun z => ‖z‖ ^ 2) (reassemble v).symm
    _ = _ := by
      rw [norm_add_sq_real, inner_mixed_screened]
      change ‖legalMixedRetraction v‖ ^ 2 + 2 * 0 +
        ‖legalPacketMean v • normalizedScreenedTwo‖ ^ 2 = _
      rw [norm_smul, Real.norm_eq_abs, mul_pow]
      ring

/-- The omitted energy is exactly the squared distance to the support cutoff. -/
theorem supportLayer_energy_remainder (n : ℕ) (m : mixedClosure) :
    (∑ k ∈ Finset.range n, ‖(supportLayer k).starProjection m‖ ^ 2) +
      ‖m - (supportSpace n).starProjection m‖ ^ 2 = ‖m‖ ^ 2 := by
  rw [sum_supportLayer_energy, ← Submodule.starProjection_orthogonal_val]
  exact (Submodule.norm_sq_eq_add_norm_sq_projection m (supportSpace n)).symm

/-- A Möbius coordinate above the cutoff gives a lower bound on the omitted norm. -/
theorem supportCoordinate_tail_bound (n : ℕ) (q : Index) (hq : n < q.val.primeFactors.card)
    (m : mixedClosure) :
    |supportCoordinate q m| ≤ ‖supportCoordinate q‖ * ‖m - (supportSpace n).starProjection m‖ := by
  have hz : supportCoordinate q ((supportSpace n).starProjection m) = 0 :=
    supportSpace_le_coordinate_ker q hq ((supportSpace n).starProjection_apply_mem m)
  simpa only [map_sub, hz, sub_zero, Real.norm_eq_abs] using
    (supportCoordinate q).le_opNorm (m - (supportSpace n).starProjection m)

/-- Every cutoff from one onward misses a full unit vector in the very next layer. -/
theorem exists_unit_missed_by_support_cutoff (n : ℕ) (hn : 1 ≤ n) :
    ∃ m : mixedClosure, ‖m‖ = 1 ∧ (supportSpace n).starProjection m = 0 := by
  obtain ⟨x, hx, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (supportLayer_ne_bot n hn)
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hne
  refine ⟨‖x‖⁻¹ • x, ?_, (Submodule.starProjection_apply_eq_zero_iff _).mpr
    ((supportSpace n).orthogonal.smul_mem _ hx.2)⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']

/-- Global Pythagoras with both the scalar weight and the full truncation error. -/
theorem legal_support_energy_remainder (v : closedSpace) (n : ℕ) :
    ‖v‖ ^ 2 = |legalPacketMean v| ^ 2 * ‖normalizedScreenedTwo‖ ^ 2 +
      (∑ k ∈ Finset.range n, ‖(supportLayer k).starProjection (legalMixedRetraction v)‖ ^ 2) +
      ‖legalMixedRetraction v - (supportSpace n).starProjection (legalMixedRetraction v)‖ ^ 2 := by
  rw [add_assoc, supportLayer_energy_remainder, legal_norm_sq_split]

theorem tendsto_legal_support_reconstruction (v : closedSpace) :
    Tendsto (fun n => screenedMeanSection (legalPacketMean v) +
      legalMixedInclusion (∑ k ∈ Finset.range n,
        (supportLayer k).starProjection (legalMixedRetraction v)))
      atTop (𝓝 v) := by
  have h := legalMixedInclusion.continuous.continuousAt.tendsto.comp
    (tendsto_sum_supportLayer_projection (legalMixedRetraction v))
  simpa only [Function.comp_def, add_comm (screenedMeanSection _) _, reassemble] using
    (tendsto_const_nhds (x := screenedMeanSection (legalPacketMean v))).add h

theorem tendsto_legal_support_energy (v : closedSpace) :
    Tendsto (fun n => |legalPacketMean v| ^ 2 * ‖normalizedScreenedTwo‖ ^ 2 +
      ∑ k ∈ Finset.range n, ‖(supportLayer k).starProjection (legalMixedRetraction v)‖ ^ 2)
      atTop (𝓝 (‖v‖ ^ 2)) := by
  rw [legal_norm_sq_split v]
  exact tendsto_const_nhds.add (tendsto_sum_supportLayer_energy (legalMixedRetraction v))

/-- Summing the layer energies is unconditional. -/
theorem hasSum_supportLayer_energy (m : mixedClosure) :
    HasSum (fun k => ‖(supportLayer k).starProjection m‖ ^ 2) (‖m‖ ^ 2) :=
  (hasSum_iff_tendsto_nat_of_nonneg (fun k => sq_nonneg ‖(supportLayer k).starProjection m‖) _).2
    (tendsto_sum_supportLayer_energy m)

/-- The layer expansion and the conductor-ordered Hilbert basis measure the same mixed energy. -/
theorem support_energy_eq_conductor_basis (x : ThresholdHilbert) :
    (∑' k, ‖(supportLayer k).starProjection (mixedClosure.orthogonalProjectionOnto x)‖ ^ 2) =
      ∑' q : Index, (inner ℝ (basis q : ThresholdHilbert) x) ^ 2 := by
  rw [projection_parseval]
  exact (hasSum_supportLayer_energy _).tsum_eq

theorem legal_support_parseval (v : closedSpace) :
    ‖v‖ ^ 2 = |legalPacketMean v| ^ 2 * ‖normalizedScreenedTwo‖ ^ 2 +
      ∑' k, ‖(supportLayer k).starProjection (legalMixedRetraction v)‖ ^ 2 := by
  rw [(hasSum_supportLayer_energy (legalMixedRetraction v)).tsum_eq, legal_norm_sq_split]

/-- The layer subspaces form an internal Hilbert sum, without choosing bases in the layers. -/
theorem supportLayer_isHilbertSum :
    IsHilbertSum ℝ (fun k => ↥(supportLayer k)) (fun k => (supportLayer k).subtypeₗᵢ) := by
  let (k : ℕ) : CompleteSpace (supportLayer k) :=
    ((show IsClosed (supportSpace (k + 1) : Set mixedClosure) from isClosed_closure).inter
      (supportSpace k).isClosed_orthogonal).completeSpace_coe
  apply IsHilbertSum.mkInternal supportLayer
  · intro i j hij x y
    rcases lt_or_gt_of_ne hij with h | h
    · exact supportLayer_orthogonal h x.property y.property
    · exact inner_eq_zero_symm.mp (supportLayer_orthogonal h y.property x.property)
  · intro m _
    apply (⨆ k, supportLayer k).isClosed_topologicalClosure.mem_of_tendsto
      (tendsto_sum_supportLayer_projection m)
    exact Filter.Eventually.of_forall fun n => Submodule.le_topologicalClosure _
      (Submodule.sum_mem _ fun k _ =>
        (le_iSup supportLayer k) ((supportLayer k).starProjection_apply_mem m))

def supportLayerEquiv : mixedClosure ≃ₗᵢ[ℝ] lp (fun k => ↥(supportLayer k)) 2 :=
  supportLayer_isHilbertSum.linearIsometryEquiv

/-- Each analysis coordinate is the orthogonal projection onto its layer. -/
theorem supportLayerEquiv_apply (m : mixedClosure) (k : ℕ) :
    supportLayerEquiv m k = (supportLayer k).orthogonalProjectionOnto m := by
  apply ext_inner_left ℝ
  intro y
  have hi := supportLayerEquiv.symm.inner_map_map (lp.single 2 k y) (supportLayerEquiv m)
  have hs : supportLayerEquiv.symm (lp.single 2 k y) = (y : mixedClosure) :=
    supportLayer_isHilbertSum.linearIsometryEquiv_symm_apply_single y
  rw [hs, supportLayerEquiv.symm_apply_apply, lp.inner_single_left] at hi
  have hp := (supportLayer k).sub_starProjection_mem_orthogonal m (y : mixedClosure) y.property
  rw [inner_sub_right, sub_eq_zero] at hp
  exact hi.symm.trans hp

/-- Both factors carry Hilbert norms. The first is the physical scalar line. -/
abbrev LegalSupportSum := WithLp 2 (screenedPrimeClosure × lp (fun k => ↥(supportLayer k)) 2)

/-- Mean coordinates on the screened line. Its Hilbert norm is the inherited Pareto norm. -/
def screenedScalarParametrization : ℝ ≃ₗ[ℝ] screenedPrimeClosure where
  toFun a := ⟨a • normalizedScreenedTwo,
    screenedPrimeClosure.smul_mem a normalizedScreenedTwo_mem_screenedPrimeClosure⟩
  invFun w := inner ℝ (w : ThresholdHilbert) hilbertOne
  left_inv a := by
    change inner ℝ (a • normalizedScreenedTwo) hilbertOne = a
    rw [real_inner_smul_left, normalizedScreenedTwo_mean, mul_one]
  right_inv w := by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      (screenedPrimeClosure_eq_span_two.le w.property)
    apply Subtype.ext
    change inner ℝ (w : ThresholdHilbert) hilbertOne • normalizedScreenedTwo =
      (w : ThresholdHilbert)
    rw [← ha, real_inner_smul_left, normalizedScreenedTwo_mean, mul_one]
  map_add' a b := Subtype.ext (add_smul a b normalizedScreenedTwo)
  map_smul' a b := Subtype.ext (mul_smul a b normalizedScreenedTwo)

theorem norm_screenedScalarParametrization (a : ℝ) :
    ‖screenedScalarParametrization a‖ = |a| * ‖normalizedScreenedTwo‖ := by
  change ‖a • normalizedScreenedTwo‖ = _
  rw [norm_smul, Real.norm_eq_abs]

private def legalSupportAnalysis : closedSpace →ₗᵢ[ℝ] LegalSupportSum where
  toLinearMap := (WithLp.linearEquiv 2 ℝ _).symm.toLinearMap.comp
    ((screenedScalarParametrization.toLinearMap.comp legalPacketMean.toLinearMap).prod
      (supportLayerEquiv.toLinearEquiv.toLinearMap.comp legalMixedRetraction.toLinearMap))
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖legalPacketMean v • normalizedScreenedTwo‖ ^ 2 +
      ‖supportLayerEquiv (legalMixedRetraction v)‖ ^ 2 = _
    rw [supportLayerEquiv.norm_map, norm_smul, Real.norm_eq_abs, mul_pow]
    exact (legal_norm_sq_split v).symm

private theorem retract_synthesis (a : ℝ) (m : mixedClosure) :
    legalMixedRetraction (screenedMeanSection a + legalMixedInclusion m) = m := by
  apply Subtype.ext
  change ((screenedMeanSection a + legalMixedInclusion m -
    screenedMeanSection (legalPacketMean (screenedMeanSection a + legalMixedInclusion m)) :
      closedSpace) : ThresholdHilbert) = _
  rw [map_add, legalPacketMean_screenedMeanSection, legalPacketMean_legalMixedInclusion, add_zero,
    add_sub_cancel_left]
  rfl

/-- The global Pareto isometry. Synthesis is defined on every square-summable family. -/
def legalSupportEquiv : closedSpace ≃ₗᵢ[ℝ] LegalSupportSum := by
  apply LinearIsometryEquiv.ofSurjective legalSupportAnalysis
  intro z
  let a := screenedScalarParametrization.symm z.ofLp.1
  have ha : a • normalizedScreenedTwo = (z.ofLp.1 : ThresholdHilbert) :=
    congrArg Subtype.val (screenedScalarParametrization.apply_symm_apply z.ofLp.1)
  let m := supportLayerEquiv.symm z.ofLp.2
  refine ⟨screenedMeanSection a + legalMixedInclusion m, ?_⟩
  apply (WithLp.linearEquiv 2 ℝ _).injective
  apply Prod.ext
  · apply Subtype.ext
    change legalPacketMean (screenedMeanSection a + legalMixedInclusion m) • normalizedScreenedTwo =
      (z.ofLp.1 : ThresholdHilbert)
    rwa [map_add, legalPacketMean_screenedMeanSection,
      legalPacketMean_legalMixedInclusion, add_zero]
  · change supportLayerEquiv
      (legalMixedRetraction (screenedMeanSection a + legalMixedInclusion m)) = z.ofLp.2
    rw [retract_synthesis]
    exact supportLayerEquiv.apply_symm_apply _

theorem legalSupportEquiv_scalar (v : closedSpace) :
    ((legalSupportEquiv v).ofLp.1 : ThresholdHilbert) =
      legalPacketMean v • normalizedScreenedTwo := rfl

theorem legalSupportEquiv_layer (v : closedSpace) (k : ℕ) :
    (legalSupportEquiv v).ofLp.2 k =
      (supportLayer k).orthogonalProjectionOnto (legalMixedRetraction v) :=
  supportLayerEquiv_apply _ _

theorem hasSum_supportLayer_synthesis (z : LegalSupportSum) :
    HasSum (fun k => (z.ofLp.2 k : mixedClosure)) (supportLayerEquiv.symm z.ofLp.2) :=
  supportLayer_isHilbertSum.hasSum_linearIsometryEquiv_symm _

/-- Synthesis recovers the scalar vector plus the convergent mixed sum. -/
theorem legalSupportEquiv_symm_apply (z : LegalSupportSum) :
    (legalSupportEquiv.symm z : ThresholdHilbert) =
      (z.ofLp.1 : ThresholdHilbert) + (supportLayerEquiv.symm z.ofLp.2 : mixedClosure).val := by
  obtain ⟨v, rfl⟩ := legalSupportEquiv.surjective z
  rw [legalSupportEquiv.symm_apply_apply, legalSupportEquiv_scalar]
  change (v : ThresholdHilbert) = legalPacketMean v • normalizedScreenedTwo +
    (supportLayerEquiv.symm (supportLayerEquiv (legalMixedRetraction v)) : mixedClosure).val
  rw [supportLayerEquiv.symm_apply_apply]
  change (v : ThresholdHilbert) = legalPacketMean v • normalizedScreenedTwo +
    ((v : ThresholdHilbert) - legalPacketMean v • normalizedScreenedTwo)
  exact (add_sub_cancel _ _).symm

/-- Orthogonal projection of the mean-one parity input. -/
def parityMixedProjection : mixedClosure :=
  mixedClosure.orthogonalProjectionOnto ((Real.log 2)⁻¹ • ramanujanPacketHilbert 2)

private theorem parityMixedProjection_norm_sq :
    ‖parityMixedProjection‖ ^ 2 = (Real.log 2)⁻¹ - ‖normalizedScreenedTwo‖ ^ 2 := by
  change ‖mixedClosure.starProjection ((Real.log 2)⁻¹ • ramanujanPacketHilbert 2)‖ ^ 2 = _
  rw [map_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, full_mixed_capture_eq_limitEnergy,
    normalizedScreenedTwo_norm_sq]
  field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', one_sub_limitEnergy_pos.ne']

/-- The endpoint deficit is the sum of the unresolved defect and the exact omitted energy. -/
theorem parity_support_deficit (n : ℕ) :
    (Real.log 2)⁻¹ - 1 -
      (∑ k ∈ Finset.range n, ‖(supportLayer k).starProjection parityMixedProjection‖ ^ 2) =
      ‖normalizedScreenedTwo - hilbertOne‖ ^ 2 +
      ‖parityMixedProjection - (supportSpace n).starProjection parityMixedProjection‖ ^ 2 := by
  have ht := supportLayer_energy_remainder n parityMixedProjection
  rw [parityMixedProjection_norm_sq] at ht
  rw [norm_sub_sq_real, normalizedScreenedTwo_mean, hilbertOne_norm_sq]
  linarith

/-- Norm one is equivalent to saturation of the finite-support energies of parity. -/
theorem parity_support_saturation_iff_norm_one :
    Tendsto (fun n => ∑ k ∈ Finset.range n,
      ‖(supportLayer k).starProjection parityMixedProjection‖ ^ 2)
      atTop (𝓝 ((Real.log 2)⁻¹ - 1)) ↔ ‖normalizedScreenedTwo‖ = 1 := by
  have h := tendsto_sum_supportLayer_energy parityMixedProjection
  rw [parityMixedProjection_norm_sq] at h
  constructor
  · intro he
    have eqn := tendsto_nhds_unique h he
    nlinarith [norm_nonneg normalizedScreenedTwo]
  · intro hu
    simpa only [hu, one_pow] using h

/-- The open endpoint has a one-sided test with one cutoff for each tolerance. -/
theorem norm_one_iff_forall_support_capture :
    ‖normalizedScreenedTwo‖ = 1 ↔ ∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
      (Real.log 2)⁻¹ - 1 - ε <
        ∑ k ∈ Finset.range n, ‖(supportLayer k).starProjection parityMixedProjection‖ ^ 2 := by
  constructor
  · intro hu ε hε
    exact ((tendsto_order.mp (parity_support_saturation_iff_norm_one.mpr hu)).1 _
      (sub_lt_self _ hε)).exists
  · intro h
    apply le_antisymm _ one_le_norm_normalizedScreenedTwo
    by_contra! hgt
    have hpos : 0 < ‖normalizedScreenedTwo‖ ^ 2 - 1 := by
      nlinarith only [hgt, sq_nonneg (‖normalizedScreenedTwo‖ - 1)]
    obtain ⟨n, hn⟩ := h _ hpos
    have ht := supportLayer_energy_remainder n parityMixedProjection
    rw [parityMixedProjection_norm_sq] at ht
    linarith only [ht, hn, sq_nonneg
      ‖parityMixedProjection - (supportSpace n).starProjection parityMixedProjection‖]

end RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis
