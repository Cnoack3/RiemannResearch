import RiemannResearch.RH.ParetoAffineHeadTower
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Hilbert coordinates for the decreasing physical-head kernels

The minimum mixed corrections for successive physical observations become an
orthonormal basis after normalization. Their coefficient isometry realizes
each finite head kernel as the sequences with the corresponding initial
coefficients zero. Source: the physical-head tower and its density theorem in
`ParetoAffineHeadTower`.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.AffineHeadTower

private instance mixedHeadComplete : CompleteSpace mixedClosure :=
  (show IsClosed (mixedClosure : Set ThresholdHilbert) from isClosed_closure).completeSpace_coe

private def mixedHeadDirection (n : ℕ) : mixedClosure :=
  ⟨direction n, ((mem_kernel n).mp (direction_mem n)).1⟩

private theorem mixedHeadDirection_ne_zero (n : ℕ) : mixedHeadDirection n ≠ 0 := by
  intro hz
  have hd : direction n = 0 := congrArg Subtype.val hz
  simpa [hd] using direction_eval n

/-- Unit vector in the line removed when the next physical value is imposed. -/
def unitHeadDirection (n : ℕ) : mixedClosure :=
  (‖mixedHeadDirection n‖ : ℝ)⁻¹ • mixedHeadDirection n

theorem unitHeadDirection_val (n : ℕ) : (unitHeadDirection n : ThresholdHilbert) =
    ‖direction n‖⁻¹ • direction n := rfl

theorem unitHeadDirection_orthonormal : Orthonormal ℝ unitHeadDirection := by
  constructor
  · intro i
    have hpos := norm_pos_iff.mpr (mixedHeadDirection_ne_zero i)
    rw [unitHeadDirection, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
      inv_mul_cancel₀ hpos.ne']
  · intro i j hij
    have h : inner ℝ (mixedHeadDirection i) (mixedHeadDirection j) = 0 := by
      change inner ℝ (direction i) (direction j) = 0
      rcases lt_or_gt_of_ne hij with h | h
      · rw [real_inner_comm, directions_inner h]
      · exact directions_inner h
    simp only [unitHeadDirection, real_inner_smul_left, real_inner_smul_right, h, mul_zero]

private theorem unitHeadDirection_span_orthogonal :
    (Submodule.span ℝ (Set.range unitHeadDirection))ᗮ = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hinner (n : ℕ) : inner ℝ (direction n) (x : ThresholdHilbert) = 0 := by
    have h := hx (unitHeadDirection n) (Submodule.subset_span (Set.mem_range_self n))
    rw [unitHeadDirection, real_inner_smul_left, mul_eq_zero] at h
    exact h.resolve_left (inv_ne_zero (norm_ne_zero_iff.mpr (mixedHeadDirection_ne_zero n)))
  have hz : (x : ThresholdHilbert) ∈ mixedClosureᗮ := by
    have heq : mixedClosureᗮ = (Submodule.span ℝ (Set.range direction))ᗮ := by
      rw [← directions_dense, Submodule.orthogonal_closure]
    rw [heq]
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨n, rfl⟩ := hz
      exact hinner n
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul a b _ hb => rw [real_inner_smul_left, hb, mul_zero]
  apply (Submodule.mem_bot ℝ).mpr
  apply Subtype.ext
  exact inner_self_eq_zero.mp (hz x x.property)

/-- The physical-head Hilbert basis of the full mixed space. -/
def physicalHeadBasis : HilbertBasis ℕ ℝ mixedClosure :=
  HilbertBasis.mkOfOrthogonalEqBot unitHeadDirection_orthonormal unitHeadDirection_span_orthogonal

theorem physicalHeadBasis_apply (n : ℕ) : physicalHeadBasis n = unitHeadDirection n := by
  simp only [physicalHeadBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- The coefficient map onto all square-summable sequences of physical layers. -/
def headLayerIsometry : mixedClosure ≃ₗᵢ[ℝ] lp (fun _ : ℕ => ℝ) 2 :=
  physicalHeadBasis.repr

theorem headLayerIsometry_apply (x : mixedClosure) (n : ℕ) :
    headLayerIsometry x n = ‖direction n‖⁻¹ * inner ℝ (direction n) (x : ThresholdHilbert) := by
  rw [headLayerIsometry, HilbertBasis.repr_apply_apply, physicalHeadBasis_apply,
    unitHeadDirection, real_inner_smul_left]
  rfl

/-- The squared coordinate energies sum to the complete Pareto norm squared. -/
theorem headLayer_hasSum (x : mixedClosure) :
    HasSum (fun n => (headLayerIsometry x n) ^ 2) (‖x‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
    LinearIsometryEquiv.norm_map] using
    (lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) (headLayerIsometry x))

/-- Parseval for the individual physical layers with their certified unit normalization. -/
theorem headLayer_parseval (x : mixedClosure) :
    ∑' n, (headLayerIsometry x n) ^ 2 = ‖x‖ ^ 2 := (headLayer_hasSum x).tsum_eq

/-- Every square-summable sequence synthesizes a mixed vector in complete norm. -/
theorem headLayer_synthesis (c : lp (fun _ : ℕ => ℝ) 2) :
    HasSum (fun n => c n • unitHeadDirection n) (headLayerIsometry.symm c) := by
  simpa only [headLayerIsometry, physicalHeadBasis_apply] using physicalHeadBasis.hasSum_repr_symm c

private theorem headLayer_zero_iff_evaluation (n : ℕ) (x : mixedClosure)
    (hx : (x : ThresholdHilbert) ∈ kernel n) :
    headLayerIsometry x n = 0 ↔ physicalEvaluationCLM n (x : ThresholdHilbert) = 0 := by
  have hd : direction n ≠ 0 := by
    intro h
    simpa [h] using direction_eval n
  have hinner : inner ℝ (direction n) (x : ThresholdHilbert) =
      (‖row n‖ ^ 2)⁻¹ * physicalEvaluationCLM n x := by
    rw [show inner ℝ (direction n) (x : ThresholdHilbert) = inner ℝ (x : ThresholdHilbert)
      (direction n) from real_inner_comm _ _, direction, real_inner_smul_right, row_inner n hx]
  rw [headLayerIsometry_apply, hinner]
  simp [norm_ne_zero_iff.mpr hd, row_ne_zero n]

/-- A finite physical-head kernel corresponds exactly to the coordinate tail in ℓ². -/
theorem mem_kernel_iff_headLayer_prefix_zero (n : ℕ) (x : mixedClosure) :
    (x : ThresholdHilbert) ∈ kernel n ↔ ∀ i < n, headLayerIsometry x i = 0 := by
  induction n with
  | zero => exact ⟨fun _ i hi => by omega, fun _ => x.property⟩
  | succ n ih =>
    change ((x : ThresholdHilbert) ∈ kernel n ∧ physicalEvaluationCLM n x = 0) ↔ _
    constructor
    · rintro ⟨hx, he⟩ i hi
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | h
      · exact ih.mp hx i h
      · subst i
        exact (headLayer_zero_iff_evaluation n x hx).mpr he
    · intro h
      have hx := ih.mpr (fun i hi => h i (Nat.lt_succ_of_lt hi))
      exact ⟨hx, (headLayer_zero_iff_evaluation n x hx).mp (h n (Nat.lt_succ_self _))⟩

end RiemannResearch.RH.Pareto.PrimePowerSchur.AffineHeadTower
