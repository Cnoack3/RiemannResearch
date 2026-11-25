import RiemannResearch.RH.MixedParityDigammaParseval
import RiemannResearch.RH.PhysicalHeadLayerIsometry

/-!
# Reconstructing the mixed projection of parity from its finite physical quotients

The signed conductor rows first compute every positive physical site. In the
orthogonal head coordinates, each finite quotient has a least-norm lift with
exactly those site values. These lifts converge to the full projected vector.
See the companion digamma Parseval module for the rational-node Gram formula.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis.DigammaParseval
open AffineHeadTower CenteredMeanSnake.DigammaSection

/-- Orthogonal projection of the unnormalized parity packet onto the mixed space. -/
abbrev projectedParity : mixedClosure :=
  mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 2)

/-- Signed coefficient of the projected, unnormalized parity packet at physical layer n. -/
def parityLayerCoefficient (n : ℕ) : ℝ :=
  ∑' q : Index, inner ℝ (unitHeadDirection n) (basis q) * digammaRow q 2

/-- Canonical mixed representative through the first N physical layers. -/
def parityLayerPrefix (N : ℕ) : mixedClosure :=
  ∑ n ∈ Finset.range N, parityLayerCoefficient n • unitHeadDirection n

/-- Mixed vectors vanishing at physical sites 1 through N. -/
def physicalKernelInMixed (N : ℕ) : Submodule ℝ mixedClosure :=
  (kernel N).comap mixedClosure.subtype

private theorem headLayer_eq_inner (x : mixedClosure) (n : ℕ) :
    headLayerIsometry x n = inner ℝ (unitHeadDirection n) x := by
  rw [headLayerIsometry, HilbertBasis.repr_apply_apply, physicalHeadBasis_apply]

private theorem inner_parityLayerPrefix {N i : ℕ} (hi : i < N) :
    inner ℝ (unitHeadDirection i) (parityLayerPrefix N) = parityLayerCoefficient i := by
  rw [parityLayerPrefix, inner_sum, Finset.sum_eq_single i]
  · rw [real_inner_smul_right, real_inner_self_eq_norm_sq, unitHeadDirection_orthonormal.1,
      one_pow, mul_one]
  · intro b _ hbi
    rw [real_inner_smul_right, unitHeadDirection_orthonormal.2 hbi.symm, mul_zero]
  · intro h
    exact (h (Finset.mem_range.mpr hi)).elim

/-- The arithmetic prefix recovers the exact projected class in every physical quotient. -/
theorem parityLayerPrefix_quotient (N : ℕ) :
    (physicalKernelInMixed N).mkQ projectedParity =
      (physicalKernelInMixed N).mkQ (parityLayerPrefix N) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change ((projectedParity - parityLayerPrefix N : mixedClosure) : ThresholdHilbert) ∈ kernel N
  apply (mem_kernel_iff_headLayer_prefix_zero N _).mpr
  intro i hi
  rw [headLayer_eq_inner, inner_sub_right, inner_parityLayerPrefix hi, ← headLayer_eq_inner]
  exact sub_eq_zero.mpr (physical_head_coefficient i)

/-- The compatible arithmetic quotient data have exactly one lift in the mixed Hilbert space. -/
theorem parityLayerPrefix_unique (x : mixedClosure) :
    (∀ N, (physicalKernelInMixed N).mkQ x =
      (physicalKernelInMixed N).mkQ (parityLayerPrefix N)) ↔ x = projectedParity := by
  constructor
  · intro h
    have hk : ((x - projectedParity : mixedClosure) : ThresholdHilbert) ∈ ⨅ N, kernel N := by
      rw [Submodule.mem_iInf]
      intro N
      have hq : (physicalKernelInMixed N).mkQ (x - projectedParity) = 0 := by
        rw [map_sub, h N, parityLayerPrefix_quotient N, sub_self]
      exact (Submodule.Quotient.mk_eq_zero (physicalKernelInMixed N)).mp hq
    rw [kernel_intersection, Submodule.mem_bot] at hk
    exact Subtype.ext (sub_eq_zero.mp hk)
  · rintro rfl
    exact parityLayerPrefix_quotient

/-- Vector-valued reconstruction in the complete Pareto norm. -/
theorem hasSum_parityLayerProjection :
    HasSum (fun n => parityLayerCoefficient n • unitHeadDirection n) projectedParity := by
  have hc (n : ℕ) : headLayerIsometry projectedParity n = parityLayerCoefficient n :=
    physical_head_coefficient n
  simpa only [hc, LinearIsometryEquiv.symm_apply_apply] using
    headLayer_synthesis (headLayerIsometry projectedParity)

theorem parityLayerPrefix_tendsto : Tendsto parityLayerPrefix atTop (𝓝 projectedParity) :=
  hasSum_parityLayerProjection.tendsto_sum_nat

/-- Physical site values computed from integrated packets and earlier conductor rows. -/
def paritySiteRow (q : Index) : ℕ → ℝ :=
  let prev (r : Finset.Iio q) : ℕ → ℝ := paritySiteRow r.val
  fun n => (ramanujanPacket q.val (n + 1) -
    ∑ r : Finset.Iio q, digammaRow r.val q.val * prev r n) /
    Real.sqrt (packetGramEntry q.val q.val - ∑ r : Finset.Iio q, (digammaRow r.val q.val) ^ 2)
termination_by q.val
decreasing_by exact (show r.val < q from Finset.mem_Iio.mp r.property)

private def mixedSite (n : ℕ) : mixedClosure →L[ℝ] ℝ :=
  (physicalEvaluationCLM n).comp mixedClosure.subtypeL

theorem paritySiteRow_eq (q : Index) : ∀ n : ℕ,
    paritySiteRow q n = physicalEvaluationCLM n (basis q : ThresholdHilbert) := by
  induction q using (measure (fun q : Index => q.val)).wf.induction with
  | h q ih =>
    intro n
    let F := (mixedSite n).toLinearMap
    change paritySiteRow q n = F (basis q)
    have hp (r : Finset.Iio q) : paritySiteRow r.val n = F (basis r.val) :=
      ih r.val (show r.val < q from Finset.mem_Iio.mp r.property) n
    have he : F (packet q) = ramanujanPacket q.val (n + 1) := by
      change physicalEvaluationCLM n (ramanujanPacketHilbert q.val) = _
      rw [physicalEvaluationCLM_apply, hilbertSequence_ramanujanPacketHilbert]
    rw [paritySiteRow, basis_functional_recurrence q F, he]
    simp only [hp]
    rw [Finset.sum_coe_sort (Finset.Iio q) (fun r => digammaRow r q.val * F (basis r)),
      Finset.sum_coe_sort (Finset.Iio q) (fun r => (digammaRow r q.val) ^ 2)]

/-- Every positive physical site of the projected vector is a signed arithmetic series. -/
theorem parity_site_hasSum (n : ℕ) :
    HasSum (fun q : Index => digammaRow q 2 * paritySiteRow q n)
      (physicalEvaluationCLM n (projectedParity : ThresholdHilbert)) := by
  have hs := (mixedSite n).hasSum hasSum_parity_modes
  simpa only [map_smul, smul_eq_mul, paritySiteRow_eq, mixedSite, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply] using hs

/-- Forget the physical constraints from N through L-1. -/
def physicalQuotientRestriction {N L : ℕ} (h : N ≤ L) :
    (mixedClosure ⧸ physicalKernelInMixed L) →ₗ[ℝ] (mixedClosure ⧸ physicalKernelInMixed N) :=
  (physicalKernelInMixed L).mapQ (physicalKernelInMixed N) LinearMap.id
    (show physicalKernelInMixed L ≤ physicalKernelInMixed N from
      fun _ hx => kernel_antitone h hx)

/-- The computed finite classes form an inverse system. -/
theorem parityLayerPrefix_compatible {N L : ℕ} (h : N ≤ L) :
    physicalQuotientRestriction h ((physicalKernelInMixed L).mkQ (parityLayerPrefix L)) =
      (physicalKernelInMixed N).mkQ (parityLayerPrefix N) := by
  rw [← parityLayerPrefix_quotient L, ← parityLayerPrefix_quotient N]
  rfl

/-- Once a physical site enters the head, all later quotient representatives have its exact value. -/
theorem parityLayerPrefix_site {N i : ℕ} (hi : i < N) :
    physicalEvaluationCLM i (projectedParity : ThresholdHilbert) =
      physicalEvaluationCLM i (parityLayerPrefix N : ThresholdHilbert) := by
  have hq : (physicalKernelInMixed N).mkQ (projectedParity - parityLayerPrefix N) = 0 := by
    rw [map_sub, parityLayerPrefix_quotient, sub_self]
  have hk : ((projectedParity - parityLayerPrefix N : mixedClosure) : ThresholdHilbert) ∈ kernel N :=
    (Submodule.Quotient.mk_eq_zero (physicalKernelInMixed N)).mp hq
  have he := ((mem_kernel N).mp hk).2 i hi
  change physicalEvaluationCLM i ((projectedParity : ThresholdHilbert) - (parityLayerPrefix N : ThresholdHilbert)) = 0 at he
  rw [map_sub, sub_eq_zero] at he
  exact he

/-- Forward substitution in the physical quotient tower using the arithmetic site value. -/
theorem parityLayerCoefficient_from_site (n : ℕ) :
    parityLayerCoefficient n = ((∑' q : Index, digammaRow q 2 * paritySiteRow q n) -
      physicalEvaluationCLM n (parityLayerPrefix n : ThresholdHilbert)) * ‖direction n‖ := by
  have hn : ‖direction n‖ ≠ 0 := norm_ne_zero_iff.mpr (by
    intro hz
    simpa [hz] using direction_eval n)
  have he := parityLayerPrefix_site (N := n+1) (i := n) (Nat.lt_succ_self n)
  have hs : parityLayerPrefix (n+1) = parityLayerPrefix n +
      parityLayerCoefficient n • unitHeadDirection n := by
    simp only [parityLayerPrefix, Finset.sum_range_succ]
  rw [hs] at he
  change physicalEvaluationCLM n (projectedParity : ThresholdHilbert) =
    physicalEvaluationCLM n ((parityLayerPrefix n : ThresholdHilbert) +
      parityLayerCoefficient n • (unitHeadDirection n : ThresholdHilbert)) at he
  simp only [map_add, map_smul, unitHeadDirection_val, direction_eval, smul_eq_mul, mul_one] at he
  rw [(parity_site_hasSum n).tsum_eq]
  change parityLayerCoefficient n = (physicalEvaluationCLM n (projectedParity : ThresholdHilbert) -
    physicalEvaluationCLM n (parityLayerPrefix n : ThresholdHilbert)) * ‖direction n‖
  rw [he]
  field_simp [hn]
  <;> ring

/-- The signed physical coefficient can be tested directly against J₂. -/
theorem parityLayerCoefficient_eq_ambient (n : ℕ) :
    parityLayerCoefficient n = inner ℝ (unitHeadDirection n : ThresholdHilbert)
      (ramanujanPacketHilbert 2) := by
  have hp := mixedClosure.sub_starProjection_mem_orthogonal (ramanujanPacketHilbert 2)
    (unitHeadDirection n : ThresholdHilbert) (unitHeadDirection n).property
  rw [inner_sub_right, sub_eq_zero] at hp
  calc
    parityLayerCoefficient n = headLayerIsometry projectedParity n :=
      (physical_head_coefficient n).symm
    _ = inner ℝ (unitHeadDirection n) projectedParity := headLayer_eq_inner _ _
    _ = _ := hp.symm

/-- The square of the finite representative is exactly its retained coordinate energy. -/
theorem parityLayerPrefix_norm_sq (N : ℕ) :
    ‖parityLayerPrefix N‖ ^ 2 = ∑ i ∈ Finset.range N, (parityLayerCoefficient i) ^ 2 := by
  calc
    ‖parityLayerPrefix N‖ ^ 2 = inner ℝ (parityLayerPrefix N) (parityLayerPrefix N) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∑ i ∈ Finset.range N,
        inner ℝ (parityLayerCoefficient i • unitHeadDirection i) (parityLayerPrefix N) := by
      change inner ℝ (∑ i ∈ Finset.range N, parityLayerCoefficient i • unitHeadDirection i)
        (parityLayerPrefix N) = _
      rw [sum_inner]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [real_inner_smul_left, inner_parityLayerPrefix (Finset.mem_range.mp hi), sq]

/-- Exact norm cost of every lift of the finite parity quotient class. -/
theorem parityLayerPrefix_lift_cost (N : ℕ) (x : mixedClosure)
    (hx : (physicalKernelInMixed N).mkQ x = (physicalKernelInMixed N).mkQ (parityLayerPrefix N)) :
    ‖x‖ ^ 2 = ‖parityLayerPrefix N‖ ^ 2 + ‖x - parityLayerPrefix N‖ ^ 2 := by
  have hq : (physicalKernelInMixed N).mkQ (x - parityLayerPrefix N) = 0 := by
    rw [map_sub, hx, sub_self]
  have hk : ((x - parityLayerPrefix N : mixedClosure) : ThresholdHilbert) ∈ kernel N :=
    (Submodule.Quotient.mk_eq_zero (physicalKernelInMixed N)).mp hq
  have hz := (mem_kernel_iff_headLayer_prefix_zero N _).mp hk
  have ho : inner ℝ (parityLayerPrefix N) (x - parityLayerPrefix N) = 0 := by
    calc
      _ = ∑ i ∈ Finset.range N,
          inner ℝ (parityLayerCoefficient i • unitHeadDirection i) (x - parityLayerPrefix N) := by
        change inner ℝ (∑ i ∈ Finset.range N, parityLayerCoefficient i • unitHeadDirection i)
          (x - parityLayerPrefix N) = _
        rw [sum_inner]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [real_inner_smul_left, ← headLayer_eq_inner, hz i (Finset.mem_range.mp hi), mul_zero]
  calc
    ‖x‖ ^ 2 = ‖parityLayerPrefix N + (x - parityLayerPrefix N)‖ ^ 2 := by
      rw [show parityLayerPrefix N + (x - parityLayerPrefix N) = x by abel]
    _ = _ := by rw [norm_add_sq_real, ho]; ring

/-- Exact projection error after an arbitrary finite head truncation. -/
theorem parityLayerPrefix_error (N : ℕ) :
    ‖projectedParity - parityLayerPrefix N‖ ^ 2 +
      (∑ i ∈ Finset.range N, (parityLayerCoefficient i) ^ 2) = ‖projectedParity‖ ^ 2 := by
  rw [← parityLayerPrefix_norm_sq, add_comm]
  exact (parityLayerPrefix_lift_cost N _ (parityLayerPrefix_quotient N)).symm

/-- Equality with the minimal cost singles out the prefix among all representatives. -/
theorem parityLayerPrefix_unique_minimum (N : ℕ) (x : mixedClosure)
    (hx : (physicalKernelInMixed N).mkQ x = (physicalKernelInMixed N).mkQ (parityLayerPrefix N)) :
    ‖x‖ ^ 2 ≤ ‖parityLayerPrefix N‖ ^ 2 ↔ x = parityLayerPrefix N := by
  constructor
  · intro h
    have h0 : ‖x - parityLayerPrefix N‖ ^ 2 = 0 :=
      le_antisymm (by linarith only [h, parityLayerPrefix_lift_cost N x hx]) (sq_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp h0))
  · rintro rfl
    exact le_rfl

end RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis.DigammaParseval
