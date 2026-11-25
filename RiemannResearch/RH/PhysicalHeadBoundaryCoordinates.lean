import RiemannResearch.RH.PhysicalHeadInfiniteBoundary
import RiemannResearch.RH.PhysicalHeadLayerIsometry
import RiemannResearch.RH.PhysicalHeadSequenceCokernel

/-!
# Orthonormal coordinates of the infinite physical-head snake

Finite prefixes of a tower cochain have stable Hilbert coefficients. Sending a cochain
to these coefficients gives all scalar sequences. The coboundaries give precisely the
square-summable ones. In this algebraic quotient the connecting class is the signed
sequence of the normalized adjacent displacements.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadBoundaryCoordinates

open CoefficientStabilization AffineHeadTower PhysicalHeadStageAlgebra PhysicalHeadSequenceCokernel
open CenteredMeanSnake.PhysicalHeadSections

private abbrev ScalarL2 := lp (fun _ : ℕ => ℝ) 2

/-- The signed coefficient along the next normalized physical-head direction. -/
def signedCarry (n : ℕ) : ℝ := (1 - physicalEvaluationCLM n (patch n)) * ‖direction n‖

theorem signedCarry_eq_div_rowNorm (n : ℕ) :
    signedCarry n = (1 - physicalEvaluationCLM n (patch n)) / ‖row n‖ := by
  have hn := norm_ne_zero_iff.mpr (row_ne_zero n)
  rw [signedCarry, direction, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  field_simp [hn]

theorem unitCarry_mixed (n : ℕ) :
    kernelToMixed n (unitCarries n) = signedCarry n • unitHeadDirection n := by
  have hn : direction n ≠ 0 := by
    intro h
    simpa [h] using direction_eval n
  apply Subtype.ext
  change patch (n + 1) - patch n = signedCarry n • (unitHeadDirection n : ThresholdHilbert)
  rw [patch, add_sub_cancel_left, unitHeadDirection_val, smul_smul, signedCarry,
    mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hn), mul_one]

theorem signedCarry_sq (n : ℕ) : (signedCarry n) ^ 2 = adjacentSnakeEnergy n := by
  rw [signedCarry_eq_div_rowNorm, div_pow, adjacentSnakeEnergy_eq_stepEnergy, stepEnergy]

private def layerValue (i : ℕ) : mixedClosure →ₗ[ℝ] ℝ where
  toFun x := headLayerIsometry x i
  map_add' x y := congrArg (fun c : ScalarL2 => c i) (headLayerIsometry.map_add x y)
  map_smul' t x := congrArg (fun c : ScalarL2 => c i) (headLayerIsometry.map_smul t x)

private theorem layerValue_unit (i n : ℕ) :
    layerValue i (unitHeadDirection n) = if i = n then 1 else 0 := by
  change headLayerIsometry (unitHeadDirection n) i = _
  rw [headLayerIsometry, HilbertBasis.repr_apply_apply, physicalHeadBasis_apply]
  by_cases h : i = n
  · subst i
    rw [if_pos rfl, real_inner_self_eq_norm_sq, unitHeadDirection_orthonormal.1, one_pow]
  · rw [if_neg h, unitHeadDirection_orthonormal.2 h]

/-- The actual image of the isometry inside unrestricted scalar sequences. -/
def squareSummableSequences : Submodule ℝ (ℕ → ℝ) := LinearMap.range (LinearMap.pi layerValue)

theorem mem_squareSummableSequences_iff (s : ℕ → ℝ) :
    s ∈ squareSummableSequences ↔ Summable (fun i => (s i) ^ 2) := by
  constructor
  · rintro ⟨m, rfl⟩
    exact (headLayer_hasSum m).summable
  · intro h
    have hs : Memℓp s 2 := memℓp_gen (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using h)
    let c : ScalarL2 := ⟨s, hs⟩
    exact ⟨headLayerIsometry.symm c, funext fun i =>
      congrArg (fun v : ScalarL2 => v i) (headLayerIsometry.apply_symm_apply c)⟩

/-- Positive partial sums match the sign of the adjacent displacement coefficients. -/
def formalCoefficients : KernelSeq →ₗ[ℝ] (ℕ → ℝ) :=
  LinearMap.pi fun i => (layerValue i).comp (partialMixed (i + 1))

private theorem coefficient_stable (a : KernelSeq) (i N : ℕ) (hi : i + 1 ≤ N) :
    layerValue i (partialMixed N a) = formalCoefficients a i := by
  induction N, hi using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    have hz := (mem_kernel_iff_headLayer_prefix_zero k _).mp (kernelToMixed_mem k (a k)) i
      (show i < k by omega)
    change layerValue i (kernelToMixed k (a k)) = 0 at hz
    rw [partialMixed_succ, map_add, hz, add_zero, ih]

private theorem formalCoefficients_exact (a : KernelSeq) :
    formalCoefficients a ∈ squareSummableSequences ↔ a ∈ LinearMap.range kernelDiff := by
  constructor
  · rintro ⟨m, hm⟩
    have hw (N : ℕ) : ((partialMixed N a - m : mixedClosure) : ThresholdHilbert) ∈ kernel N := by
      apply (mem_kernel_iff_headLayer_prefix_zero N _).mpr
      intro i hi
      change layerValue i (partialMixed N a - m) = 0
      rw [map_sub, coefficient_stable a i N (by omega)]
      exact sub_eq_zero.mpr (congrFun hm i).symm
    let w : KernelSeq := fun N => kernelOfMixed N (partialMixed N a - m) (hw N)
    refine ⟨w, funext fun n => (kernelToMixed_injective n) ?_⟩
    change (partialMixed (n + 1) a - m) - (partialMixed n a - m) = kernelToMixed n (a n)
    rw [partialMixed_succ]
    abel
  · rintro ⟨w, rfl⟩
    refine ⟨-kernelToMixed 0 (w 0), funext fun i => ?_⟩
    change layerValue i (-kernelToMixed 0 (w 0)) =
      layerValue i (partialMixed (i + 1) (kernelDiff w))
    have hz := (mem_kernel_iff_headLayer_prefix_zero (i + 1) _).mp
      (kernelToMixed_mem (i + 1) (w (i + 1))) i (Nat.lt_succ_self i)
    change layerValue i (kernelToMixed (i + 1) (w (i + 1))) = 0 at hz
    rw [partialMixed_diff, map_sub, hz, zero_sub, map_neg]

private def diagonal (s : ℕ → ℝ) : KernelSeq := fun n =>
  kernelOfMixed n (s n • unitHeadDirection n) (by
    apply (mem_kernel_iff_headLayer_prefix_zero n _).mpr
    intro i hi
    change layerValue i (s n • unitHeadDirection n) = 0
    rw [map_smul, layerValue_unit, if_neg (Nat.ne_of_lt hi), smul_zero])

private theorem partial_diagonal (s : ℕ → ℝ) (N i : ℕ) :
    layerValue i (partialMixed N (diagonal s)) = if i < N then s i else 0 := by
  induction N with
  | zero =>
    change layerValue i 0 = _
    simp
  | succ N ih =>
    rw [partialMixed_succ, map_add, ih]
    change _ + layerValue i (s N • unitHeadDirection N) = _
    rw [map_smul, layerValue_unit, smul_eq_mul]
    by_cases h : i = N
    · subst i
      simp
    · have hi : i < N + 1 ↔ i < N := by omega
      simp [h, hi]

private theorem formalCoefficients_diagonal (s : ℕ → ℝ) : formalCoefficients (diagonal s) = s := by
  funext i
  change layerValue i (partialMixed (i + 1) (diagonal s)) = s i
  rw [partial_diagonal, if_pos (Nat.lt_succ_self _)]

private def quotientCoefficients : KernelSeq →ₗ[ℝ] ((ℕ → ℝ) ⧸ squareSummableSequences) :=
  squareSummableSequences.mkQ.comp formalCoefficients

private theorem quotientCoefficients_ker :
    LinearMap.range kernelDiff = quotientCoefficients.ker := by
  ext a
  change a ∈ LinearMap.range kernelDiff ↔
    (Submodule.Quotient.mk (formalCoefficients a) : (ℕ → ℝ) ⧸ squareSummableSequences) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact (formalCoefficients_exact a).symm

/-- The algebraic first derived limit is all scalar sequences modulo their ℓ² subspace. -/
def layerCokernelEquiv : KernelCokernel ≃ₗ[ℝ] ((ℕ → ℝ) ⧸ squareSummableSequences) :=
  (Submodule.quotEquivOfEq _ _ quotientCoefficients_ker).trans
    (quotientCoefficients.quotKerEquivOfSurjective
      (squareSummableSequences.mkQ_surjective.comp fun s =>
        ⟨diagonal s, formalCoefficients_diagonal s⟩))

/-- The positive coefficient convention sends the unit boundary to the signed carry sequence. -/
theorem layerCokernel_boundary :
    layerCokernelEquiv (productSnake 1) = squareSummableSequences.mkQ signedCarry := by
  have hd : unitCarries = diagonal signedCarry :=
    funext fun n => (kernelToMixed_injective n) (unitCarry_mixed n)
  rw [productSnake_one]
  change squareSummableSequences.mkQ (formalCoefficients unitCarries) = _
  rw [hd, formalCoefficients_diagonal]

/-- A single square-summable signed displacement sequence is equivalent to RH. -/
theorem summable_signedCarry_iff_rh :
    Summable (fun n => (signedCarry n) ^ 2) ↔ RiemannHypothesis := by
  simp_rw [signedCarry_sq]
  exact productSnake_one_eq_zero_iff_summable_adjacent.symm.trans productSnake_one_eq_zero_iff_rh

theorem exists_layer_lift_iff_rh :
    (∃ m : mixedClosure, ∀ n, headLayerIsometry m n = signedCarry n) ↔ RiemannHypothesis := by
  rw [← summable_signedCarry_iff_rh, ← mem_squareSummableSequences_iff]
  exact ⟨fun ⟨m, hm⟩ => ⟨m, funext hm⟩, fun ⟨m, hm⟩ => ⟨m, congrFun hm⟩⟩

/-- Exact parity capture including the squared norm of the ambient centered boundary. -/
theorem parity_capture_with_boundary :
    ‖mixedClosure.starProjection (ramanujanPacketHilbert 2)‖ ^ 2 =
      Real.log 2 - (Real.log 2) ^ 2 * (1 + ‖CenteredMeanSnake.boundary‖ ^ 2) := by
  rw [full_mixed_capture_eq_limitEnergy, CenteredMeanSnake.boundary_norm_sq,
    normalizedScreenedTwo_norm_sq, div_eq_mul_inv]
  ring

/-- The proposed parity-capture endpoint is equivalent to finite total physical-layer energy. -/
theorem parity_capture_iff_summable_signedCarry :
    ‖mixedClosure.starProjection (ramanujanPacketHilbert 2)‖ ^ 2 =
        Real.log 2 - (Real.log 2) ^ 2 ↔ Summable (fun n => (signedCarry n) ^ 2) :=
  full_capture_saturation_iff.trans (productSnake_one_eq_zero_iff_one_mem.symm.trans
    (productSnake_one_eq_zero_iff_rh.trans summable_signedCarry_iff_rh.symm))

/-- Taking one normalized direction in each layer gives an unconditional nonzero class. -/
theorem constant_layers_ne_zero :
    layerCokernelEquiv.symm (squareSummableSequences.mkQ (fun _ : ℕ => (1 : ℝ))) ≠ 0 := by
  intro h
  have hz := congrArg layerCokernelEquiv h
  rw [LinearEquiv.apply_symm_apply, map_zero] at hz
  change (Submodule.Quotient.mk (fun _ : ℕ => (1 : ℝ)) :
    (ℕ → ℝ) ⧸ squareSummableSequences) = 0 at hz
  have hs := (mem_squareSummableSequences_iff _).mp ((Submodule.Quotient.mk_eq_zero _).mp hz)
  simp [summable_const_iff] at hs

/-- The mean squared signed coefficient up to the physical cutoff N. -/
def carryMeanSquare (N : ℕ) : ℝ := (∑ i ∈ Finset.range N, (signedCarry i) ^ 2) / (N : ℝ)

theorem carryMeanSquare_tendsto_zero : Tendsto carryMeanSquare atTop (𝓝 0) := by
  unfold carryMeanSquare
  simp_rw [signedCarry_sq, partial_adjacentSnakeEnergy]
  exact finite_snake_norm_sq_sublinear

/-- No scalar multiple of the arithmetic boundary agrees with the all-ones sequence modulo ℓ². -/
theorem not_summable_one_sub_signedCarry (t : ℝ) :
    ¬ Summable (fun i => (1 - t * signedCarry i) ^ 2) := by
  intro hs
  let A := ∑' i, (1 - t * signedCarry i) ^ 2
  have hA : Tendsto (fun n : ℕ => 2 * A / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hQ : Tendsto (fun n : ℕ => 2 * t ^ 2 * carryMeanSquare n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := 2 * t ^ 2)).mul carryMeanSquare_tendsto_zero
  have hlim : Tendsto (fun n : ℕ => 2 * A / (n : ℝ) + 2 * t ^ 2 * carryMeanSquare n)
      atTop (𝓝 0) := by simpa only [add_zero] using hA.add hQ
  obtain ⟨N, hN, hlt⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    (hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1))).exists
  have hpoint (i : ℕ) : (1 : ℝ) ≤
      2 * (1 - t * signedCarry i) ^ 2 + (2 * t ^ 2) * (signedCarry i) ^ 2 := by
    nlinarith [sq_nonneg (1 - 2 * (t * signedCarry i))]
  have hsum := Finset.sum_le_sum (s := Finset.range N) (fun i _ => hpoint i)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hpartial : (∑ i ∈ Finset.range N, (1 - t * signedCarry i) ^ 2) ≤ A :=
    hs.sum_le_tsum _ (fun i _ => sq_nonneg _)
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hbound : (N : ℝ) ≤ 2 * A + (2 * t ^ 2) * ∑ i ∈ Finset.range N, (signedCarry i) ^ 2 := by
    linarith only [hsum, hpartial]
  have hone : (1 : ℝ) ≤ 2 * A / (N : ℝ) + 2 * t ^ 2 * carryMeanSquare N := by
    calc
      (1 : ℝ) ≤ (2 * A + (2 * t ^ 2) * ∑ i ∈ Finset.range N, (signedCarry i) ^ 2) / (N : ℝ) :=
        (le_div_iff₀ hN').mpr (by simpa only [one_mul] using hbound)
      _ = _ := by unfold carryMeanSquare; ring
  exact (not_lt.mpr hone) hlt

/-- The class with one unit in each layer survives even in the legal-stage derived limit. -/
theorem constant_layers_survive :
    cokernelInclusion (layerCokernelEquiv.symm
      (squareSummableSequences.mkQ (fun _ : ℕ => (1 : ℝ)))) ≠ 0 := by
  intro h
  obtain ⟨t, ht⟩ := (productSnake_cokernelInclusion_exact _).mp h
  have hx := congrArg layerCokernelEquiv ht
  have ht' : productSnake t = t • productSnake 1 := by
    simpa only [smul_eq_mul, mul_one] using productSnake.map_smul t (1 : ℝ)
  rw [LinearEquiv.apply_symm_apply, ht', map_smul, layerCokernel_boundary] at hx
  have hz : squareSummableSequences.mkQ ((fun _ : ℕ => (1 : ℝ)) - t • signedCarry) = 0 := by
    rw [map_sub, map_smul, ← hx, sub_self]
  have hm := (Submodule.Quotient.mk_eq_zero _).mp hz
  exact not_summable_one_sub_signedCarry t ((mem_squareSummableSequences_iff _).mp hm)

end RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadBoundaryCoordinates
