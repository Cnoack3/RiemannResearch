import RiemannResearch.RH.DyadicCarryOptimization
import RiemannResearch.RH.DyadicCarryQuantitative

/-!
# Limit of a concrete finite dyadic optimization schedule

Source: the user-requested continuation of the exact dyadic-block/CRT
argument, September 2026. Removing the legal residue term and controlling
moving-target orthogonal projections computes the actual optimized limit.
The theorem proves convergence to the constant's projection defect, not
that the defect vanishes.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
open CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk

/-- The terminal residue belongs to the explicit dyadic correction dictionary. -/
theorem dyadicResidue_mem_finiteSpace (k : ℕ) :
    normalizedResidueHilbert (2^k+1) (by positivity) ∈ finiteSpace (2^k) := by
  have hp : 0 < 2^k := by positivity
  apply Submodule.subset_span
  refine ⟨⟨2^k-1, by omega⟩, ?_⟩
  change residueAtom (2^k-1) = _
  simp only [residueAtom, show 2^k-1+2 = 2^k+1 by omega]

/-- At this explicit budget, the actual inverse-Gram optimum is the finite
projection error of the reverse sampled residue. -/
theorem dyadicRepairEnergy_zero_head_eq_sampled (k : ℕ) :
    dyadicRepairEnergy k 0 (2^k) =
      ‖dyadicSampledResidue k -
        (finiteSpace (2^k)).starProjection (dyadicSampledResidue k)‖^2 := by
  have hJ : jointHeadHilbert (dyadicCarryBlockSequence k) 0 = 0 := by
    simp [jointHeadHilbert]
  rw [dyadicRepairEnergy_eq_norm, dyadicRepairedBlock, hJ, zero_add,
    dyadicJointResidual, hJ, sub_zero, headCorrection_zero_eq_projection]
  have hg := Submodule.starProjection_eq_self_iff.mpr (dyadicResidue_mem_finiteSpace k)
  have he : dyadicCarryBlock k (2^k+1) (by positivity) -
      (finiteSpace (2^k)).starProjection (dyadicCarryBlock k (2^k+1) (by positivity)) =
        -(dyadicSampledResidue k -
          (finiteSpace (2^k)).starProjection (dyadicSampledResidue k)) := by
    unfold dyadicCarryBlock dyadicSampledResidue
    rw [map_sub, map_smul, hg]
    abel
  rw [he, norm_neg]

/-- Finite projections of the varying sampled targets converge to the actual
closed-space projection. The proof uses the uniform contraction bound. -/
theorem dyadicSampled_finiteProjection_tendsto :
    Tendsto (fun k => (finiteSpace (2^k)).starProjection (dyadicSampledResidue k))
      atTop (𝓝 limitProjection) := by
  have hk : Tendsto (fun k : ℕ => 2^k) atTop atTop :=
    tendsto_atTop_mono (fun k => (Nat.lt_two_pow_self (n := k)).le) tendsto_id
  have hy : Tendsto (fun k => dyadicSampledResidue k - hilbertOne)
      atTop (𝓝 (0 : ThresholdHilbert)) := by
    simpa using dyadicSampledResidue_tendsto_one.sub_const hilbertOne
  have hp : Tendsto (fun k => (finiteSpace (2^k)).starProjection
      (dyadicSampledResidue k - hilbertOne)) atTop (𝓝 (0 : ThresholdHilbert)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    apply squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
      (by simpa using hy.norm)
    exact Submodule.norm_starProjection_apply_le _ _
  have hfixed := projection_tendsto.comp hk
  have hsum := hfixed.add hp
  have he : (fun k => projection (2^k) + (finiteSpace (2^k)).starProjection
      (dyadicSampledResidue k - hilbertOne)) =
        (fun k => (finiteSpace (2^k)).starProjection (dyadicSampledResidue k)) := by
    funext k
    rw [map_sub]
    unfold projection
    abel
  simpa only [Function.comp_def, add_zero, he] using hsum

/-- Unconditional convergence of the constructed finite Schur energies at the
explicit schedule N=0, L=2^k. The limit is not asserted to be zero. -/
theorem dyadicRepairEnergy_zero_head_tendsto :
    Tendsto (fun k => dyadicRepairEnergy k 0 (2^k)) atTop (𝓝 limitEnergy) := by
  have ht := (dyadicSampledResidue_tendsto_one.sub
    dyadicSampled_finiteProjection_tendsto).norm.pow 2
  simpa only [dyadicRepairEnergy_zero_head_eq_sampled, limitEnergy, limitingError,
    limitProjection] using ht

/-- For this completely specified schedule, vanishing is exactly the original
constant-membership question, rather than an extra consequence of exhaustion. -/
theorem dyadicRepairEnergy_zero_head_tendsto_zero_iff :
    Tendsto (fun k => dyadicRepairEnergy k 0 (2^k)) atTop (𝓝 0) ↔
      hilbertOne ∈ closedSpace := by
  constructor
  · intro h
    exact limitEnergy_zero_iff_mem.mp
      (tendsto_nhds_unique dyadicRepairEnergy_zero_head_tendsto h)
  · intro h
    simpa only [limitEnergy_zero_iff_mem.mpr h] using dyadicRepairEnergy_zero_head_tendsto


/-! Source: the user's request to complete the dyadic proof, 2026-09-20.
These exact finite comparisons retain the covariance and quantify a change
of target. They do not supply vanishing of the original projection error. -/

/-- The sparse-multiple error remaining after the actual finite projection. -/
def dyadicFiniteSparseResidual (k : ℕ) : ThresholdHilbert :=
  dyadicMultipleIndicator k -
    (finiteSpace (2 ^ k)).starProjection (dyadicMultipleIndicator k)

theorem dyadicFiniteSparseResidual_norm_le (k : ℕ) :
    ‖dyadicFiniteSparseResidual k‖ ≤
      Real.sqrt (2 / ((2 ^ k + 1 : ℕ) : ℝ) ^ 2) := by
  have hp : ‖dyadicFiniteSparseResidual k‖ ≤ ‖dyadicMultipleIndicator k‖ := by
    unfold dyadicFiniteSparseResidual
    rw [← Submodule.starProjection_orthogonal_val]
    exact (finiteSpace (2 ^ k))ᗮ.norm_starProjection_apply_le _
  exact hp.trans ((Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    (dyadicMultipleIndicator_norm_sq_le k))

/-- Exact finite optimizer after the legal residue is removed. -/
theorem dyadicRepairEnergy_zero_head_eq_sparse (k : ℕ) :
    dyadicRepairEnergy k 0 (2 ^ k) =
      ‖(hilbertOne - projection (2 ^ k)) - dyadicFiniteSparseResidual k‖ ^ 2 := by
  rw [dyadicRepairEnergy_zero_head_eq_sampled]
  have hg := Submodule.starProjection_eq_self_iff.mpr (dyadicResidue_mem_finiteSpace k)
  congr 2
  dsimp [dyadicFiniteSparseResidual, dyadicMultipleIndicator, projection]
  rw [map_sub, map_add, hg]
  abel

/-- Full signed energy identity: the covariance term is retained. -/
theorem dyadicRepairEnergy_zero_head_signed (k : ℕ) :
    dyadicRepairEnergy k 0 (2 ^ k) = energy (2 ^ k) -
      2 * inner ℝ (hilbertOne - projection (2 ^ k)) (dyadicFiniteSparseResidual k) +
      ‖dyadicFiniteSparseResidual k‖ ^ 2 := by
  rw [dyadicRepairEnergy_zero_head_eq_sparse, norm_sub_sq_real]
  rfl

/-- This compares two finite optima; it does not assert either tends to zero. -/
theorem dyadicRepairEnergy_zero_head_sqrt_error_le (k : ℕ) :
    |Real.sqrt (dyadicRepairEnergy k 0 (2 ^ k)) -
      Real.sqrt (energy (2 ^ k))| ≤
      Real.sqrt (2 / ((2 ^ k + 1 : ℕ) : ℝ) ^ 2) := by
  have he : energy (2 ^ k) = ‖hilbertOne - projection (2 ^ k)‖ ^ 2 := rfl
  rw [dyadicRepairEnergy_zero_head_eq_sparse, he,
    Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_sq_eq_abs, abs_norm]
  have h := abs_norm_sub_norm_le
    ((hilbertOne - projection (2 ^ k)) - dyadicFiniteSparseResidual k)
    (hilbertOne - projection (2 ^ k))
  have hv : (hilbertOne - projection (2 ^ k) - dyadicFiniteSparseResidual k) -
      (hilbertOne - projection (2 ^ k)) = -dyadicFiniteSparseResidual k := by abel
  rw [hv, norm_neg] at h
  exact h.trans (dyadicFiniteSparseResidual_norm_le k)

end RiemannResearch.RH.Pareto
