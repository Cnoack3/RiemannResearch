import RiemannResearch.RH.PhysicalHeadStageAlgebraComparison
import Mathlib.Algebra.Module.SnakeLemma
import Mathlib.Analysis.Normed.Group.Quotient

/-!
# The relative snake of the physical-head stage algebras

Compare the underlying additive mean sequences by inclusion on the mixed kernels,
centering at the lower unit on the middle terms, and zero on scalars. The connecting
class is the product defect evaluated on the upper unit. Its quotient norm retains
the orthogonal step energy.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadStageAlgebra
open CoefficientStabilization CenteredMeanSnake.PhysicalHeadSections AffineHeadTower

/-- Left vertical arrow in the comparison of mean sequences. -/
def kernelInclusion {N K : ℕ} (h : N ≤ K) : (stageMean K).ker →ₗ[ℝ] (stageMean N).ker :=
  ((stageInclusion h).comp (stageMean K).ker.subtype).codRestrict _ fun z => z.property

/-- Middle vertical arrow, centered using the lower unit. -/
def relativeCenter {N K : ℕ} (h : N ≤ K) : headCompatible K →ₗ[ℝ] headCompatible N :=
  (stageMean N).ker.subtype.comp ((mixedCoordinate N).toLinearMap.comp (stageInclusion h))

private theorem relative_left_square {N K : ℕ} (h : N ≤ K) :
    (stageMean N).ker.subtype.comp (kernelInclusion h) =
      (relativeCenter h).comp (stageMean K).ker.subtype := by
  apply LinearMap.ext
  intro z
  change stageInclusion h z.val = (mixedCoordinate N (stageInclusion h z.val)).val
  rw [mixedCoordinate_val, stageInclusion_mean, show stageMean K z.val = 0 from z.property,
    zero_smul, sub_zero]

private theorem relative_right_square {N K : ℕ} (h : N ≤ K) :
    (stageMean N).toLinearMap.comp (relativeCenter h) =
      (0 : ℝ →ₗ[ℝ] ℝ).comp (stageMean K).toLinearMap := by
  apply LinearMap.ext
  intro x
  exact (mixedCoordinate N (stageInclusion h x)).property

/-- The deeper mean kernel viewed inside the lower mean kernel. -/
abbrev deeperKernel {N K : ℕ} (h : N ≤ K) := LinearMap.range (kernelInclusion h)

private theorem relative_cokernel_exact {N K : ℕ} (h : N ≤ K) :
    Function.Exact (kernelInclusion h) (deeperKernel h).mkQ := by
  intro z
  exact Submodule.Quotient.mk_eq_zero _

/-- Mathlib's connecting morphism for the two physical stage rows. -/
def relativeSnake {N K : ℕ} (h : N ≤ K) : ℝ →ₗ[ℝ] (stageMean N).ker ⧸ deeperKernel h :=
  SnakeLemma.δ (kernelInclusion h) (relativeCenter h) (0 : ℝ →ₗ[ℝ] ℝ)
    (stageMean K).ker.subtype (stageMean K).toLinearMap (LinearMap.exact_subtype_ker_map _)
    (stageMean N).ker.subtype (stageMean N).toLinearMap (LinearMap.exact_subtype_ker_map _)
    (relative_left_square h) (relative_right_square h)
    (fun t : ℝ => t • stageUnit K) (funext fun t => by
      change stageMean K (t • stageUnit K) = t
      rw [map_smul, stageUnit_mean, smul_eq_mul, mul_one])
    (mixedCoordinate N) (funext fun z => mixedCoordinate_kernel N z)
    LinearMap.id ((LinearMap.exact_zero_iff_surjective _ _).mpr Function.surjective_id)
    (deeperKernel h).mkQ (relative_cokernel_exact h)

/-- The orthogonal representative before passing to the cokernel. -/
def unitCarry {N K : ℕ} (h : N ≤ K) : (stageMean N).ker :=
  ⟨displacement h, displacement_mean h⟩

theorem relativeSnake_one {N K : ℕ} (h : N ≤ K) :
    relativeSnake h 1 = (deeperKernel h).mkQ (unitCarry h) := by
  change (deeperKernel h).mkQ (mixedCoordinate N (relativeCenter h ((1 : ℝ) • stageUnit K))) = _
  rw [one_smul]
  change (deeperKernel h).mkQ
    (mixedCoordinate N (mixedCoordinate N (stageInclusion h (stageUnit K))).val) = _
  rw [mixedCoordinate_kernel]
  apply congrArg (deeperKernel h).mkQ
  apply Subtype.ext
  change (mixedCoordinate N (stageInclusion h (stageUnit K))).val = displacement h
  rw [mixedCoordinate_val, stageInclusion_mean, stageUnit_mean, one_smul]
  rfl

theorem relativeSnake_apply {N K : ℕ} (h : N ≤ K) (a : ℝ) :
    relativeSnake h a = a • (deeperKernel h).mkQ (unitCarry h) := by
  rw [← relativeSnake_one h, ← map_smul, smul_eq_mul, mul_one]

/-- Exact identification with the signed multiplicative defect of the ordinary inclusion. -/
theorem relativeSnake_one_eq_unit_product_defect {N K : ℕ} (h : N ≤ K) :
    relativeSnake h 1 = (deeperKernel h).mkQ
      ⟨stageInclusion h (stageUnit K) * stageInclusion h (stageUnit K) -
        stageInclusion h (stageUnit K * stageUnit K), by
          rw [inclusion_unit_defect]
          exact displacement_mean h⟩ := by
  rw [relativeSnake_one]
  apply congrArg (deeperKernel h).mkQ
  exact Subtype.ext (inclusion_unit_defect h).symm

private theorem kernel_vector_mem_affine_kernel {K : ℕ} (y : (stageMean K).ker) :
    (y.val.val : ThresholdHilbert) ∈ kernel K := by
  obtain ⟨hm, hh⟩ := (mem_stageMean_ker_iff K y.val).mp y.property
  apply (mem_kernel K).mpr
  refine ⟨hm, fun i hi => ?_⟩
  have he := congrArg (fun v : ThresholdHilbert => hilbertSequenceLinear v (i + 1)) hh
  change hilbertSequence (compactHead K (y.val.val : ThresholdHilbert)) (i + 1) =
    hilbertSequenceLinear 0 (i + 1) at he
  rw [compactHead_sequence, if_pos (show i + 1 ≤ K by omega), map_zero] at he
  simpa only [physicalEvaluationCLM_apply, Pi.zero_apply] using he

theorem unitCarry_orthogonal {N K : ℕ} (h : N ≤ K) :
    unitCarry h ∈ (deeperKernel h)ᗮ := by
  rintro z ⟨y, rfl⟩
  exact displacement_orthogonal_deeper h _ (kernel_vector_mem_affine_kernel y)

/-- No part of the two-stage orthogonal energy is lost in the quotient. -/
theorem relativeSnake_one_norm_sq {N K : ℕ} (h : N ≤ K) :
    ‖relativeSnake h 1‖ ^ 2 = ‖patch K‖ ^ 2 - ‖patch N‖ ^ 2 := by
  rw [relativeSnake_one]
  have he : ‖(deeperKernel h).mkQ (unitCarry h)‖ = ‖unitCarry h‖ := by
    calc
      ‖(deeperKernel h).mkQ (unitCarry h)‖ =
          Metric.infDist (unitCarry h) (deeperKernel h : Set (stageMean N).ker) :=
        QuotientAddGroup.norm_mk (S := (deeperKernel h).toAddSubgroup) (unitCarry h)
      _ = ‖unitCarry h‖ := by
        apply le_antisymm
        · simpa only [dist_zero_right] using
            (Metric.infDist_le_dist_of_mem (x := unitCarry h) (deeperKernel h).zero_mem)
        · apply (Metric.le_infDist ⟨0, (deeperKernel h).zero_mem⟩).mpr
          intro z hz
          rw [dist_eq_norm]
          apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
          rw [norm_sub_sq_real, real_inner_comm, unitCarry_orthogonal h z hz]
          linarith [sq_nonneg ‖z‖]
  rw [he]
  exact displacement_norm_sq h

end RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadStageAlgebra
