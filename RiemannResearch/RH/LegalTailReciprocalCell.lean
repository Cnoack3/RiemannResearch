/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.LegalTailNymanMesh
import RiemannResearch.RH.LegalTailResidual
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Reciprocal-cell transport in real L²

Source: Christian Noack, legal tail-capacity handoff, November 2026.
All scales take values in one real Hilbert space on the unit interval.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open FiniteHeadRepair RiemannResearch.RH.Burnol.ContinuousNyman

abbrev RealMeshHilbert := Lp ℝ 2 intervalMeasure
abbrev TailHeadSpace (K : ℕ) := (headMap K).ker

def reciprocalCellFunction (K : ℕ) (f : ThresholdHilbert) (t : ℝ) : ℝ :=
  hilbertSequence f ⌊((K+1 : ℕ) : ℝ) / t⌋₊

private theorem cell_measurable (K : ℕ) (f : ThresholdHilbert) :
    Measurable (reciprocalCellFunction K f) :=
  (measurable_of_countable (f := hilbertSequence f)).comp (by fun_prop)

private theorem cell_square_integral (K : ℕ) (f : TailHeadSpace K) :
    (∫⁻ t, ENNReal.ofReal (reciprocalCellFunction K f t ^ 2) ∂intervalMeasure) =
      ENNReal.ofReal (((K+1 : ℕ) : ℝ) * ‖f‖ ^ 2) :=
  scaled_reciprocalFloor_norm_sq _ (Nat.succ_pos K) f (fun j hj =>
    legalHeadKernel_sequence_zero (k := j) f.property (Nat.le_of_lt_succ hj))

private theorem cell_memLp (K : ℕ) (f : TailHeadSpace K) :
    MemLp (reciprocalCellFunction K f) 2 intervalMeasure := by
  have h := cell_measurable K f
  apply (memLp_two_iff_integrable_sq h.aestronglyMeasurable).mpr
  apply (lintegral_ofReal_ne_top_iff_integrable ((h.pow_const 2).aestronglyMeasurable)
    (Eventually.of_forall (fun t => sq_nonneg (reciprocalCellFunction K f t)))).mp
  rw [cell_square_integral]
  exact ENNReal.ofReal_ne_top

def reciprocalCellMap (K : ℕ) : TailHeadSpace K →ₗ[ℝ] RealMeshHilbert where
  toFun f := (cell_memLp K f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(cell_memLp K (f+g)).coeFn_toLp, (cell_memLp K f).coeFn_toLp,
      (cell_memLp K g).coeFn_toLp, Lp.coeFn_add ((cell_memLp K f).toLp _)
        ((cell_memLp K g).toLp _)] with t h h₁ h₂ h₃
    rw [h, h₃, Pi.add_apply, h₁, h₂]
    simp only [reciprocalCellFunction, Submodule.coe_add, hilbertSequence_add, Pi.add_apply]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(cell_memLp K (c • f)).coeFn_toLp, (cell_memLp K f).coeFn_toLp,
      Lp.coeFn_smul c ((cell_memLp K f).toLp _)] with t h h₁ h₂
    change _ = ((c • (cell_memLp K f).toLp _ : RealMeshHilbert) : ℝ → ℝ) t
    rw [h, h₂, Pi.smul_apply, h₁]
    simp only [reciprocalCellFunction, Submodule.coe_smul, hilbertSequence_smul, Pi.smul_apply]

theorem reciprocalCellMap_ae (K : ℕ) (f : TailHeadSpace K) :
    (reciprocalCellMap K f : ℝ → ℝ) =ᵐ[intervalMeasure] reciprocalCellFunction K f :=
  (cell_memLp K f).coeFn_toLp

theorem reciprocalCellMap_norm_sq (K : ℕ) (f : TailHeadSpace K) :
    ‖reciprocalCellMap K f‖ ^ 2 = ((K+1 : ℕ) : ℝ) * ‖f‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    _ = ∫ t, reciprocalCellFunction K f t ^ 2 ∂intervalMeasure := by
      apply integral_congr_ae
      filter_upwards [reciprocalCellMap_ae K f] with t ht
      simp only [ht, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    _ = _ := by
      rw [integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall (fun t => sq_nonneg (reciprocalCellFunction K f t)))
        (((cell_measurable K f).pow_const 2).aestronglyMeasurable), cell_square_integral,
        ENNReal.toReal_ofReal (by positivity)]

theorem reciprocalCellMap_norm (K : ℕ) (f : TailHeadSpace K) :
    ‖reciprocalCellMap K f‖ = Real.sqrt (K+1 : ℕ) * ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [reciprocalCellMap_norm_sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

/-- The normalized map on the entire ambient zero-head subspace. -/
def reciprocalCellIsometry (K : ℕ) : TailHeadSpace K →ₗᵢ[ℝ] RealMeshHilbert where
  toLinearMap := (Real.sqrt (K+1 : ℕ))⁻¹ • reciprocalCellMap K
  norm_map' f := by
    change ‖(Real.sqrt (K+1 : ℕ))⁻¹ • reciprocalCellMap K f‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), reciprocalCellMap_norm,
      ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

def legalCellMap (K : ℕ) : legalHeadKernel K →ₗ[ℝ] RealMeshHilbert :=
  (reciprocalCellMap K).comp
    (Submodule.inclusion (show legalHeadKernel K ≤ TailHeadSpace K from inf_le_right))

theorem legalCellMap_norm_sq (K : ℕ) (v : legalHeadKernel K) :
    ‖legalCellMap K v‖^2 = ((K : ℝ)+1) * ‖v.val‖^2 := by
  change ‖reciprocalCellMap K ⟨v.val,v.property.2⟩‖^2 = _
  rw [reciprocalCellMap_norm_sq,Nat.cast_add,Nat.cast_one]
  rfl

def legalCellIsometry (K : ℕ) : legalHeadKernel K →ₗᵢ[ℝ] RealMeshHilbert where
  toLinearMap := (Real.sqrt (K+1 : ℕ))⁻¹ • legalCellMap K
  norm_map' v := (reciprocalCellIsometry K).norm_map ⟨v.val,v.property.2⟩

theorem legalCellMap_range_eq_isometry (K : ℕ) :
    (legalCellMap K).range = (legalCellIsometry K).toLinearMap.range := by
  ext y
  constructor
  · rintro ⟨v,rfl⟩
    refine ⟨Real.sqrt (K+1 : ℕ) • v, ?_⟩
    change (Real.sqrt (K+1 : ℕ))⁻¹ • legalCellMap K (_ • v) = _
    rw [map_smul, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  · rintro ⟨v,rfl⟩
    exact ⟨(Real.sqrt (K+1 : ℕ))⁻¹ • v, (legalCellMap K).map_smul _ _⟩

theorem legalCellMap_range_closed (K : ℕ) :
    IsClosed ((legalCellMap K).range : Set RealMeshHilbert) := by
  rw [legalCellMap_range_eq_isometry]
  exact (legalCellIsometry K).isometry.isClosedEmbedding.isClosed_range

def realMeshUnit : RealMeshHilbert := (memLp_const (1 : ℝ)).toLp (fun _ : ℝ => (1:ℝ))

theorem paretoTail_mem_headKer (K : ℕ) : paretoTail K ∈ TailHeadSpace K := by
  change headMap K _ = 0
  ext i
  rw [headMap_apply, ← hilbertGibbsPhysical_eq, paretoTail_physical, if_pos i.isLt]
  rfl

theorem reciprocalCellMap_tail (K : ℕ) :
    reciprocalCellMap K ⟨paretoTail K, paretoTail_mem_headKer K⟩ = realMeshUnit := by
  apply Lp.ext
  filter_upwards [reciprocalCellMap_ae K ⟨paretoTail K, paretoTail_mem_headKer K⟩,
    (memLp_const (μ := intervalMeasure) (p := 2) (1 : ℝ)).coeFn_toLp,
    ae_restrict_mem (μ := volume) measurableSet_Ioc] with t hv h1 ht
  change _ = (memLp_const (μ := intervalMeasure) (p := 2) (1 : ℝ)).toLp _ t
  rw [hv, h1]
  have hfloor : K+1 ≤ ⌊((K+1 : ℕ) : ℝ)/t⌋₊ := by
    apply Nat.le_floor
    exact (le_div_iff₀ ht.1).mpr (by nlinarith [mul_nonneg (Nat.cast_nonneg (K+1)) (sub_nonneg.mpr ht.2)])
  simp only [reciprocalCellFunction, paretoTail_eq_scaled_dilation, hilbertTail_sequence, if_pos hfloor]

/-- The actual optimal fit, in the same real L² for every cutoff. -/
def commonTailOptimizer (K : ℕ) : RealMeshHilbert :=
  legalCellMap K ⟨legalTailMeanVector K, legalTailMeanVector_mem K⟩

theorem commonTailOptimizer_norm_sq (K : ℕ) :
    ‖commonTailOptimizer K‖^2 = normalizedLegalTailMeanCapacity K := by
  let v : TailHeadSpace K := ⟨legalTailMeanVector K,(legalTailMeanVector_mem K).2⟩
  change ‖reciprocalCellMap K v‖^2 = ((K : ℝ)+1) * ‖legalTailMeanVector K‖^2
  rw [reciprocalCellMap_norm_sq]
  simp [v]

end RiemannResearch.RH.Pareto.PrimePowerSchur
