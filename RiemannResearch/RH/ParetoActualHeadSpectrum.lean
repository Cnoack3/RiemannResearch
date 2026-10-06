/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoCompactHead
import RiemannResearch.Analysis.FiniteHeadTailSpectralRealization
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Abel

/-!
# Literal complete Pareto head spectrum

The finite head lift is CONSTRUCTED from the actual physical cutoff and the
entire legal stage. Head injectivity follows from the already proved compact
coefficient duals. Neither a new injectivity premise nor a spectrum premise
is introduced. This constructs the finite spectrum; no arithmetic source-moment estimate is asserted.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

open RiemannResearch.Analysis

theorem compactHead_preserves_coefficient (N m : ℕ) (hm : 0 < m) (hmN : m ≤ N)
    (x : ThresholdHilbert) :
    coefficientCLM m (compactHead N x) = coefficientCLM m x := by
  simp only [coefficientCLM, neg_apply]
  congr 1
  rw [← mobiusRieszHilbert_inner m (compactHead N x),
    ← mobiusRieszHilbert_inner m x]
  rw [real_inner_comm (compactHead N x) (mobiusRieszHilbert m),
    compactHead_observation N x (mobiusRieszHilbert m)
      (compactHead_mobiusRiesz N m hm hmN)]
  exact (real_inner_comm x (mobiusRieszHilbert m)).symm

/-- The actual physical head restriction of the entire stage. -/
def stageHeadRestriction (n N : ℕ) : finiteSpace n →ₗ[ℝ] ThresholdHilbert :=
  (compactHeadLinear N).comp (finiteSpace n).subtype

theorem stageHeadRestriction_injective (n N : ℕ) (hN : n+1 ≤ N) :
    Function.Injective (stageHeadRestriction n N) := by
  intro x y hxy
  have hc (i : Fin n) :
      coefficientCLM (i.val+2) (x : ThresholdHilbert) =
        coefficientCLM (i.val+2) (y : ThresholdHilbert) := by
    have hiN : i.val+2 ≤ N := by omega
    have hx := compactHead_preserves_coefficient N (i.val+2) (by omega) hiN
      (x : ThresholdHilbert)
    have hy := compactHead_preserves_coefficient N (i.val+2) (by omega) hiN
      (y : ThresholdHilbert)
    exact hx.symm.trans ((congrArg (coefficientCLM (i.val+2)) hxy).trans hy)
  obtain ⟨a, ha⟩ := finiteSpace_expansion n x x.property
  obtain ⟨b, hb⟩ := finiteSpace_expansion n y y.property
  have hab : a = b := by
    funext i
    have h := hc i
    rw [ha, hb, coefficient_finite_sum, coefficient_finite_sum] at h
    exact h
  apply Subtype.ext
  rw [ha, hb, hab]

/-- The literal finite head image Q_N V_n, not an abstract supplied space. -/
def stageHeadSpace (n N : ℕ) : Submodule ℝ ThresholdHilbert :=
  (stageHeadRestriction n N).range

instance stageHeadSpace_finiteDimensional (n N : ℕ) :
    FiniteDimensional ℝ (stageHeadSpace n N) := by
  apply FiniteDimensional.of_surjective (stageHeadRestriction n N).rangeRestrict
  rintro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩

def stageHeadEquiv (n N : ℕ) (hN : n+1 ≤ N) :
    finiteSpace n ≃ₗ[ℝ] stageHeadSpace n N :=
  LinearEquiv.ofInjective (stageHeadRestriction n N)
    (stageHeadRestriction_injective n N hN)

/-- Inverse physical head restriction, as a map into the full Hilbert space. -/
def stageHeadLift (n N : ℕ) (hN : n+1 ≤ N) :
    stageHeadSpace n N →L[ℝ] ThresholdHilbert :=
  ((finiteSpace n).subtype.comp (stageHeadEquiv n N hN).symm.toLinearMap).toContinuousLinearMap

def stageHeadInclusion (n N : ℕ) : stageHeadSpace n N →ₗᵢ[ℝ] ThresholdHilbert where
  toLinearMap := (stageHeadSpace n N).subtype
  norm_map' _ := rfl

/-- The whole infinite physical tail of the actual inverse head lift. -/
def stageTailLift (n N : ℕ) (hN : n+1 ≤ N) :
    stageHeadSpace n N →L[ℝ] ThresholdHilbert :=
  stageHeadLift n N hN - (stageHeadInclusion n N).toContinuousLinearMap

theorem stageHeadLift_mem (n N : ℕ) (hN : n+1 ≤ N) (x : stageHeadSpace n N) :
    stageHeadLift n N hN x ∈ finiteSpace n :=
  ((stageHeadEquiv n N hN).symm x).property

theorem compactHead_stageHeadLift (n N : ℕ) (hN : n+1 ≤ N)
    (x : stageHeadSpace n N) :
    compactHead N (stageHeadLift n N hN x) = (x : ThresholdHilbert) := by
  have hx := (stageHeadEquiv n N hN).apply_symm_apply x
  exact congrArg (fun z : stageHeadSpace n N => (z : ThresholdHilbert)) hx

theorem compactHead_stageHeadSpace (n N : ℕ) (x : stageHeadSpace n N) :
    compactHead N (x : ThresholdHilbert) = (x : ThresholdHilbert) := by
  obtain ⟨z, hz⟩ := x.property
  rw [← hz]
  exact compactHead_idempotent N z

theorem stageTailLift_eq_physicalTail (n N : ℕ) (hN : n+1 ≤ N)
    (x : stageHeadSpace n N) :
    stageTailLift n N hN x =
      stageHeadLift n N hN x - compactHead N (stageHeadLift n N hN x) := by
  rw [compactHead_stageHeadLift]
  rfl

theorem compactHead_stageTailLift (n N : ℕ) (hN : n+1 ≤ N)
    (x : stageHeadSpace n N) : compactHead N (stageTailLift n N hN x) = 0 := by
  rw [stageTailLift_eq_physicalTail, compactHead_sub, compactHead_idempotent]
  exact sub_self _

theorem stage_head_tail_orthogonal (n N : ℕ) (hN : n+1 ≤ N)
    (x y : stageHeadSpace n N) :
    inner ℝ (stageHeadInclusion n N x) (stageTailLift n N hN y) = 0 := by
  rw [stageTailLift_eq_physicalTail, real_inner_comm]
  change inner ℝ (stageHeadLift n N hN y - compactHead N (stageHeadLift n N hN y))
    (x : ThresholdHilbert) = 0
  rw [← compactHead_stageHeadSpace n N x]
  exact compactHead_tail_inner_head N (stageHeadLift n N hN y) x

theorem stage_target_tail_orthogonal (n N : ℕ) (hN : n+1 ≤ N)
    (v : ThresholdHilbert) (hv : compactHead N v = v) (x : stageHeadSpace n N) :
    inner ℝ v (stageTailLift n N hN x) = 0 := by
  rw [stageTailLift_eq_physicalTail, real_inner_comm, ← hv]
  exact compactHead_tail_inner_head N (stageHeadLift n N hN x) v

abbrev stageEigenBasis (n N : ℕ) (hN : n+1 ≤ N) :=
  FiniteHeadTailSpectralRealization.eigenBasis (stageTailLift n N hN)

abbrev stageEigenvalue (n N : ℕ) (hN : n+1 ≤ N) :=
  FiniteHeadTailSpectralRealization.eigenvalue (stageTailLift n N hN)

def stageSpectralHead (n N : ℕ) (hN : n+1 ≤ N) :=
  fun i => stageHeadInclusion n N (stageEigenBasis n N hN i)

def stageSpectralTail (n N : ℕ) (hN : n+1 ≤ N) :=
  fun i => stageTailLift n N hN (stageEigenBasis n N hN i)

theorem stageSpectralFrame_eq_lift (n N : ℕ) (hN : n+1 ≤ N)
    (i : Fin (Module.finrank ℝ (stageHeadSpace n N))) :
    FiniteHeadTailSpectralRealization.frame (stageSpectralHead n N hN) (stageSpectralTail n N hN) i =
      stageHeadLift n N hN (stageEigenBasis n N hN i) := by
  change (stageEigenBasis n N hN i : ThresholdHilbert) +
    (stageHeadLift n N hN (stageEigenBasis n N hN i) -
      (stageEigenBasis n N hN i : ThresholdHilbert)) = _
  abel

/-- The entire conductor stage is recovered from the constructed source
eigenvectors. No conductor column or composite interaction is removed. -/
theorem stageSpectralFrame_span (n N : ℕ) (hN : n+1 ≤ N) :
    FiniteHilbertGram.synthesisSpan (FiniteHeadTailSpectralRealization.frame (stageSpectralHead n N hN)
      (stageSpectralTail n N hN)) = finiteSpace n := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    rw [stageSpectralFrame_eq_lift]
    exact stageHeadLift_mem n N hN _
  · intro z hz
    let x : finiteSpace n := ⟨z, hz⟩
    let y := stageHeadEquiv n N hN x
    let b := stageEigenBasis n N hN
    rw [FiniteHilbertGram.synthesisSpan, ← Fintype.range_linearCombination]
    refine ⟨fun i => b.repr y i, ?_⟩
    rw [Fintype.linearCombination_apply]
    simp only [stageSpectralFrame_eq_lift]
    simp only [← map_smul]
    rw [← map_sum, b.sum_repr]
    change ((stageHeadEquiv n N hN).symm y : ThresholdHilbert) = z
    simp [y, x]

/-- The literal full-spectrum fit equals the actual complete stage projection. -/
theorem stageSpectralFit_eq_projection (n N : ℕ) (hN : n+1 ≤ N)
    (v : ThresholdHilbert) (hv : compactHead N v = v) :
    FiniteHeadTailSpectralRealization.fullFit (stageSpectralHead n N hN) (stageSpectralTail n N hN)
      (stageEigenvalue n N hN) v = (finiteSpace n).starProjection v := by
  have h := FiniteHeadTailSpectralRealization.spectralFrame_fullFit_eq_projection
    (stageHeadInclusion n N) (stageTailLift n N hN) v
    (stage_head_tail_orthogonal n N hN) (stage_target_tail_orthogonal n N hN v hv)
  have h' : FiniteHeadTailSpectralRealization.fullFit (stageSpectralHead n N hN)
      (stageSpectralTail n N hN) (stageEigenvalue n N hN) v =
      (FiniteHilbertGram.synthesisSpan (FiniteHeadTailSpectralRealization.frame
        (stageSpectralHead n N hN) (stageSpectralTail n N hN))).starProjection v := h
  simpa only [stageSpectralFrame_span n N hN] using h'

theorem stageSpectralHead_span (n N : ℕ) (hN : n+1 ≤ N) :
    FiniteHilbertGram.synthesisSpan (stageSpectralHead n N hN) =
      stageHeadSpace n N := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    exact (stageEigenBasis n N hN i).property
  · intro z hz
    let y : stageHeadSpace n N := ⟨z, hz⟩
    let b := stageEigenBasis n N hN
    rw [FiniteHilbertGram.synthesisSpan, ← Fintype.range_linearCombination]
    refine ⟨fun i => b.repr y i, ?_⟩
    rw [Fintype.linearCombination_apply]
    have heq := congrArg (fun x : stageHeadSpace n N => (x : ThresholdHilbert))
      (b.sum_repr y)
    change (∑ i, b.repr y i • (b i : ThresholdHilbert)) = z
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using heq

theorem stageSpectralHeadFit_eq_projection (n N : ℕ) (hN : n+1 ≤ N)
    (v : ThresholdHilbert) :
    FiniteHeadTailSpectralRealization.headFit (stageSpectralHead n N hN) v =
      (stageHeadSpace n N).starProjection v := by
  have h := FiniteHilbertGram.projection_eq_orthonormal_sum
    (FiniteHeadTailSpectralRealization.head_basis_orthonormal
      (stageHeadInclusion n N) (stageTailLift n N hN)) v
  have h' : (FiniteHilbertGram.synthesisSpan (stageSpectralHead n N hN)).starProjection v =
      FiniteHeadTailSpectralRealization.headFit (stageSpectralHead n N hN) v := h
  simpa only [stageSpectralHead_span n N hN] using h'.symm

theorem compactHead_stageSpectralFit (n N : ℕ) (hN : n+1 ≤ N)
    (v : ThresholdHilbert) :
    compactHead N (FiniteHeadTailSpectralRealization.fullFit
      (stageSpectralHead n N hN) (stageSpectralTail n N hN)
      (stageEigenvalue n N hN) v) =
    FiniteHeadTailSpectralRealization.fittedHead (stageSpectralHead n N hN)
      (stageEigenvalue n N hN) v := by
  unfold FiniteHeadTailSpectralRealization.fullFit
    FiniteHeadTailSpectralRealization.fittedHead
    FiniteHeadTailSpectralRealization.synthesize
  change (compactHeadLinear N) (∑ i, _ • _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  change _ • compactHead N (FiniteHeadTailSpectralRealization.frame
    (stageSpectralHead n N hN) (stageSpectralTail n N hN) i) = _
  rw [stageSpectralFrame_eq_lift, compactHead_stageHeadLift]
  rfl

/-- S is literally the full infinite physical-tail square of the actual
complete-stage optimizer, rather than a scalar quantity assumed equal to it. -/
theorem actualOptimizerTail_eq_spectral (n N : ℕ) (hN : n+1 ≤ N)
    (v : ThresholdHilbert) (hv : compactHead N v = v) :
    ‖(finiteSpace n).starProjection v -
      compactHead N ((finiteSpace n).starProjection v)‖^2 =
    FiniteSpectralBudget.optimizerTail Finset.univ
      (FiniteHeadTailSpectralRealization.sourceWeight (stageSpectralHead n N hN) v)
      (stageEigenvalue n N hN) := by
  have hfit := stageSpectralFit_eq_projection n N hN v hv
  have heq : (finiteSpace n).starProjection v -
      compactHead N ((finiteSpace n).starProjection v) =
      FiniteHeadTailSpectralRealization.fittedTail (stageSpectralHead n N hN)
        (stageSpectralTail n N hN) (stageEigenvalue n N hN) v := by
    rw [← hfit, compactHead_stageSpectralFit,
      FiniteHeadTailSpectralRealization.fullFit_eq_head_add_tail]
    abel
  rw [heq]
  exact FiniteHeadTailSpectralRealization.fittedTail_norm_sq _ _ _ v
    (FiniteHeadTailSpectralRealization.tail_basis_inner (stageTailLift n N hN))

/-- J is literally the displacement of the actual optimizer head from the
optimal head projection, retaining the second complete correction square. -/
theorem actualHeadDisplacement_eq_spectral (n N : ℕ) (hN : n+1 ≤ N)
    (v : ThresholdHilbert) (hv : compactHead N v = v) :
    ‖compactHead N ((finiteSpace n).starProjection v) -
      (stageHeadSpace n N).starProjection v‖^2 =
    FiniteSpectralBudget.headDisplacement Finset.univ
      (FiniteHeadTailSpectralRealization.sourceWeight (stageSpectralHead n N hN) v)
      (stageEigenvalue n N hN) := by
  rw [← stageSpectralFit_eq_projection n N hN v hv, compactHead_stageSpectralFit,
    ← stageSpectralHeadFit_eq_projection n N hN v]
  exact FiniteHeadTailSpectralRealization.headDisplacement_norm_sq _ _ v
    (FiniteHeadTailSpectralRealization.head_basis_orthonormal
      (stageHeadInclusion n N) (stageTailLift n N hN))
    (FiniteHeadTailSpectralRealization.eigenvalue_nonneg (stageTailLift n N hN))

theorem actualSourceMass_eq_headProjection (n N : ℕ) (hN : n+1 ≤ N)
    (v : ThresholdHilbert) :
    FiniteSpectralBudget.mass Finset.univ
      (FiniteHeadTailSpectralRealization.sourceWeight (stageSpectralHead n N hN) v) =
      ‖(stageHeadSpace n N).starProjection v‖^2 := by
  rw [← stageSpectralHeadFit_eq_projection n N hN v]
  symm
  exact FiniteHeadTailSpectralRealization.headFit_norm_sq _ v
    (FiniteHeadTailSpectralRealization.head_basis_orthonormal
      (stageHeadInclusion n N) (stageTailLift n N hN))

theorem actualSourceMass_eq_targetNorm_sub_headError
    (n N : ℕ) (hN : n+1 ≤ N) (v : ThresholdHilbert) :
    FiniteSpectralBudget.mass Finset.univ
      (FiniteHeadTailSpectralRealization.sourceWeight (stageSpectralHead n N hN) v) =
      ‖v‖^2 - ‖v - (stageHeadSpace n N).starProjection v‖^2 := by
  rw [actualSourceMass_eq_headProjection]
  have ho := Submodule.starProjection_inner_eq_zero v
    ((stageHeadSpace n N).starProjection v)
    ((stageHeadSpace n N).starProjection_apply_mem v)
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at ho
  rw [norm_sub_sq_real]
  linarith

theorem actualProjectionError_head_tail_identity (n N : ℕ)
    (v : ThresholdHilbert) (hv : compactHead N v = v) :
    ‖v - (finiteSpace n).starProjection v‖^2 =
      ‖v - (stageHeadSpace n N).starProjection v‖^2 +
      ‖compactHead N ((finiteSpace n).starProjection v) -
        (stageHeadSpace n N).starProjection v‖^2 +
      ‖(finiteSpace n).starProjection v -
        compactHead N ((finiteSpace n).starProjection v)‖^2 := by
  let p := (finiteSpace n).starProjection v
  let y := (stageHeadSpace n N).starProjection v
  have hp : p ∈ finiteSpace n := (finiteSpace n).starProjection_apply_mem v
  have hy : y ∈ stageHeadSpace n N := (stageHeadSpace n N).starProjection_apply_mem v
  have hQp : compactHead N p ∈ stageHeadSpace n N := ⟨⟨p, hp⟩, rfl⟩
  have horth : inner ℝ (v-y) (y-compactHead N p) = 0 := by
    rw [real_inner_comm]
    exact ((stageHeadSpace n N).mem_orthogonal (v-y)).mp
      (Submodule.sub_starProjection_mem_orthogonal v) _
      ((stageHeadSpace n N).sub_mem hy hQp)
  have hsplit : ‖v - compactHead N p‖^2 =
      ‖v-y‖^2 + ‖compactHead N p-y‖^2 := by
    have heq : v - compactHead N p = (v-y)+(y-compactHead N p) := by abel
    rw [heq, norm_add_sq_real, horth]
    rw [norm_sub_rev y (compactHead N p)]
    ring
  have hfull := compactHead_pythagoras N (v-p)
  rw [compactHead_sub, hv, hsplit] at hfull
  have htail : (v-p)-(v-compactHead N p) = -(p-compactHead N p) := by abel
  rw [htail, norm_neg] at hfull
  exact hfull

/-- Exact actual error e+T, now identified with the complete source spectrum.
Both correction squares remain visible in its proved geometric identity. -/
theorem actualProjectionError_eq_headError_add_correction
    (n N : ℕ) (hN : n+1 ≤ N) (v : ThresholdHilbert) (hv : compactHead N v = v) :
    ‖v - (finiteSpace n).starProjection v‖^2 =
      ‖v - (stageHeadSpace n N).starProjection v‖^2 +
      FiniteSpectralBudget.correction Finset.univ
        (FiniteHeadTailSpectralRealization.sourceWeight (stageSpectralHead n N hN) v)
        (stageEigenvalue n N hN) := by
  rw [actualProjectionError_head_tail_identity n N v hv,
    actualHeadDisplacement_eq_spectral n N hN v hv,
    actualOptimizerTail_eq_spectral n N hN v hv,
    FiniteSpectralBudget.correction_eq_headDisplacement_add_optimizerTail
      Finset.univ _ _ (fun i _ =>
        FiniteHeadTailSpectralRealization.eigenvalue_nonneg (stageTailLift n N hN) i)]
  ring

end RiemannResearch.RH.Pareto.CoefficientStabilization
