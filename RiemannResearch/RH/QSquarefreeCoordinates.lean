/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-!
# Squarefree legal coordinates in L²(Q)

The full divisor-wavelet Hilbert basis gives a unitary coordinate map. Its restriction
to the closed span of the squarefree residue atoms is an isometric equivalence onto
a closed coordinate subspace. This file proves the restriction, its adjoint and
orthogonal projection identities, and the exact mean/nonconstant-energy error split.

The arithmetic Parseval input is the preceding `QDivisorHilbertBasis` development.
The squarefree approximation criterion motivating this restriction is discussed in
B. Bagchi, "On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the
Riemann hypothesis", Remarks 4 and 8, https://arxiv.org/abs/math/0607733.
That reference supports the approximation criterion, not a proof of its unresolved
density hypothesis in this repository.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.RH.QSquarefreeCoordinates
open ZetaTwoHilbert ZetaTwoProbability QDivisorHilbert
abbrev Coordinates := lp (fun _ : ℕ+ => ℝ) 2
def fullCoordinates : QHilbert ≃ₗᵢ[ℝ] Coordinates := divisorHilbertBasis.repr
def coordinateSpace : Submodule ℝ Coordinates :=
  qSquarefreeCRTSpan.topologicalClosure.map fullCoordinates.toLinearEquiv.toLinearMap
def coordinateEquiv :
    qSquarefreeCRTSpan.topologicalClosure ≃ₗᵢ[ℝ] coordinateSpace :=
  LinearIsometryEquiv.submoduleMap qSquarefreeCRTSpan.topologicalClosure fullCoordinates
def coordinateMap : qSquarefreeCRTSpan.topologicalClosure →ₗᵢ[ℝ] Coordinates :=
  fullCoordinates.toLinearIsometry.comp qSquarefreeCRTSpan.topologicalClosure.subtypeₗᵢ
theorem fullCoordinates_apply (f : QHilbert) (r : ℕ+) :
    fullCoordinates f r = inner ℝ f (normalizedDivisorWavelet r) := by
  simp only [fullCoordinates, HilbertBasis.repr_apply_apply, divisorHilbertBasis_apply,
    real_inner_comm]
theorem mem_coordinateSpace (z : Coordinates) :
    z ∈ coordinateSpace ↔ fullCoordinates.symm z ∈ qSquarefreeCRTSpan.topologicalClosure := by
  constructor
  · intro hz
    obtain ⟨f, hf⟩ := coordinateEquiv.surjective ⟨z, hz⟩
    have he : (coordinateEquiv f : Coordinates) = z := congrArg Subtype.val hf
    change fullCoordinates (f : QHilbert) = z at he
    rw [← he, fullCoordinates.symm_apply_apply]
    exact f.property
  · intro hz
    exact ⟨fullCoordinates.symm z, hz, fullCoordinates.apply_symm_apply z⟩
theorem coordinateSpace_isClosed : IsClosed (coordinateSpace : Set Coordinates) := by
  have he : (coordinateSpace : Set Coordinates) =
      fullCoordinates '' (qSquarefreeCRTSpan.topologicalClosure : Set QHilbert) := rfl
  rw [he]
  exact fullCoordinates.toHomeomorph.isClosedMap _ qSquarefreeCRTSpan.isClosed_topologicalClosure
instance : CompleteSpace qSquarefreeCRTSpan.topologicalClosure :=
  qSquarefreeCRTSpan.isClosed_topologicalClosure.completeSpace_coe
instance : CompleteSpace coordinateSpace :=
  coordinateSpace_isClosed.completeSpace_coe
theorem coordinateMap_norm (f : qSquarefreeCRTSpan.topologicalClosure) :
    ‖coordinateMap f‖ = ‖f‖ := coordinateMap.norm_map f
theorem coordinateMap_inner (f g : qSquarefreeCRTSpan.topologicalClosure) :
    inner ℝ (coordinateMap f) (coordinateMap g) = inner ℝ f g :=
  coordinateMap.inner_map_map f g
theorem fullCoordinates_qOne_apply (r : ℕ+) :
    fullCoordinates qOne r = if r = 1 then 1 else 0 := by
  rw [fullCoordinates_apply, normalizedDivisorWavelet, inner_smul_right,
    qOne_divisorWavelet_inner]
  by_cases h : r = 1
  · subst r
    simp [qJordanTwo]
  · simp [h]
theorem fullCoordinates_first (f : QHilbert) :
    fullCoordinates f 1 = inner ℝ f qOne := by
  rw [fullCoordinates_apply]
  simp [normalizedDivisorWavelet, qJordanTwo, divisorWavelet_one]
theorem residue_coordinate (m : ℕ) (r : ℕ+) :
    fullCoordinates (qResidue m) r =
      qResidueDivisorCoefficient m (r : ℕ) / Real.sqrt (qJordanTwo (r : ℕ)) := by
  rw [fullCoordinates_apply, normalizedDivisorWavelet, inner_smul_right,
    qResidue_divisorWavelet_inner]
  ring
theorem fullCoordinates_error (f : QHilbert) :
    ‖fullCoordinates qOne - fullCoordinates f‖ = ‖qOne - f‖ := by
  rw [← map_sub, fullCoordinates.norm_map]

/-- Reconstruction preserves every Q vector. -/
theorem inverse_reconstruction (f : QHilbert) :
    fullCoordinates.symm (fullCoordinates f) = f :=
  fullCoordinates.symm_apply_apply f

theorem coordinates_parseval (f : QHilbert) :
    (∑' r : ℕ+, (fullCoordinates f r)^2) = ‖f‖^2 := by
  rw [← fullCoordinates.norm_map f, ← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
  apply tsum_congr
  intro r
  simp [Real.norm_eq_abs, sq_abs]

def centered (f : QHilbert) : QHilbert := f - inner ℝ f qOne • qOne

theorem centered_coordinates (f : QHilbert) (r : ℕ+) :
    fullCoordinates (centered f) r =
      if r = 1 then 0 else fullCoordinates f r := by
  change fullCoordinates (f - inner ℝ f qOne • qOne) r = _
  rw [map_sub, map_smul]
  change fullCoordinates f r - inner ℝ f qOne * fullCoordinates qOne r = _
  rw [fullCoordinates_qOne_apply]
  by_cases hr : r = 1
  · subst r
    simp [fullCoordinates_first]
  · simp [hr]

def nonconstantEnergy (z : Coordinates) : ℝ :=
  ∑' r : ℕ+, if r = 1 then 0 else (z r)^2

theorem centered_energy (f : QHilbert) :
    nonconstantEnergy (fullCoordinates f) = ‖centered f‖^2 := by
  have h := coordinates_parseval (centered f)
  simp_rw [centered_coordinates] at h
  simpa only [nonconstantEnergy, ite_pow, zero_pow (by norm_num : 2 ≠ 0)] using h

theorem centered_norm_sq (f : QHilbert) :
    ‖centered f‖^2 = ‖f‖^2 - (fullCoordinates f 1)^2 := by
  simp only [centered, norm_sub_sq_real, inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, qOne_norm_sq, mul_one, fullCoordinates_first]
  ring

theorem error_eq_mean_and_nonconstantEnergy (f : QHilbert) :
    ‖qOne - f‖^2 = (1 - fullCoordinates f 1)^2 +
      nonconstantEnergy (fullCoordinates f) := by
  rw [centered_energy, centered_norm_sq, norm_sub_sq_real, qOne_norm_sq,
    fullCoordinates_first, real_inner_comm qOne f]
  ring

def coordinateAdjoint : Coordinates →L[ℝ] qSquarefreeCRTSpan.topologicalClosure :=
  coordinateMap.toContinuousLinearMap.adjoint

theorem coordinateAdjoint_apply (z : Coordinates) :
    coordinateAdjoint z =
      qSquarefreeCRTSpan.topologicalClosure.orthogonalProjectionOnto (fullCoordinates.symm z) := by
  apply ext_inner_left ℝ
  intro f
  rw [coordinateAdjoint, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (fullCoordinates (f : QHilbert)) z =
    inner ℝ (f : QHilbert)
      (qSquarefreeCRTSpan.topologicalClosure.starProjection (fullCoordinates.symm z))
  have hi := fullCoordinates.inner_map_map (f : QHilbert) (fullCoordinates.symm z)
  rw [fullCoordinates.apply_symm_apply] at hi
  rw [hi]
  have ho : inner ℝ (f : QHilbert) (fullCoordinates.symm z -
      qSquarefreeCRTSpan.topologicalClosure.starProjection (fullCoordinates.symm z)) = 0 :=
    (qSquarefreeCRTSpan.topologicalClosure.mem_orthogonal _).mp
      (Submodule.sub_starProjection_mem_orthogonal (fullCoordinates.symm z)) _ f.property
  rw [inner_sub_right] at ho
  linarith

theorem coordinateAdjoint_coordinateMap (f : qSquarefreeCRTSpan.topologicalClosure) :
    coordinateAdjoint (coordinateMap f) = f := by
  rw [coordinateAdjoint_apply]
  apply Subtype.ext
  change qSquarefreeCRTSpan.topologicalClosure.starProjection
    (fullCoordinates.symm (fullCoordinates (f : QHilbert))) = (f : QHilbert)
  rw [fullCoordinates.symm_apply_apply, Submodule.starProjection_eq_self_iff.mpr f.property]

theorem coordinate_projection_conjugation (z : Coordinates) :
    coordinateSpace.starProjection z =
      fullCoordinates (qSquarefreeCRTSpan.topologicalClosure.starProjection
        (fullCoordinates.symm z)) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · apply (mem_coordinateSpace _).mpr
    rw [fullCoordinates.symm_apply_apply]
    exact qSquarefreeCRTSpan.topologicalClosure.starProjection_apply_mem _
  · intro w hw
    have hmem := (mem_coordinateSpace _).mp hw
    have ho : inner ℝ
        (fullCoordinates.symm z -
          qSquarefreeCRTSpan.topologicalClosure.starProjection (fullCoordinates.symm z))
        (fullCoordinates.symm w) = 0 :=
      (Submodule.mem_orthogonal' _ _).mp
        (Submodule.sub_starProjection_mem_orthogonal (fullCoordinates.symm z)) _ hmem
    have hi := fullCoordinates.inner_map_map
      (fullCoordinates.symm z -
        qSquarefreeCRTSpan.topologicalClosure.starProjection (fullCoordinates.symm z))
      (fullCoordinates.symm w)
    rw [map_sub, fullCoordinates.apply_symm_apply, fullCoordinates.apply_symm_apply] at hi
    rw [hi]
    exact ho

theorem coordinateMap_coordinateAdjoint (z : Coordinates) :
    coordinateMap (coordinateAdjoint z) = coordinateSpace.starProjection z := by
  rw [coordinateAdjoint_apply, coordinate_projection_conjugation]
  rfl

end RiemannResearch.RH.QSquarefreeCoordinates
