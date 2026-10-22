/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.FiniteMeanZeroSlope

/-!
# Finite endpoint-zero profile coordinates

This module closes the finite coordinate chain from curvature vectors, through
mean-zero slope vectors, to profiles whose initial and final coordinates both
vanish. The construction prefix-integrates centered slopes on the unit grid,
and its inverse takes finite adjacent curvature.

Source: user-provided argument,
RH_Proof_First_Continuation_2026-09-04.md, Section 5. The source supports the
coordinate and gauge strategy. This is finite-dimensional algebra; it does not
identify a Weil form, establish dyadic density, or prove RH.
-/

namespace RiemannResearch.RH.PrimeGapCurvature

noncomputable section

open scoped BigOperators

/-- The constant unit gap vector on a finite window. -/
def unitFiniteGap (n : ℕ) : Fin (n + 1) → ℝ :=
  fun _ ↦ 1

@[simp] theorem unitFiniteGap_apply (n : ℕ) (j : Fin (n + 1)) :
    unitFiniteGap n j = 1 :=
  rfl

/-- Read a finite slope vector at a natural index, returning zero outside. -/
def finiteSlopeGet {n : ℕ} (s : Fin (n + 1) → ℝ) (j : ℕ) : ℝ :=
  if hj : j < n + 1 then s ⟨j, hj⟩ else 0

/-- Prefix-integrate a finite slope vector, with initial profile value zero. -/
def slopeProfilePrefix {n : ℕ} (s : Fin (n + 1) → ℝ)
    (k : Fin (n + 2)) : ℝ :=
  ∑ j ∈ Finset.range k.val, finiteSlopeGet s j

@[simp] theorem slopeProfilePrefix_zero {n : ℕ}
    (s : Fin (n + 1) → ℝ) :
    slopeProfilePrefix s (0 : Fin (n + 2)) = 0 := by
  simp [slopeProfilePrefix]

theorem slopeProfilePrefix_succ_sub {n : ℕ}
    (s : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    slopeProfilePrefix s j.succ - slopeProfilePrefix s j.castSucc = s j := by
  unfold slopeProfilePrefix
  change (∑ k ∈ Finset.range (j.val + 1), finiteSlopeGet s k) -
    (∑ k ∈ Finset.range j.val, finiteSlopeGet s k) = s j
  rw [Finset.sum_range_succ]
  simp [finiteSlopeGet, j.isLt]

theorem slopeProfilePrefix_last {n : ℕ}
    (s : Fin (n + 1) → ℝ) :
    slopeProfilePrefix s (Fin.last (n + 1)) = finiteSlopeSumMap n s := by
  change (∑ j ∈ Finset.range (n + 1), finiteSlopeGet s j) =
    ∑ j, s j
  rw [Finset.sum_fin_eq_sum_range]
  rfl

lemma finiteSlopeGet_add {n : ℕ} (s t : Fin (n + 1) → ℝ) (j : ℕ) :
    finiteSlopeGet (s + t) j = finiteSlopeGet s j + finiteSlopeGet t j := by
  by_cases hj : j < n + 1
  · simp [finiteSlopeGet, hj]
  · simp [finiteSlopeGet, hj]

lemma finiteSlopeGet_smul {n : ℕ} (a : ℝ)
    (s : Fin (n + 1) → ℝ) (j : ℕ) :
    finiteSlopeGet (a • s) j = a * finiteSlopeGet s j := by
  by_cases hj : j < n + 1
  · simp [finiteSlopeGet, hj]
  · simp [finiteSlopeGet, hj]

lemma slopeProfilePrefix_add {n : ℕ}
    (s t : Fin (n + 1) → ℝ) (k : Fin (n + 2)) :
    slopeProfilePrefix (s + t) k =
      slopeProfilePrefix s k + slopeProfilePrefix t k := by
  simp [slopeProfilePrefix, finiteSlopeGet_add, Finset.sum_add_distrib]

lemma slopeProfilePrefix_smul {n : ℕ} (a : ℝ)
    (s : Fin (n + 1) → ℝ) (k : Fin (n + 2)) :
    slopeProfilePrefix (a • s) k = a * slopeProfilePrefix s k := by
  simp [slopeProfilePrefix, finiteSlopeGet_smul, Finset.mul_sum]

/-- Prefix integration as a linear map from slopes to profiles. -/
def slopeProfilePrefixLinearMap (n : ℕ) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 2) → ℝ) where
  toFun s := slopeProfilePrefix s
  map_add' s t := by
    funext k
    exact slopeProfilePrefix_add s t k
  map_smul' a s := by
    funext k
    exact slopeProfilePrefix_smul a s k

@[simp] theorem slopeProfilePrefixLinearMap_apply
    (n : ℕ) (s : Fin (n + 1) → ℝ) (k : Fin (n + 2)) :
    slopeProfilePrefixLinearMap n s k = slopeProfilePrefix s k :=
  rfl

/-- On the unit grid, adjacent slopes undo prefix integration. -/
theorem finiteAdjacentSlope_slopeProfilePrefix
    (n : ℕ) (s : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    finiteAdjacentSlope (unitFiniteGap n) (slopeProfilePrefix s) j = s j := by
  rw [finiteAdjacentSlope, slopeProfilePrefix_succ_sub]
  simp

/-- Prefix-integrating the unit-grid adjacent slopes reconstructs a profile
up to its initial value. -/
theorem slopeProfilePrefix_finiteAdjacentSlope
    (n : ℕ) (z : Fin (n + 2) → ℝ) (k : Fin (n + 2)) :
    slopeProfilePrefix (finiteAdjacentSlope (unitFiniteGap n) z) k =
      z k - z 0 := by
  classical
  let f : ℕ → ℝ := fun i ↦
    if hi : i < n + 2 then z ⟨i, hi⟩ else 0
  unfold slopeProfilePrefix
  calc
    (∑ j ∈ Finset.range k.val,
        finiteSlopeGet (finiteAdjacentSlope (unitFiniteGap n) z) j) =
        ∑ j ∈ Finset.range k.val, (f (j + 1) - f j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjk : j < k.val := Finset.mem_range.mp hj
      have hjslope : j < n + 1 := by omega
      have hjprofile : j < n + 2 := by omega
      have hjsucc : j + 1 < n + 2 := by omega
      simp only [finiteSlopeGet, dif_pos hjslope, finiteAdjacentSlope,
        unitFiniteGap_apply, div_one]
      change
        z ⟨j + 1, by omega⟩ - z ⟨j, by omega⟩ =
          f (j + 1) - f j
      unfold f
      rw [dif_pos hjsucc, dif_pos hjprofile]
    _ = f k.val - f 0 := by
      rw [Finset.sum_range_sub]
    _ = z k - z 0 := by
      unfold f
      rw [dif_pos k.isLt, dif_pos (Nat.zero_lt_succ (n + 1))]
      simp

/-- Profiles whose first and last coordinates both vanish. -/
def endpointZeroProfileSubmodule (n : ℕ) :
    Submodule ℝ (Fin (n + 2) → ℝ) where
  carrier := {z | z 0 = 0 ∧ z (Fin.last (n + 1)) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro z w hz hw
    constructor
    · simp [hz.1, hw.1]
    · simp [hz.2, hw.2]
  smul_mem' := by
    intro a z hz
    constructor
    · simp [hz.1]
    · simp [hz.2]

@[simp] theorem mem_endpointZeroProfileSubmodule
    (n : ℕ) (z : Fin (n + 2) → ℝ) :
    z ∈ endpointZeroProfileSubmodule n ↔
      z 0 = 0 ∧ z (Fin.last (n + 1)) = 0 :=
  Iff.rfl

/-- Integrate the centered curvature-prefix slopes. -/
def centeredProfileSectionLinearMap (n : ℕ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin (n + 2) → ℝ) :=
  (slopeProfilePrefixLinearMap n).comp (centeredSlopePrefixLinearMap n)

@[simp] theorem centeredProfileSectionLinearMap_apply
    (n : ℕ) (c : Fin n → ℝ) (k : Fin (n + 2)) :
    centeredProfileSectionLinearMap n c k =
      slopeProfilePrefix (centeredSlopePrefixLinearMap n c) k :=
  rfl

@[simp] theorem centeredProfileSection_zero
    (n : ℕ) (c : Fin n → ℝ) :
    centeredProfileSectionLinearMap n c 0 = 0 := by
  rw [centeredProfileSectionLinearMap_apply, slopeProfilePrefix_zero]

@[simp] theorem centeredProfileSection_last
    (n : ℕ) (c : Fin n → ℝ) :
    centeredProfileSectionLinearMap n c (Fin.last (n + 1)) = 0 := by
  rw [centeredProfileSectionLinearMap_apply, slopeProfilePrefix_last]
  exact centeredSlopePrefix_sum_zero n c

/-- The adjacent slopes of the centered profile are the centered prefix
slopes. -/
theorem finiteAdjacentSlope_centeredProfileSection
    (n : ℕ) (c : Fin n → ℝ) (j : Fin (n + 1)) :
    finiteAdjacentSlope (unitFiniteGap n)
        (centeredProfileSectionLinearMap n c) j =
      centeredSlopePrefixLinearMap n c j := by
  change finiteAdjacentSlope (unitFiniteGap n)
    (slopeProfilePrefix (centeredSlopePrefixLinearMap n c)) j =
      centeredSlopePrefixLinearMap n c j
  exact finiteAdjacentSlope_slopeProfilePrefix n
    (centeredSlopePrefixLinearMap n c) j

/-- The centered endpoint-zero profile has exactly the prescribed curvature. -/
theorem finiteCurvature_centeredProfileSection
    (n : ℕ) (c : Fin n → ℝ) :
    finiteCurvature (unitFiniteGap n)
      (centeredProfileSectionLinearMap n c) = c := by
  funext i
  rw [finiteCurvature,
    finiteAdjacentSlope_centeredProfileSection,
    finiteAdjacentSlope_centeredProfileSection]
  exact finiteSlopeDifference_centeredSlopePrefix_apply n c i

/-- Unit-grid adjacent slopes have zero sum when both profile endpoints
vanish. -/
theorem finiteSlopeSumMap_finiteAdjacentSlope_of_endpoints_zero
    (n : ℕ) (z : Fin (n + 2) → ℝ)
    (hzero : z 0 = 0) (hlast : z (Fin.last (n + 1)) = 0) :
    finiteSlopeSumMap n (finiteAdjacentSlope (unitFiniteGap n) z) = 0 := by
  calc
    finiteSlopeSumMap n (finiteAdjacentSlope (unitFiniteGap n) z) =
        slopeProfilePrefix (finiteAdjacentSlope (unitFiniteGap n) z)
          (Fin.last (n + 1)) := by
      exact (slopeProfilePrefix_last
        (finiteAdjacentSlope (unitFiniteGap n) z)).symm
    _ = z (Fin.last (n + 1)) - z 0 :=
      slopeProfilePrefix_finiteAdjacentSlope n z (Fin.last (n + 1))
    _ = 0 := by rw [hzero, hlast]; ring

/-- Curvature reconstructs every profile whose two endpoints vanish. -/
theorem centeredProfileSection_finiteCurvature_of_endpoints_zero
    (n : ℕ) (z : Fin (n + 2) → ℝ)
    (hzero : z 0 = 0) (hlast : z (Fin.last (n + 1)) = 0) :
    centeredProfileSectionLinearMap n
      (finiteCurvature (unitFiniteGap n) z) = z := by
  let s : Fin (n + 1) → ℝ :=
    finiteAdjacentSlope (unitFiniteGap n) z
  have hs : finiteSlopeSumMap n s = 0 := by
    exact finiteSlopeSumMap_finiteAdjacentSlope_of_endpoints_zero
      n z hzero hlast
  have hcurv :
      finiteCurvature (unitFiniteGap n) z =
        finiteSlopeDifferenceMap n s := by
    rfl
  have hslopes :
      centeredSlopePrefixLinearMap n
          (finiteCurvature (unitFiniteGap n) z) = s := by
    rw [hcurv]
    exact centeredSlopePrefix_difference_of_sum_eq_zero n s hs
  funext k
  rw [centeredProfileSectionLinearMap_apply, hslopes,
    slopeProfilePrefix_finiteAdjacentSlope, hzero, sub_zero]

/-- Curvature coordinates are linearly equivalent to profiles with both
endpoints zero. -/
def curvatureEndpointZeroProfileEquiv (n : ℕ) :
    (Fin n → ℝ) ≃ₗ[ℝ] endpointZeroProfileSubmodule n where
  toFun c :=
    ⟨centeredProfileSectionLinearMap n c,
      (mem_endpointZeroProfileSubmodule n
        (centeredProfileSectionLinearMap n c)).2
        ⟨centeredProfileSection_zero n c,
          centeredProfileSection_last n c⟩⟩
  invFun z := finiteCurvatureMap (unitFiniteGap n) z.1
  left_inv c :=
    finiteCurvature_centeredProfileSection n c
  right_inv z := by
    apply Subtype.ext
    exact centeredProfileSection_finiteCurvature_of_endpoints_zero
      n z.1 z.2.1 z.2.2
  map_add' c d := by
    apply Subtype.ext
    exact (centeredProfileSectionLinearMap n).map_add c d
  map_smul' a c := by
    apply Subtype.ext
    exact (centeredProfileSectionLinearMap n).map_smul a c

@[simp] theorem curvatureEndpointZeroProfileEquiv_apply
    (n : ℕ) (c : Fin n → ℝ) :
    ((curvatureEndpointZeroProfileEquiv n c :
        endpointZeroProfileSubmodule n) : Fin (n + 2) → ℝ) =
      centeredProfileSectionLinearMap n c :=
  rfl

@[simp] theorem curvatureEndpointZeroProfileEquiv_symm_apply
    (n : ℕ) (z : endpointZeroProfileSubmodule n) :
    (curvatureEndpointZeroProfileEquiv n).symm z =
      finiteCurvatureMap (unitFiniteGap n) z.1 :=
  rfl

/-- The forward endpoint-zero profile realizes exactly the mean-zero slope
vector attached to its curvature coordinates. -/
theorem finiteAdjacentSlope_curvatureEndpointZeroProfileEquiv
    (n : ℕ) (c : Fin n → ℝ) :
    finiteAdjacentSlope (unitFiniteGap n)
        ((curvatureEndpointZeroProfileEquiv n c :
          endpointZeroProfileSubmodule n) : Fin (n + 2) → ℝ) =
      ((curvatureMeanZeroSlopeEquiv n c :
        meanZeroSlopeSubmodule n) : Fin (n + 1) → ℝ) := by
  funext j
  rw [curvatureEndpointZeroProfileEquiv_apply,
    finiteAdjacentSlope_centeredProfileSection,
    curvatureMeanZeroSlopeEquiv_apply]

end

end RiemannResearch.RH.PrimeGapCurvature
