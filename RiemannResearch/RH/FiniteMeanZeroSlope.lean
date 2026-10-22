/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.FiniteCurvatureGreen
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Finite curvature coordinates and mean-zero slopes

This module identifies finite adjacent-curvature coordinates with slope
vectors whose coordinate sum is zero. The equivalence is explicit: take
adjacent differences in one direction, and in the other take curvature prefix
sums and subtract their arithmetic mean.

Source: user-provided argument,
RH_Proof_First_Continuation_2026-09-04.md, Section 5. The source supports the
statements and proof strategy. This is finite-dimensional algebra; it does not
identify a Weil form, establish dyadic density, or prove RH.
-/

namespace RiemannResearch.RH.PrimeGapCurvature

noncomputable section

open scoped BigOperators

/-- Adjacent differences of a finite slope vector. -/
def finiteSlopeDifferenceMap (n : ℕ) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun s i := s i.succ - s i.castSucc
  map_add' s t := by
    funext i
    simp
    ring
  map_smul' a s := by
    funext i
    simp [smul_eq_mul]
    ring

@[simp] theorem finiteSlopeDifferenceMap_apply
    (n : ℕ) (s : Fin (n + 1) → ℝ) (i : Fin n) :
    finiteSlopeDifferenceMap n s i = s i.succ - s i.castSucc :=
  rfl

/-- Sum of all coordinates of a finite slope vector. -/
def finiteSlopeSumMap (n : ℕ) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ where
  toFun s := ∑ j, s j
  map_add' s t := by
    exact Finset.sum_add_distrib
  map_smul' a s := by
    simp [Finset.mul_sum]

@[simp] theorem finiteSlopeSumMap_apply
    (n : ℕ) (s : Fin (n + 1) → ℝ) :
    finiteSlopeSumMap n s = ∑ j, s j :=
  rfl

/-- The codimension-one space of finite slope vectors with coordinate sum
zero. -/
def meanZeroSlopeSubmodule (n : ℕ) :
    Submodule ℝ (Fin (n + 1) → ℝ) :=
  LinearMap.ker (finiteSlopeSumMap n)

/-- Prefix slopes with their arithmetic mean removed. -/
def centeredSlopePrefix {n : ℕ}
    (c : Fin n → ℝ) (j : Fin (n + 1)) : ℝ :=
  slopePrefix c j -
    (∑ k, slopePrefix c k) / ((n + 1 : ℕ) : ℝ)

lemma centeredSlopePrefix_add {n : ℕ}
    (c d : Fin n → ℝ) (j : Fin (n + 1)) :
    centeredSlopePrefix (c + d) j =
      centeredSlopePrefix c j + centeredSlopePrefix d j := by
  simp only [centeredSlopePrefix, slopePrefix_add]
  rw [Finset.sum_add_distrib]
  ring

lemma centeredSlopePrefix_smul {n : ℕ}
    (a : ℝ) (c : Fin n → ℝ) (j : Fin (n + 1)) :
    centeredSlopePrefix (a • c) j =
      a * centeredSlopePrefix c j := by
  simp only [centeredSlopePrefix, slopePrefix_smul]
  rw [← Finset.mul_sum]
  ring

/-- The centered prefix construction as a linear map. -/
def centeredSlopePrefixLinearMap (n : ℕ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun c := centeredSlopePrefix c
  map_add' c d := by
    funext j
    exact centeredSlopePrefix_add c d j
  map_smul' a c := by
    funext j
    exact centeredSlopePrefix_smul a c j

@[simp] theorem centeredSlopePrefixLinearMap_apply
    (n : ℕ) (c : Fin n → ℝ) (j : Fin (n + 1)) :
    centeredSlopePrefixLinearMap n c j = centeredSlopePrefix c j :=
  rfl

/-- Centering makes the coordinate sum vanish. -/
theorem centeredSlopePrefix_sum_zero
    (n : ℕ) (c : Fin n → ℝ) :
    finiteSlopeSumMap n (centeredSlopePrefixLinearMap n c) = 0 := by
  classical
  change
    (∑ j, (slopePrefix c j -
      (∑ k, slopePrefix c k) / ((n + 1 : ℕ) : ℝ))) = 0
  rw [Finset.sum_sub_distrib, Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hn]
  ring

/-- Taking adjacent differences after centering recovers the curvature
data. -/
theorem finiteSlopeDifference_centeredSlopePrefix_apply
    (n : ℕ) (c : Fin n → ℝ) (i : Fin n) :
    finiteSlopeDifferenceMap n (centeredSlopePrefixLinearMap n c) i =
      c i := by
  change centeredSlopePrefix c i.succ - centeredSlopePrefix c i.castSucc = c i
  simp only [centeredSlopePrefix]
  rw [sub_sub_sub_cancel_right, slopePrefix_succ_sub]

/-- The difference map is a left inverse of the centered-prefix map. -/
theorem finiteSlopeDifference_comp_centeredSlopePrefix
    (n : ℕ) :
    (finiteSlopeDifferenceMap n).comp
        (centeredSlopePrefixLinearMap n) =
      LinearMap.id := by
  apply LinearMap.ext
  intro c
  funext i
  exact finiteSlopeDifference_centeredSlopePrefix_apply n c i

/-- Telescoping finite differences reconstruct a slope vector up to its
initial coordinate. -/
theorem slopePrefix_finiteSlopeDifferenceMap
    (n : ℕ) (s : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    slopePrefix (finiteSlopeDifferenceMap n s) j = s j - s 0 := by
  classical
  let f : ℕ → ℝ := fun k =>
    if hk : k < n + 1 then s ⟨k, hk⟩ else 0
  unfold slopePrefix
  calc
    (∑ i ∈ Finset.range j.val,
        finiteCurvatureGet (finiteSlopeDifferenceMap n s) i) =
        ∑ i ∈ Finset.range j.val, (f (i + 1) - f i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hij : i < j.val := Finset.mem_range.mp hi
      have hin : i < n := by omega
      have hiwide : i < n + 1 := by omega
      have hisucc : i + 1 < n + 1 := by omega
      simp only [finiteCurvatureGet, dif_pos hin,
        finiteSlopeDifferenceMap_apply]
      change
        s ⟨i + 1, by omega⟩ - s ⟨i, by omega⟩ =
          f (i + 1) - f i
      unfold f
      rw [dif_pos hisucc, dif_pos hiwide]
    _ = f j.val - f 0 := by
      rw [Finset.sum_range_sub]
    _ = s j - s 0 := by
      unfold f
      rw [dif_pos j.isLt, dif_pos (Nat.zero_lt_succ n)]
      simp

/-- A zero-sum slope vector is exactly reconstructed from its adjacent
differences by the centered prefix construction. -/
theorem centeredSlopePrefix_difference_of_sum_eq_zero
    (n : ℕ) (s : Fin (n + 1) → ℝ)
    (hs : finiteSlopeSumMap n s = 0) :
    centeredSlopePrefixLinearMap n (finiteSlopeDifferenceMap n s) = s := by
  classical
  have hs' : (∑ k, s k) = 0 := by
    simpa only [finiteSlopeSumMap_apply] using hs
  have hsumdiff :
      (∑ k : Fin (n + 1), (s k - s 0)) =
        -(((n + 1 : ℕ) : ℝ) * s 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hs']
    ring
  funext j
  simp only [centeredSlopePrefixLinearMap_apply, centeredSlopePrefix,
    slopePrefix_finiteSlopeDifferenceMap]
  rw [hsumdiff]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hn]
  ring

/-- Every curvature vector is the adjacent difference of its centered prefix
slopes. -/
theorem finiteSlopeDifferenceMap_surjective (n : ℕ) :
    Function.Surjective (finiteSlopeDifferenceMap n) := by
  intro c
  refine ⟨centeredSlopePrefixLinearMap n c, ?_⟩
  funext i
  exact finiteSlopeDifference_centeredSlopePrefix_apply n c i

/-- The centered-prefix map is injective. -/
theorem centeredSlopePrefixLinearMap_injective (n : ℕ) :
    Function.Injective (centeredSlopePrefixLinearMap n) := by
  intro c d h
  funext i
  calc
    c i =
        finiteSlopeDifferenceMap n (centeredSlopePrefixLinearMap n c) i := by
          exact (finiteSlopeDifference_centeredSlopePrefix_apply n c i).symm
    _ = finiteSlopeDifferenceMap n (centeredSlopePrefixLinearMap n d) i := by
          rw [h]
    _ = d i := finiteSlopeDifference_centeredSlopePrefix_apply n d i

/-- The centered prefixes are exactly the finite zero-sum slope vectors. -/
theorem range_centeredSlopePrefixLinearMap (n : ℕ) :
    LinearMap.range (centeredSlopePrefixLinearMap n) =
      meanZeroSlopeSubmodule n := by
  ext s
  constructor
  · rintro ⟨c, rfl⟩
    rw [meanZeroSlopeSubmodule, LinearMap.mem_ker]
    exact centeredSlopePrefix_sum_zero n c
  · intro hs
    rw [meanZeroSlopeSubmodule, LinearMap.mem_ker] at hs
    refine ⟨finiteSlopeDifferenceMap n s, ?_⟩
    exact centeredSlopePrefix_difference_of_sum_eq_zero n s hs

/-- Curvature coordinates are linearly equivalent to finite mean-zero
slopes. -/
def curvatureMeanZeroSlopeEquiv (n : ℕ) :
    (Fin n → ℝ) ≃ₗ[ℝ] meanZeroSlopeSubmodule n where
  toFun c :=
    ⟨centeredSlopePrefixLinearMap n c, by
      change
        finiteSlopeSumMap n (centeredSlopePrefixLinearMap n c) = 0
      exact centeredSlopePrefix_sum_zero n c⟩
  invFun s := finiteSlopeDifferenceMap n s.1
  left_inv c := by
    funext i
    exact finiteSlopeDifference_centeredSlopePrefix_apply n c i
  right_inv s := by
    apply Subtype.ext
    have hs : finiteSlopeSumMap n s.1 = 0 := by
      exact (LinearMap.mem_ker).mp s.2
    exact centeredSlopePrefix_difference_of_sum_eq_zero n s.1 hs
  map_add' c d := by
    apply Subtype.ext
    exact (centeredSlopePrefixLinearMap n).map_add c d
  map_smul' a c := by
    apply Subtype.ext
    exact (centeredSlopePrefixLinearMap n).map_smul a c

@[simp] theorem curvatureMeanZeroSlopeEquiv_apply
    (n : ℕ) (c : Fin n → ℝ) :
    ((curvatureMeanZeroSlopeEquiv n c : meanZeroSlopeSubmodule n) :
      Fin (n + 1) → ℝ) =
      centeredSlopePrefixLinearMap n c :=
  rfl

@[simp] theorem curvatureMeanZeroSlopeEquiv_symm_apply
    (n : ℕ) (s : meanZeroSlopeSubmodule n) :
    (curvatureMeanZeroSlopeEquiv n).symm s =
      finiteSlopeDifferenceMap n s.1 :=
  rfl

/-- The anchored prefix profile differs from the centered slope gauge by one
constant slope. -/
theorem finiteAdjacentSlope_profilePrefix_eq_centeredSlope_add_mean
    {n : ℕ} (g : Fin (n + 1) → ℝ) (hg : ∀ j, g j ≠ 0)
    (c : Fin n → ℝ) (j : Fin (n + 1)) :
    finiteAdjacentSlope g (profilePrefix g c) j =
      centeredSlopePrefixLinearMap n c j +
        (∑ k, slopePrefix c k) / ((n + 1 : ℕ) : ℝ) := by
  rw [finiteAdjacentSlope_profilePrefix g hg]
  simp only [centeredSlopePrefixLinearMap_apply, centeredSlopePrefix]
  ring

end

end RiemannResearch.RH.PrimeGapCurvature
