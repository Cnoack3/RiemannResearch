/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.FiniteCurvatureGreen
import RiemannResearch.LinearAlgebra.DualGreenProjection
import RiemannResearch.LinearAlgebra.FiniteWeightedEnergy

/-!
# Weighted Green representatives for finite adjacent curvature

This module constructs the positive weighted bilinear form on finite profiles,
the explicit weighted projection onto affine profiles, and the orthogonalized
prefix right inverse of finite adjacent curvature. It then specializes the
abstract dual Green identities to prove exact Pythagoras, minimization, and
uniqueness on every finite curvature fiber.

Source: user-provided argument,
`RH_Proof_First_Continuation_2026-09-04.md`, Section 2. The source supports the
statements and proof strategy. These are finite-dimensional algebraic results;
they neither identify this energy with a Weil form nor prove RH.
-/

namespace RiemannResearch.RH.PrimeGapCurvature

noncomputable section

open scoped BigOperators

/-- Positive coordinate-weighted bilinear form on finite profiles. -/
def weightedProfileBilin {n : ℕ} (w : Fin (n + 2) → ℝ) :
    LinearMap.BilinForm ℝ (Fin (n + 2) → ℝ) :=
  LinearMap.mk₂ ℝ
    (fun z y ↦ ∑ j, w j * z j * y j)
    (by
      intro z y v
      simp only [Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring)
    (by
      intro a z y
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring)
    (by
      intro z y v
      simp only [Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring)
    (by
      intro a z y
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring)

@[simp] theorem weightedProfileBilin_apply {n : ℕ}
    (w z y : Fin (n + 2) → ℝ) :
    weightedProfileBilin w z y = ∑ j, w j * z j * y j :=
  rfl

theorem weightedProfileBilin_symm {n : ℕ}
    (w z y : Fin (n + 2) → ℝ) :
    weightedProfileBilin w z y = weightedProfileBilin w y z := by
  rw [weightedProfileBilin_apply, weightedProfileBilin_apply]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem weightedProfileBilin_nonneg {n : ℕ}
    (w : Fin (n + 2) → ℝ) (hw : ∀ j, 0 ≤ w j)
    (z : Fin (n + 2) → ℝ) :
    0 ≤ weightedProfileBilin w z z := by
  rw [weightedProfileBilin_apply]
  apply Finset.sum_nonneg
  intro j hj
  nlinarith [hw j, sq_nonneg (z j)]

theorem weightedProfileBilin_eq_zero_iff {n : ℕ}
    (w : Fin (n + 2) → ℝ) (hw : ∀ j, 0 < w j)
    (z : Fin (n + 2) → ℝ) :
    weightedProfileBilin w z z = 0 ↔ z = 0 := by
  constructor
  · intro h
    rw [weightedProfileBilin_apply] at h
    funext j
    have hn : ∀ k ∈ (Finset.univ : Finset (Fin (n + 2))),
        0 ≤ w k * z k * z k := by
      intro k hk
      nlinarith [hw k, sq_nonneg (z k)]
    have hterm :=
      (Finset.sum_eq_zero_iff_of_nonneg hn).mp h j (Finset.mem_univ j)
    rcases mul_eq_zero.mp hterm with hwz | hz
    · rcases mul_eq_zero.mp hwz with hwi | hz
      · exact ((hw j).ne' hwi).elim
      · exact hz
    · exact hz
  · rintro rfl
    simp

/-- The zeroth scalar in the two-by-two affine normal matrix. -/
def weightedAffineS0 {n : ℕ} (w : Fin (n + 2) → ℝ) : ℝ :=
  ∑ j, w j

/-- The first scalar in the two-by-two affine normal matrix. -/
def weightedAffineS1 (t : ℕ → ℝ) {n : ℕ}
    (w : Fin (n + 2) → ℝ) : ℝ :=
  ∑ j, w j * t j.val

/-- The second scalar in the two-by-two affine normal matrix. -/
def weightedAffineS2 (t : ℕ → ℝ) {n : ℕ}
    (w : Fin (n + 2) → ℝ) : ℝ :=
  ∑ j, w j * (t j.val) ^ 2

/-- Determinant of the affine normal matrix. -/
def weightedAffineDet (t : ℕ → ℝ) {n : ℕ}
    (w : Fin (n + 2) → ℝ) : ℝ :=
  weightedAffineS0 w * weightedAffineS2 t w -
    (weightedAffineS1 t w) ^ 2

/-- Weighted zeroth moment as a linear functional. -/
def weightedAffineZ0LinearMap {n : ℕ} (w : Fin (n + 2) → ℝ) :
    (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ where
  toFun z := ∑ j, w j * z j
  map_add' := by
    intro z y
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  map_smul' := by
    intro a z
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

/-- Weighted first moment as a linear functional. -/
def weightedAffineZ1LinearMap (t : ℕ → ℝ) {n : ℕ}
    (w : Fin (n + 2) → ℝ) :
    (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ where
  toFun z := ∑ j, w j * t j.val * z j
  map_add' := by
    intro z y
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  map_smul' := by
    intro a z
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

def weightedAffineZ0 {n : ℕ} (w z : Fin (n + 2) → ℝ) : ℝ :=
  weightedAffineZ0LinearMap w z

def weightedAffineZ1 (t : ℕ → ℝ) {n : ℕ}
    (w z : Fin (n + 2) → ℝ) : ℝ :=
  weightedAffineZ1LinearMap t w z

/-- The constant coefficient of the weighted affine projection, as a linear map. -/
def weightedAffineCoeffALinearMap (t : ℕ → ℝ) {n : ℕ}
    (w : Fin (n + 2) → ℝ) :
    (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ :=
  (weightedAffineDet t w)⁻¹ •
    ((weightedAffineS2 t w) • weightedAffineZ0LinearMap w -
      (weightedAffineS1 t w) • weightedAffineZ1LinearMap t w)

/-- The slope coefficient of the weighted affine projection, as a linear map. -/
def weightedAffineCoeffBLinearMap (t : ℕ → ℝ) {n : ℕ}
    (w : Fin (n + 2) → ℝ) :
    (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ :=
  (weightedAffineDet t w)⁻¹ •
    ((weightedAffineS0 w) • weightedAffineZ1LinearMap t w -
      (weightedAffineS1 t w) • weightedAffineZ0LinearMap w)

def weightedAffineCoeffA (t : ℕ → ℝ) {n : ℕ}
    (w z : Fin (n + 2) → ℝ) : ℝ :=
  weightedAffineCoeffALinearMap t w z

def weightedAffineCoeffB (t : ℕ → ℝ) {n : ℕ}
    (w z : Fin (n + 2) → ℝ) : ℝ :=
  weightedAffineCoeffBLinearMap t w z

@[simp] theorem weightedAffineCoeffA_formula
    (t : ℕ → ℝ) {n : ℕ} (w z : Fin (n + 2) → ℝ) :
    weightedAffineCoeffA t w z =
      (weightedAffineS2 t w * weightedAffineZ0 w z -
        weightedAffineS1 t w * weightedAffineZ1 t w z) /
          weightedAffineDet t w := by
  simp [weightedAffineCoeffA, weightedAffineCoeffALinearMap,
    weightedAffineZ0, weightedAffineZ1, div_eq_mul_inv]
  ring

@[simp] theorem weightedAffineCoeffB_formula
    (t : ℕ → ℝ) {n : ℕ} (w z : Fin (n + 2) → ℝ) :
    weightedAffineCoeffB t w z =
      (weightedAffineS0 w * weightedAffineZ1 t w z -
        weightedAffineS1 t w * weightedAffineZ0 w z) /
          weightedAffineDet t w := by
  simp [weightedAffineCoeffB, weightedAffineCoeffBLinearMap,
    weightedAffineZ0, weightedAffineZ1, div_eq_mul_inv]
  ring

/-- Explicit weighted orthogonal projection onto the affine-profile range. -/
def weightedAffineProjection (t : ℕ → ℝ) (n : ℕ)
    (w : Fin (n + 2) → ℝ) :
    (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin (n + 2) → ℝ) :=
  (affineProfileMap t n).comp
    ((weightedAffineCoeffALinearMap t w).prod
      (weightedAffineCoeffBLinearMap t w))

@[simp] theorem weightedAffineProjection_apply
    (t : ℕ → ℝ) (n : ℕ) (w z : Fin (n + 2) → ℝ)
    (j : Fin (n + 2)) :
    weightedAffineProjection t n w z j =
      weightedAffineCoeffA t w z +
        weightedAffineCoeffB t w z * t j.val :=
  rfl

theorem weightedAffine_normalEquation_zero
    (t : ℕ → ℝ) {n : ℕ} (w z : Fin (n + 2) → ℝ)
    (hdet : weightedAffineDet t w ≠ 0) :
    weightedAffineS0 w * weightedAffineCoeffA t w z +
        weightedAffineS1 t w * weightedAffineCoeffB t w z =
      weightedAffineZ0 w z := by
  rw [weightedAffineCoeffA_formula, weightedAffineCoeffB_formula]
  field_simp [hdet]
  unfold weightedAffineDet
  ring

theorem weightedAffine_normalEquation_one
    (t : ℕ → ℝ) {n : ℕ} (w z : Fin (n + 2) → ℝ)
    (hdet : weightedAffineDet t w ≠ 0) :
    weightedAffineS1 t w * weightedAffineCoeffA t w z +
        weightedAffineS2 t w * weightedAffineCoeffB t w z =
      weightedAffineZ1 t w z := by
  rw [weightedAffineCoeffA_formula, weightedAffineCoeffB_formula]
  field_simp [hdet]
  unfold weightedAffineDet
  ring

theorem weightedAffineZ0_affineProfileMap
    (t : ℕ → ℝ) {n : ℕ} (w : Fin (n + 2) → ℝ) (p : ℝ × ℝ) :
    weightedAffineZ0 w (affineProfileMap t n p) =
      weightedAffineS0 w * p.1 + weightedAffineS1 t w * p.2 := by
  simp only [weightedAffineZ0, weightedAffineZ0LinearMap, weightedAffineS0,
    weightedAffineS1, affineProfileMap]
  calc
    (∑ j, w j * (p.1 + p.2 * t j.val)) =
        ∑ j, (w j * p.1 + w j * t j.val * p.2) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]

theorem weightedAffineZ1_affineProfileMap
    (t : ℕ → ℝ) {n : ℕ} (w : Fin (n + 2) → ℝ) (p : ℝ × ℝ) :
    weightedAffineZ1 t w (affineProfileMap t n p) =
      weightedAffineS1 t w * p.1 + weightedAffineS2 t w * p.2 := by
  simp only [weightedAffineZ1, weightedAffineZ1LinearMap, weightedAffineS1,
    weightedAffineS2, affineProfileMap]
  calc
    (∑ j, w j * t j.val * (p.1 + p.2 * t j.val)) =
        ∑ j, (w j * t j.val * p.1 + w j * (t j.val) ^ 2 * p.2) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]

theorem weightedAffineProjection_mem_range
    (t : ℕ → ℝ) (n : ℕ) (w z : Fin (n + 2) → ℝ) :
    weightedAffineProjection t n w z ∈
      LinearMap.range (affineProfileMap t n) := by
  rw [LinearMap.mem_range]
  exact ⟨(weightedAffineCoeffA t w z, weightedAffineCoeffB t w z), rfl⟩

theorem weightedAffineProjection_eq_self_of_mem_range
    (t : ℕ → ℝ) (n : ℕ) (w : Fin (n + 2) → ℝ)
    (hdet : weightedAffineDet t w ≠ 0)
    {z : Fin (n + 2) → ℝ}
    (hz : z ∈ LinearMap.range (affineProfileMap t n)) :
    weightedAffineProjection t n w z = z := by
  rw [LinearMap.mem_range] at hz
  rcases hz with ⟨p, rfl⟩
  have ha :
      weightedAffineCoeffA t w (affineProfileMap t n p) = p.1 := by
    rw [weightedAffineCoeffA_formula, weightedAffineZ0_affineProfileMap,
      weightedAffineZ1_affineProfileMap]
    field_simp [hdet]
    unfold weightedAffineDet
    ring
  have hb :
      weightedAffineCoeffB t w (affineProfileMap t n p) = p.2 := by
    rw [weightedAffineCoeffB_formula, weightedAffineZ0_affineProfileMap,
      weightedAffineZ1_affineProfileMap]
    field_simp [hdet]
    unfold weightedAffineDet
    ring
  funext j
  change weightedAffineCoeffA t w (affineProfileMap t n p) +
      weightedAffineCoeffB t w (affineProfileMap t n p) * t j.val =
    p.1 + p.2 * t j.val
  rw [ha, hb]

theorem weightedAffineProjection_idempotent
    (t : ℕ → ℝ) (n : ℕ) (w : Fin (n + 2) → ℝ)
    (hdet : weightedAffineDet t w ≠ 0) :
    (weightedAffineProjection t n w).comp (weightedAffineProjection t n w) =
      weightedAffineProjection t n w := by
  apply LinearMap.ext
  intro z
  exact weightedAffineProjection_eq_self_of_mem_range t n w hdet
    (weightedAffineProjection_mem_range t n w z)

theorem weightedProfileBilin_affine_right
    (t : ℕ → ℝ) {n : ℕ} (w z : Fin (n + 2) → ℝ) (p : ℝ × ℝ) :
    weightedProfileBilin w z (affineProfileMap t n p) =
      p.1 * weightedAffineZ0 w z + p.2 * weightedAffineZ1 t w z := by
  change (∑ j, w j * z j * (p.1 + p.2 * t j.val)) =
    p.1 * (∑ j, w j * z j) +
      p.2 * (∑ j, w j * t j.val * z j)
  calc
    (∑ j, w j * z j * (p.1 + p.2 * t j.val)) =
        ∑ j, (p.1 * (w j * z j) + p.2 * (w j * t j.val * z j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

theorem weightedAffineResidual_orthogonal_affineRange
    (t : ℕ → ℝ) (n : ℕ) (w z a : Fin (n + 2) → ℝ)
    (hdet : weightedAffineDet t w ≠ 0)
    (ha : a ∈ LinearMap.range (affineProfileMap t n)) :
    weightedProfileBilin w (z - weightedAffineProjection t n w z) a = 0 := by
  rw [LinearMap.mem_range] at ha
  rcases ha with ⟨p, rfl⟩
  rw [weightedProfileBilin_affine_right]
  have h0 := weightedAffine_normalEquation_zero t w z hdet
  have h1 := weightedAffine_normalEquation_one t w z hdet
  have hz0 :
      weightedAffineZ0 w (z - weightedAffineProjection t n w z) = 0 := by
    change weightedAffineZ0LinearMap w
      (z - weightedAffineProjection t n w z) = 0
    rw [map_sub]
    change weightedAffineZ0 w z -
      weightedAffineZ0 w (affineProfileMap t n
        (weightedAffineCoeffA t w z, weightedAffineCoeffB t w z)) = 0
    rw [weightedAffineZ0_affineProfileMap]
    exact sub_eq_zero.mpr h0.symm
  have hz1 :
      weightedAffineZ1 t w (z - weightedAffineProjection t n w z) = 0 := by
    change weightedAffineZ1LinearMap t w
      (z - weightedAffineProjection t n w z) = 0
    rw [map_sub]
    change weightedAffineZ1 t w z -
      weightedAffineZ1 t w (affineProfileMap t n
        (weightedAffineCoeffA t w z, weightedAffineCoeffB t w z)) = 0
    rw [weightedAffineZ1_affineProfileMap]
    exact sub_eq_zero.mpr h1.symm
  rw [hz0, hz1]
  ring

/-- Positive weights and one nonzero adjacent gap make the normal determinant
strictly positive. -/
theorem weightedAffineDet_pos
    (t : ℕ → ℝ) (n : ℕ) (w : Fin (n + 2) → ℝ)
    (hgap : ∀ i ≤ n, gap t i ≠ 0)
    (hw : ∀ j, 0 < w j) :
    0 < weightedAffineDet t w := by
  apply RiemannResearch.LinearAlgebra.affine_normal_det_positive
    (Finset.univ : Finset (Fin (n + 2))) w (fun j ↦ t j.val)
  · intro i hi
    exact (hw i).le
  · let i0 : Fin (n + 2) := ⟨0, by omega⟩
    let i1 : Fin (n + 2) := ⟨1, by omega⟩
    refine ⟨i0, Finset.mem_univ i0, i1, Finset.mem_univ i1,
      hw i0, hw i1, ?_⟩
    intro heq
    have hg := hgap 0 (Nat.zero_le n)
    exact hg (by
      simpa [gap, i0, i1] using sub_eq_zero.mpr heq.symm)

/-- Remove the weighted affine component from the anchored prefix section. -/
def weightedOrthogonalPrefix (t : ℕ → ℝ) (n : ℕ)
    (w : Fin (n + 2) → ℝ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin (n + 2) → ℝ) :=
  (LinearMap.id - weightedAffineProjection t n w).comp
    (profilePrefixLinearMap (finiteGapWindow n t))

@[simp] theorem weightedOrthogonalPrefix_apply
    (t : ℕ → ℝ) (n : ℕ) (w : Fin (n + 2) → ℝ)
    (c : Fin n → ℝ) :
    weightedOrthogonalPrefix t n w c =
      profilePrefixLinearMap (finiteGapWindow n t) c -
        weightedAffineProjection t n w
          (profilePrefixLinearMap (finiteGapWindow n t) c) :=
  rfl

theorem finiteCurvatureMap_comp_weightedAffineProjection
    (t : ℕ → ℝ) (n : ℕ) (w : Fin (n + 2) → ℝ)
    (hgap : ∀ i ≤ n, gap t i ≠ 0) :
    (finiteCurvatureMap (finiteGapWindow n t)).comp
        (weightedAffineProjection t n w) = 0 := by
  apply LinearMap.ext
  intro z
  change finiteCurvatureMap (finiteGapWindow n t)
      (weightedAffineProjection t n w z) = 0
  have hp := weightedAffineProjection_mem_range t n w z
  rw [← ker_finiteCurvatureMap_eq_range_affineProfileMap t n hgap] at hp
  exact LinearMap.mem_ker.mp hp

theorem finiteCurvatureMap_comp_weightedOrthogonalPrefix
    (t : ℕ → ℝ) (n : ℕ) (w : Fin (n + 2) → ℝ)
    (hgap : ∀ i ≤ n, gap t i ≠ 0) :
    (finiteCurvatureMap (finiteGapWindow n t)).comp
        (weightedOrthogonalPrefix t n w) = LinearMap.id := by
  have hg : ∀ j : Fin (n + 1), finiteGapWindow n t j ≠ 0 := by
    intro j
    exact hgap j.val (by omega)
  apply LinearMap.ext
  intro c
  change finiteCurvatureMap (finiteGapWindow n t)
      (profilePrefixLinearMap (finiteGapWindow n t) c -
        weightedAffineProjection t n w
          (profilePrefixLinearMap (finiteGapWindow n t) c)) = c
  rw [map_sub]
  have hp :
      finiteCurvatureMap (finiteGapWindow n t)
        (weightedAffineProjection t n w
          (profilePrefixLinearMap (finiteGapWindow n t) c)) = 0 := by
    have hcomp := finiteCurvatureMap_comp_weightedAffineProjection
      t n w hgap
    exact LinearMap.congr_fun hcomp
      (profilePrefixLinearMap (finiteGapWindow n t) c)
  rw [hp, sub_zero]
  exact finiteCurvature_profilePrefix (finiteGapWindow n t) hg c

theorem weightedOrthogonalPrefix_rightInverse
    (t : ℕ → ℝ) (n : ℕ) (w : Fin (n + 2) → ℝ)
    (hgap : ∀ i ≤ n, gap t i ≠ 0) :
    Function.RightInverse (weightedOrthogonalPrefix t n w)
      (finiteCurvatureMap (finiteGapWindow n t)) := by
  intro c
  have hcomp := finiteCurvatureMap_comp_weightedOrthogonalPrefix
    t n w hgap
  exact LinearMap.congr_fun hcomp c

theorem weightedOrthogonalPrefix_orthogonal_affineRange
    (t : ℕ → ℝ) (n : ℕ) (w : Fin (n + 2) → ℝ)
    (hgap : ∀ i ≤ n, gap t i ≠ 0)
    (hw : ∀ j, 0 < w j)
    (c : Fin n → ℝ) (a : Fin (n + 2) → ℝ)
    (ha : a ∈ LinearMap.range (affineProfileMap t n)) :
    weightedProfileBilin w (weightedOrthogonalPrefix t n w c) a = 0 := by
  change weightedProfileBilin w
    (profilePrefixLinearMap (finiteGapWindow n t) c -
      weightedAffineProjection t n w
        (profilePrefixLinearMap (finiteGapWindow n t) c)) a = 0
  exact weightedAffineResidual_orthogonal_affineRange t n w
    (profilePrefixLinearMap (finiteGapWindow n t) c) a
    (weightedAffineDet_pos t n w hgap hw).ne' ha

theorem sameFiniteCurvature_sub_mem_affineRange
    (t : ℕ → ℝ) (n : ℕ)
    (hgap : ∀ i ≤ n, gap t i ≠ 0)
    {z y : Fin (n + 2) → ℝ}
    (hzy : finiteCurvatureMap (finiteGapWindow n t) z =
      finiteCurvatureMap (finiteGapWindow n t) y) :
    z - y ∈ LinearMap.range (affineProfileMap t n) :=
  (finiteCurvatureMap_eq_iff_sub_mem_affineProfileRange
    t n hgap z y).mp hzy

open RiemannResearch.LinearAlgebra

/-- Pull back the weighted profile form along the orthogonal prefix section. -/
def weightedCurvatureGreenBilin (t : ℕ → ℝ) (n : ℕ)
    (w : Fin (n + 2) → ℝ) :
    LinearMap.BilinForm ℝ (Fin n → ℝ) :=
  LinearMap.mk₂ ℝ
    (fun c d ↦ weightedProfileBilin w
      (weightedOrthogonalPrefix t n w c)
      (weightedOrthogonalPrefix t n w d))
    (by
      intro c d e
      rw [map_add, map_add, LinearMap.add_apply])
    (by
      intro a c d
      rw [map_smul, map_smul, LinearMap.smul_apply])
    (by
      intro c d e
      rw [map_add, map_add])
    (by
      intro a c d
      rw [map_smul, map_smul])

@[simp] theorem weightedCurvatureGreenBilin_apply
    (t : ℕ → ℝ) (n : ℕ) (w : Fin (n + 2) → ℝ)
    (c d : Fin n → ℝ) :
    weightedCurvatureGreenBilin t n w c d =
      weightedProfileBilin w
        (weightedOrthogonalPrefix t n w c)
        (weightedOrthogonalPrefix t n w d) :=
  rfl

/-- The weighted-orthogonal prefix section is dual to finite curvature for
the pulled-back curvature form. -/
theorem weightedOrthogonalPrefix_duality
    (t : ℕ → ℝ) (n : ℕ) (w : Fin (n + 2) → ℝ)
    (hgap : ∀ i ≤ n, gap t i ≠ 0)
    (hw : ∀ j, 0 < w j)
    (c : Fin n → ℝ) (z : Fin (n + 2) → ℝ) :
    weightedProfileBilin w (weightedOrthogonalPrefix t n w c) z =
      weightedCurvatureGreenBilin t n w c
        (finiteCurvatureMap (finiteGapWindow n t) z) := by
  let D := finiteCurvatureMap (finiteGapWindow n t)
  let R := weightedOrthogonalPrefix t n w
  have hR : Function.RightInverse R D :=
    weightedOrthogonalPrefix_rightInverse t n w hgap
  have hk : z - R (D z) ∈ LinearMap.ker D := by
    rw [LinearMap.mem_ker, map_sub, hR (D z), sub_self]
  have ha : z - R (D z) ∈
      LinearMap.range (affineProfileMap t n) := by
    rw [← ker_finiteCurvatureMap_eq_range_affineProfileMap t n hgap]
    exact hk
  have ho :
      weightedProfileBilin w (R c) (z - R (D z)) = 0 :=
    weightedOrthogonalPrefix_orthogonal_affineRange
      t n w hgap hw c _ ha
  have hz : R (D z) + (z - R (D z)) = z := by abel
  calc
    weightedProfileBilin w (R c) z =
        weightedProfileBilin w (R c)
          (R (D z) + (z - R (D z))) := by rw [hz]
    _ = weightedProfileBilin w (R c) (R (D z)) +
        weightedProfileBilin w (R c) (z - R (D z)) := by
          rw [map_add]
    _ = weightedProfileBilin w (R c) (R (D z)) := by rw [ho, add_zero]
    _ = weightedCurvatureGreenBilin t n w c (D z) := rfl

/-- The concrete weighted Green projection of a finite profile. -/
def weightedOrthogonalGreenProjection
    (t : ℕ → ℝ) (n : ℕ) (w : Fin (n + 2) → ℝ) :
    (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin (n + 2) → ℝ) :=
  dualGreenProjection
    (finiteCurvatureMap (finiteGapWindow n t))
    (weightedOrthogonalPrefix t n w)
    LinearMap.id

@[simp] theorem weightedOrthogonalGreenProjection_apply
    (t : ℕ → ℝ) (n : ℕ) (w : Fin (n + 2) → ℝ)
    (z : Fin (n + 2) → ℝ) :
    weightedOrthogonalGreenProjection t n w z =
      weightedOrthogonalPrefix t n w
        (finiteCurvatureMap (finiteGapWindow n t) z) :=
  rfl

theorem weightedOrthogonalGreen_rightInverse
    (t : ℕ → ℝ) (n : ℕ) (w : Fin (n + 2) → ℝ)
    (hgap : ∀ i ≤ n, gap t i ≠ 0) :
    Function.RightInverse
      (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
      (greenOperator
        (finiteCurvatureMap (finiteGapWindow n t))
        (weightedOrthogonalPrefix t n w)) := by
  intro c
  simpa [greenOperator] using
    weightedOrthogonalPrefix_rightInverse t n w hgap c

theorem weightedOrthogonalGreen_mapsTo
    (t : ℕ → ℝ) (n : ℕ) (w : Fin (n + 2) → ℝ)
    (hgap : ∀ i ≤ n, gap t i ≠ 0)
    (z : Fin (n + 2) → ℝ) :
    finiteCurvatureMap (finiteGapWindow n t)
        (weightedOrthogonalGreenProjection t n w z) =
      finiteCurvatureMap (finiteGapWindow n t) z := by
  exact dualGreenProjection_mapsTo _ _ _
    (weightedOrthogonalGreen_rightInverse t n w hgap) z

theorem weightedOrthogonalGreen_residual_mem_affineRange
    (t : ℕ → ℝ) (n : ℕ) (w : Fin (n + 2) → ℝ)
    (hgap : ∀ i ≤ n, gap t i ≠ 0)
    (z : Fin (n + 2) → ℝ) :
    z - weightedOrthogonalGreenProjection t n w z ∈
      LinearMap.range (affineProfileMap t n) := by
  rw [← ker_finiteCurvatureMap_eq_range_affineProfileMap t n hgap]
  exact dualGreenProjection_residual_mem_ker _ _ _
    (weightedOrthogonalGreen_rightInverse t n w hgap) z

/-- Exact weighted Pythagoras on every finite-curvature fiber. -/
theorem weightedOrthogonalGreen_pythagoras
    (t : ℕ → ℝ) (n : ℕ) (w : Fin (n + 2) → ℝ)
    (hgap : ∀ i ≤ n, gap t i ≠ 0)
    (hw : ∀ j, 0 < w j)
    {z x : Fin (n + 2) → ℝ}
    (hx : finiteCurvatureMap (finiteGapWindow n t) x =
      finiteCurvatureMap (finiteGapWindow n t) z) :
    weightedProfileBilin w x x =
      weightedProfileBilin w
          (weightedOrthogonalGreenProjection t n w z)
          (weightedOrthogonalGreenProjection t n w z) +
        weightedProfileBilin w
          (x - weightedOrthogonalGreenProjection t n w z)
          (x - weightedOrthogonalGreenProjection t n w z) := by
  simpa [weightedOrthogonalGreenProjection, weightedCurvatureGreenBilin] using
    dualGreen_pythagoras
      (weightedProfileBilin w)
      (weightedCurvatureGreenBilin t n w)
      (finiteCurvatureMap (finiteGapWindow n t))
      (weightedOrthogonalPrefix t n w)
      (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
      (weightedOrthogonalGreen_rightInverse t n w hgap)
      (weightedOrthogonalPrefix_duality t n w hgap hw)
      (weightedProfileBilin_symm w)
      hx

/-- The weighted Green projection minimizes energy on its curvature fiber. -/
theorem weightedOrthogonalGreen_minimizes
    (t : ℕ → ℝ) (n : ℕ) (w : Fin (n + 2) → ℝ)
    (hgap : ∀ i ≤ n, gap t i ≠ 0)
    (hw : ∀ j, 0 < w j)
    {z x : Fin (n + 2) → ℝ}
    (hx : finiteCurvatureMap (finiteGapWindow n t) x =
      finiteCurvatureMap (finiteGapWindow n t) z) :
    weightedProfileBilin w
        (weightedOrthogonalGreenProjection t n w z)
        (weightedOrthogonalGreenProjection t n w z) ≤
      weightedProfileBilin w x x := by
  simpa [weightedOrthogonalGreenProjection, weightedCurvatureGreenBilin] using
    dualGreen_minimizes
      (weightedProfileBilin w)
      (weightedCurvatureGreenBilin t n w)
      (finiteCurvatureMap (finiteGapWindow n t))
      (weightedOrthogonalPrefix t n w)
      (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
      (weightedOrthogonalGreen_rightInverse t n w hgap)
      (weightedOrthogonalPrefix_duality t n w hgap hw)
      (weightedProfileBilin_symm w)
      (weightedProfileBilin_nonneg w (fun j ↦ (hw j).le))
      hx

/-- Equality in the weighted minimum forces the unique Green representative. -/
theorem weightedOrthogonalGreen_unique
    (t : ℕ → ℝ) (n : ℕ) (w : Fin (n + 2) → ℝ)
    (hgap : ∀ i ≤ n, gap t i ≠ 0)
    (hw : ∀ j, 0 < w j)
    {z x : Fin (n + 2) → ℝ}
    (hx : finiteCurvatureMap (finiteGapWindow n t) x =
      finiteCurvatureMap (finiteGapWindow n t) z)
    (henergy :
      weightedProfileBilin w x x =
        weightedProfileBilin w
          (weightedOrthogonalGreenProjection t n w z)
          (weightedOrthogonalGreenProjection t n w z)) :
    x = weightedOrthogonalGreenProjection t n w z := by
  have hp := weightedOrthogonalGreen_pythagoras t n w hgap hw hx
  have hzero :
      weightedProfileBilin w
          (x - weightedOrthogonalGreenProjection t n w z)
          (x - weightedOrthogonalGreenProjection t n w z) = 0 := by
    linarith
  exact sub_eq_zero.mp
    ((weightedProfileBilin_eq_zero_iff w hw _).mp hzero)

/-- The orthogonal prefix lift is the unique minimum-energy representative of
each prescribed finite curvature vector. -/
theorem weightedOrthogonalPrefix_unique_minimizer
    (t : ℕ → ℝ) (n : ℕ) (w : Fin (n + 2) → ℝ)
    (hgap : ∀ i ≤ n, gap t i ≠ 0)
    (hw : ∀ j, 0 < w j)
    (c : Fin n → ℝ) (z : Fin (n + 2) → ℝ)
    (hz : finiteCurvatureMap (finiteGapWindow n t) z = c) :
    weightedProfileBilin w
        (weightedOrthogonalPrefix t n w c)
        (weightedOrthogonalPrefix t n w c) ≤
      weightedProfileBilin w z z ∧
    (weightedProfileBilin w z z =
        weightedProfileBilin w
          (weightedOrthogonalPrefix t n w c)
          (weightedOrthogonalPrefix t n w c) ↔
      z = weightedOrthogonalPrefix t n w c) := by
  have hmin := weightedOrthogonalGreen_minimizes
    t n w hgap hw (z := z) (x := z) rfl
  have hproj :
      weightedOrthogonalGreenProjection t n w z =
        weightedOrthogonalPrefix t n w c := by
    rw [weightedOrthogonalGreenProjection_apply, hz]
  constructor
  · simpa [hproj] using hmin
  · constructor
    · intro heq
      have hunique := weightedOrthogonalGreen_unique
        t n w hgap hw (z := z) (x := z) rfl
          (by simpa [hproj] using heq)
      simpa [hproj] using hunique
    · rintro rfl
      rfl

end

end RiemannResearch.RH.PrimeGapCurvature
