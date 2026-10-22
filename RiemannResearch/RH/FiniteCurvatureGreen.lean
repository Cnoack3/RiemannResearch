/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.PrimeGapCurvature

/-!
# Finite adjacent-curvature quotient and prefix section

This module upgrades the pointwise adjacent-curvature identities to a concrete
linear map between finite coordinate spaces. It identifies the kernel exactly
with affine profiles and constructs an explicit linear right inverse by two
prefix sums.

Source: user-provided argument,
RH_Proof_First_Continuation_2026-09-04.md, Sections 1 and 2. The source
supports the statements and proof strategy. These finite quotient results do
not identify the resulting energy with a Weil form and do not prove RH.
-/

namespace RiemannResearch.RH.PrimeGapCurvature

noncomputable section

open scoped BigOperators

/-- The first n+1 adjacent gaps of a global coordinate sequence. -/
def finiteGapWindow (n : ℕ) (t : ℕ → ℝ) : Fin (n + 1) → ℝ :=
  fun j ↦ gap t j.val

/-- The first n+2 values of a global profile. -/
def finiteProfileWindow (n : ℕ) (z : ℕ → ℝ) : Fin (n + 2) → ℝ :=
  fun k ↦ z k.val

/-- Extend a finite profile by zero outside its defining window. -/
def finiteProfileExtension {n : ℕ} (z : Fin (n + 2) → ℝ) : ℕ → ℝ :=
  fun k ↦ if hk : k < n + 2 then z ⟨k, hk⟩ else 0

@[simp] theorem finiteProfileWindow_extension {n : ℕ}
    (z : Fin (n + 2) → ℝ) :
    finiteProfileWindow n (finiteProfileExtension z) = z := by
  funext k
  simp [finiteProfileWindow, finiteProfileExtension, k.isLt]

/-- Adjacent slope on a finite gap/profile window. -/
def finiteAdjacentSlope {n : ℕ} (g : Fin (n + 1) → ℝ)
    (z : Fin (n + 2) → ℝ) (j : Fin (n + 1)) : ℝ :=
  (z j.succ - z j.castSucc) / g j

/-- Adjacent curvature on a finite gap/profile window. -/
def finiteCurvature {n : ℕ} (g : Fin (n + 1) → ℝ)
    (z : Fin (n + 2) → ℝ) (i : Fin n) : ℝ :=
  finiteAdjacentSlope g z i.succ - finiteAdjacentSlope g z i.castSucc

/-- Restricting global data to a finite window preserves adjacent curvature exactly. -/
theorem finiteCurvature_window {n : ℕ} (t z : ℕ → ℝ) (i : Fin n) :
    finiteCurvature (finiteGapWindow n t) (finiteProfileWindow n z) i =
      adjacentCurvature t z i.val := by
  rfl

/-- Extending a finite profile and then taking global adjacent curvature gives
that same finite curvature coordinate. -/
theorem finiteCurvature_extension {n : ℕ} (t : ℕ → ℝ)
    (z : Fin (n + 2) → ℝ) (i : Fin n) :
    finiteCurvature (finiteGapWindow n t) z i =
      adjacentCurvature t (finiteProfileExtension z) i.val := by
  rw [← finiteCurvature_window (n := n) t (finiteProfileExtension z) i]
  rw [finiteProfileWindow_extension]

/-- Finite adjacent curvature as a linear map from profiles to curvature data. -/
def finiteCurvatureMap {n : ℕ} (g : Fin (n + 1) → ℝ) :
    (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun z := finiteCurvature g z
  map_add' := by
    intro z w
    funext i
    simp [finiteCurvature, finiteAdjacentSlope]
    ring
  map_smul' := by
    intro a z
    funext i
    simp [finiteCurvature, finiteAdjacentSlope]
    ring

@[simp] theorem finiteCurvatureMap_apply {n : ℕ}
    (g : Fin (n + 1) → ℝ) (z : Fin (n + 2) → ℝ) (i : Fin n) :
    finiteCurvatureMap g z i = finiteCurvature g z i :=
  rfl

/-- The affine two-parameter family on the first n+2 coordinates of t. -/
def affineProfileMap (t : ℕ → ℝ) (n : ℕ) :
    (ℝ × ℝ) →ₗ[ℝ] (Fin (n + 2) → ℝ) where
  toFun p i := p.1 + p.2 * t i.val
  map_add' := by
    intro p q
    funext i
    simp
    ring
  map_smul' := by
    intro a p
    funext i
    simp
    ring

/-- With nonzero adjacent gaps, the kernel of finite curvature is exactly the
space of affine profiles. -/
theorem ker_finiteCurvatureMap_eq_range_affineProfileMap
    (t : ℕ → ℝ) (n : ℕ)
    (hgap : ∀ i ≤ n, gap t i ≠ 0) :
    LinearMap.ker (finiteCurvatureMap (finiteGapWindow n t)) =
      LinearMap.range (affineProfileMap t n) := by
  ext z
  constructor
  · intro hz
    have hzmap :
        finiteCurvatureMap (finiteGapWindow n t) z = 0 :=
      (LinearMap.mem_ker).mp hz
    have hcurv :
        ∀ i < n, adjacentCurvature t (finiteProfileExtension z) i = 0 := by
      intro i hi
      let fi : Fin n := ⟨i, hi⟩
      calc
        adjacentCurvature t (finiteProfileExtension z) i =
            finiteCurvature (finiteGapWindow n t) z fi := by
              exact (finiteCurvature_extension t z fi).symm
        _ = 0 := by
          have hpoint := congrFun hzmap fi
          simpa [finiteCurvatureMap] using hpoint
    obtain ⟨a, b, hab⟩ :=
      (curvature_eq_zero_iff_exists_affine_on_range
        t (finiteProfileExtension z) n hgap).mp hcurv
    rw [LinearMap.mem_range]
    refine ⟨(a, b), ?_⟩
    funext i
    have hi : i.val ≤ n + 1 := by omega
    have heq := hab i.val hi
    simpa [affineProfileMap, finiteProfileExtension, i.isLt] using heq.symm
  · intro hz
    rw [LinearMap.mem_range] at hz
    obtain ⟨p, rfl⟩ := hz
    rw [LinearMap.mem_ker]
    funext i
    have hcurv :
        ∀ k < n,
          adjacentCurvature t
            (finiteProfileExtension (affineProfileMap t n p)) k = 0 := by
      apply (curvature_eq_zero_iff_exists_affine_on_range
        t (finiteProfileExtension (affineProfileMap t n p)) n hgap).mpr
      refine ⟨p.1, p.2, ?_⟩
      intro k hk
      have hk' : k < n + 2 := by omega
      simp [finiteProfileExtension, affineProfileMap, hk']
    calc
      finiteCurvatureMap (finiteGapWindow n t) (affineProfileMap t n p) i =
          adjacentCurvature t
            (finiteProfileExtension (affineProfileMap t n p)) i.val := by
              exact finiteCurvature_extension t (affineProfileMap t n p) i
      _ = 0 := hcurv i.val i.isLt
      _ = (0 : Fin n → ℝ) i := rfl

/-- Two profiles have the same finite curvature exactly when their difference
lies in the affine-profile range. -/
theorem finiteCurvatureMap_eq_iff_sub_mem_affineProfileRange
    (t : ℕ → ℝ) (n : ℕ)
    (hgap : ∀ i ≤ n, gap t i ≠ 0)
    (z w : Fin (n + 2) → ℝ) :
    finiteCurvatureMap (finiteGapWindow n t) z =
        finiteCurvatureMap (finiteGapWindow n t) w ↔
      z - w ∈ LinearMap.range (affineProfileMap t n) := by
  rw [← ker_finiteCurvatureMap_eq_range_affineProfileMap t n hgap]
  constructor
  · intro h
    rw [LinearMap.mem_ker, map_sub, h, sub_self]
  · intro h
    have hz := LinearMap.mem_ker.mp h
    rw [map_sub, sub_eq_zero] at hz
    exact hz

/-- Coordinate form: equal finite curvature is equivalent to an affine
pointwise difference. -/
theorem finiteCurvatureMap_eq_iff_exists_affine_sub
    (t : ℕ → ℝ) (n : ℕ)
    (hgap : ∀ i ≤ n, gap t i ≠ 0)
    (z w : Fin (n + 2) → ℝ) :
    finiteCurvatureMap (finiteGapWindow n t) z =
        finiteCurvatureMap (finiteGapWindow n t) w ↔
      ∃ a b : ℝ, ∀ i, z i - w i = a + b * t i.val := by
  rw [finiteCurvatureMap_eq_iff_sub_mem_affineProfileRange t n hgap]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.1, p.2, ?_⟩
    intro i
    have hpoint := congrFun hp i
    simpa [affineProfileMap] using hpoint.symm
  · rintro ⟨a, b, hab⟩
    rw [LinearMap.mem_range]
    refine ⟨(a, b), ?_⟩
    funext i
    simpa [affineProfileMap] using (hab i).symm

/-- Read a finite curvature vector at a natural index, returning zero outside. -/
def finiteCurvatureGet {n : ℕ} (c : Fin n → ℝ) (i : ℕ) : ℝ :=
  if hi : i < n then c ⟨i, hi⟩ else 0

/-- The prefix sum of prescribed curvatures, normalized to have initial slope zero. -/
def slopePrefix {n : ℕ} (c : Fin n → ℝ) (j : Fin (n + 1)) : ℝ :=
  ∑ i ∈ Finset.range j.val, finiteCurvatureGet c i

@[simp] theorem slopePrefix_zero {n : ℕ} (c : Fin n → ℝ) :
    slopePrefix c (0 : Fin (n + 1)) = 0 := by
  simp [slopePrefix]

theorem slopePrefix_succ_sub {n : ℕ} (c : Fin n → ℝ) (i : Fin n) :
    slopePrefix c i.succ - slopePrefix c i.castSucc = c i := by
  simp [slopePrefix, Finset.sum_range_succ, finiteCurvatureGet, i.isLt]

/-- Gap-weighted prefix-slope data at a natural index. -/
def weightedSlopeGet {n : ℕ} (g : Fin (n + 1) → ℝ)
    (c : Fin n → ℝ) (j : ℕ) : ℝ :=
  if hj : j < n + 1 then g ⟨j, hj⟩ * slopePrefix c ⟨j, hj⟩ else 0

/-- The prefix-integrated profile with initial value and initial slope zero. -/
def profilePrefix {n : ℕ} (g : Fin (n + 1) → ℝ)
    (c : Fin n → ℝ) (k : Fin (n + 2)) : ℝ :=
  ∑ j ∈ Finset.range k.val, weightedSlopeGet g c j

@[simp] theorem profilePrefix_zero {n : ℕ}
    (g : Fin (n + 1) → ℝ) (c : Fin n → ℝ) :
    profilePrefix g c (0 : Fin (n + 2)) = 0 := by
  simp [profilePrefix]

theorem profilePrefix_succ_sub {n : ℕ}
    (g : Fin (n + 1) → ℝ) (c : Fin n → ℝ) (j : Fin (n + 1)) :
    profilePrefix g c j.succ - profilePrefix g c j.castSucc =
      g j * slopePrefix c j := by
  unfold profilePrefix
  change (∑ k ∈ Finset.range (j.val + 1), weightedSlopeGet g c k) -
    (∑ k ∈ Finset.range j.val, weightedSlopeGet g c k) =
      g j * slopePrefix c j
  rw [Finset.sum_range_succ]
  rw [weightedSlopeGet]
  simp only [dif_pos j.isLt]
  ring

theorem finiteAdjacentSlope_profilePrefix {n : ℕ}
    (g : Fin (n + 1) → ℝ) (hg : ∀ j, g j ≠ 0)
    (c : Fin n → ℝ) (j : Fin (n + 1)) :
    finiteAdjacentSlope g (profilePrefix g c) j = slopePrefix c j := by
  rw [finiteAdjacentSlope, profilePrefix_succ_sub]
  exact mul_div_cancel_left₀ (slopePrefix c j) (hg j)

theorem finiteCurvature_profilePrefix {n : ℕ}
    (g : Fin (n + 1) → ℝ) (hg : ∀ j, g j ≠ 0)
    (c : Fin n → ℝ) :
    finiteCurvature g (profilePrefix g c) = c := by
  funext i
  rw [finiteCurvature, finiteAdjacentSlope_profilePrefix g hg,
    finiteAdjacentSlope_profilePrefix g hg, slopePrefix_succ_sub]

lemma finiteCurvatureGet_add {n : ℕ} (c d : Fin n → ℝ) (i : ℕ) :
    finiteCurvatureGet (c + d) i =
      finiteCurvatureGet c i + finiteCurvatureGet d i := by
  by_cases hi : i < n
  · simp [finiteCurvatureGet, hi]
  · simp [finiteCurvatureGet, hi]

lemma finiteCurvatureGet_smul {n : ℕ} (a : ℝ)
    (c : Fin n → ℝ) (i : ℕ) :
    finiteCurvatureGet (a • c) i = a * finiteCurvatureGet c i := by
  by_cases hi : i < n
  · simp [finiteCurvatureGet, hi]
  · simp [finiteCurvatureGet, hi]

lemma slopePrefix_add {n : ℕ} (c d : Fin n → ℝ) (j : Fin (n + 1)) :
    slopePrefix (c + d) j = slopePrefix c j + slopePrefix d j := by
  simp [slopePrefix, finiteCurvatureGet_add, Finset.sum_add_distrib]

lemma slopePrefix_smul {n : ℕ} (a : ℝ)
    (c : Fin n → ℝ) (j : Fin (n + 1)) :
    slopePrefix (a • c) j = a * slopePrefix c j := by
  simp [slopePrefix, finiteCurvatureGet_smul, Finset.mul_sum]

lemma weightedSlopeGet_add {n : ℕ} (g : Fin (n + 1) → ℝ)
    (c d : Fin n → ℝ) (j : ℕ) :
    weightedSlopeGet g (c + d) j =
      weightedSlopeGet g c j + weightedSlopeGet g d j := by
  by_cases hj : j < n + 1
  · simp [weightedSlopeGet, hj, slopePrefix_add, mul_add]
  · simp [weightedSlopeGet, hj]

lemma weightedSlopeGet_smul {n : ℕ} (g : Fin (n + 1) → ℝ)
    (a : ℝ) (c : Fin n → ℝ) (j : ℕ) :
    weightedSlopeGet g (a • c) j =
      a * weightedSlopeGet g c j := by
  by_cases hj : j < n + 1
  · simp [weightedSlopeGet, hj, slopePrefix_smul]
    ring
  · simp [weightedSlopeGet, hj]

lemma profilePrefix_add {n : ℕ} (g : Fin (n + 1) → ℝ)
    (c d : Fin n → ℝ) (k : Fin (n + 2)) :
    profilePrefix g (c + d) k =
      profilePrefix g c k + profilePrefix g d k := by
  simp [profilePrefix, weightedSlopeGet_add, Finset.sum_add_distrib]

lemma profilePrefix_smul {n : ℕ} (g : Fin (n + 1) → ℝ)
    (a : ℝ) (c : Fin n → ℝ) (k : Fin (n + 2)) :
    profilePrefix g (a • c) k = a * profilePrefix g c k := by
  simp [profilePrefix, weightedSlopeGet_smul, Finset.mul_sum]

/-- The normalized prefix construction as a linear section of curvature. -/
def profilePrefixLinearMap {n : ℕ} (g : Fin (n + 1) → ℝ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin (n + 2) → ℝ) where
  toFun c := profilePrefix g c
  map_add' := by
    intro c d
    funext k
    exact profilePrefix_add g c d k
  map_smul' := by
    intro a c
    funext k
    exact profilePrefix_smul g a c k

@[simp] theorem profilePrefixLinearMap_apply {n : ℕ}
    (g : Fin (n + 1) → ℝ) (c : Fin n → ℝ) (k : Fin (n + 2)) :
    profilePrefixLinearMap g c k = profilePrefix g c k :=
  rfl

/-- The prefix section is an exact right inverse to finite curvature. -/
theorem profilePrefixLinearMap_rightInverse {n : ℕ}
    (g : Fin (n + 1) → ℝ) (hg : ∀ j, g j ≠ 0) :
    Function.RightInverse (profilePrefixLinearMap g) (finiteCurvatureMap g) := by
  intro c
  exact finiteCurvature_profilePrefix g hg c

/-- Equivalently, curvature followed by its prefix section is the identity. -/
theorem finiteCurvatureMap_comp_profilePrefixLinearMap {n : ℕ}
    (g : Fin (n + 1) → ℝ) (hg : ∀ j, g j ≠ 0) :
    (finiteCurvatureMap g).comp (profilePrefixLinearMap g) =
      LinearMap.id := by
  apply LinearMap.ext
  intro c
  funext i
  exact congrFun (finiteCurvature_profilePrefix g hg c) i

/-- Nonzero gaps make the finite curvature map surjective. -/
theorem finiteCurvatureMap_surjective {n : ℕ}
    (g : Fin (n + 1) → ℝ) (hg : ∀ j, g j ≠ 0) :
    Function.Surjective (finiteCurvatureMap g) := by
  intro c
  exact ⟨profilePrefixLinearMap g c, finiteCurvature_profilePrefix g hg c⟩

end

end RiemannResearch.RH.PrimeGapCurvature
