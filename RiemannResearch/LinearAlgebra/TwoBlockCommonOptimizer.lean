/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.LinearAlgebra.DualGreenProjection
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Two-block common optimizers

This module proves exact completion identities for forcing two quadratic blocks
to share one optimizer. The first layer permits two distinct symmetric
bilinear forms and constructs the optimizer from the inverse summed normal
map. The second layer gives the closed weighted barycenter and parallel-sum
mismatch when both blocks use the same form.

Source: user-provided continuation argument,
`RH_Lean_Autonomous_Next_Task_Handoff.md`. The source supports the statements
and proof strategy. These are finite-dimensional or purely algebraic
identities; they do not identify an RH quadratic form or prove RH.
-/

namespace RiemannResearch.LinearAlgebra

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ## Distinct bilinear forms -/

/-- Sum of two quadratic losses centered at `u` and `v`. -/
def twoBlockFormLoss
    (B₁ B₂ : RealBilin V) (u v x : V) : ℝ :=
  B₁ (x - u) (x - u) + B₂ (x - v) (x - v)

/-- Residual cost of forcing the two blocks to use the common point `m`. -/
def twoBlockFormMismatch
    (B₁ B₂ : RealBilin V) (u v m : V) : ℝ :=
  B₁ (m - u) (m - u) + B₂ (m - v) (m - v)

/-- First-order stationarity of a common optimizer for two bilinear forms. -/
def TwoBlockFormStationary
    (B₁ B₂ : RealBilin V) (u v m : V) : Prop :=
  ∀ y, B₁ (m - u) y + B₂ (m - v) y = 0

/-- Stationarity is exactly the summed normal equation. -/
theorem twoBlockFormStationary_iff_normalEquation
    (B₁ B₂ : RealBilin V) (u v m : V) :
    TwoBlockFormStationary B₁ B₂ u v m ↔
      (B₁ + B₂) m = B₁ u + B₂ v := by
  constructor
  · intro hm
    apply LinearMap.ext
    intro y
    have hy := hm y
    simp only [LinearMap.add_apply, map_sub, LinearMap.sub_apply] at hy ⊢
    linarith
  · intro hm y
    have hy := LinearMap.congr_fun hm y
    simp only [LinearMap.add_apply, map_sub, LinearMap.sub_apply] at hy ⊢
    linarith

/-- The shared boundary flux, viewed from the first block. -/
def twoBlockCommonFlux
    (B₁ : RealBilin V) (u m : V) : V →ₗ[ℝ] ℝ :=
  B₁ (u - m)

/-- At a stationary point, both blocks carry the same boundary flux. -/
theorem twoBlockCommonFlux_eq
    (B₁ B₂ : RealBilin V) (u v m : V)
    (hm : TwoBlockFormStationary B₁ B₂ u v m) :
    twoBlockCommonFlux B₁ u m = B₂ (m - v) := by
  apply LinearMap.ext
  intro y
  have h := hm y
  simp only [twoBlockCommonFlux]
  have hum : u - m = -(m - u) := by abel
  rw [hum, map_neg, LinearMap.neg_apply]
  linarith

/-- The residual cost is exactly flux times the displacement between centers. -/
theorem twoBlockFormMismatch_eq_commonFlux
    (B₁ B₂ : RealBilin V) (u v m : V)
    (hm : TwoBlockFormStationary B₁ B₂ u v m) :
    twoBlockFormMismatch B₁ B₂ u v m =
      twoBlockCommonFlux B₁ u m (u - v) := by
  have hflux := twoBlockCommonFlux_eq B₁ B₂ u v m hm
  have hflux_eval := LinearMap.congr_fun hflux (m - v)
  change B₁ (u - m) (m - v) = B₂ (m - v) (m - v) at hflux_eval
  have huv : u - v = (u - m) + (m - v) := by abel
  have hmu : m - u = -(u - m) := by abel
  simp only [twoBlockFormMismatch, twoBlockCommonFlux, huv, map_add,
    hmu, map_neg, LinearMap.neg_apply, neg_neg]
  rw [hflux_eval]

/-- Exact completion around a stationary common optimizer. -/
theorem twoBlockForm_commonOptimizer_identity
    (B₁ B₂ : RealBilin V)
    (h₁symm : ∀ x y, B₁ x y = B₁ y x)
    (h₂symm : ∀ x y, B₂ x y = B₂ y x)
    (u v m x : V)
    (hm : TwoBlockFormStationary B₁ B₂ u v m) :
    twoBlockFormLoss B₁ B₂ u v x =
      (B₁ (x - m) (x - m) + B₂ (x - m) (x - m)) +
        twoBlockFormMismatch B₁ B₂ u v m := by
  have hxu : x - u = (x - m) + (m - u) := by abel
  have hxv : x - v = (x - m) + (m - v) := by abel
  simp only [twoBlockFormLoss, twoBlockFormMismatch, hxu, hxv, map_add,
    LinearMap.add_apply]
  rw [h₁symm (x - m) (m - u), h₂symm (x - m) (m - v)]
  linarith [hm (x - m)]

/-- The mismatch is nonnegative for two nonnegative forms. -/
theorem twoBlockFormMismatch_nonneg
    (B₁ B₂ : RealBilin V)
    (h₁nonneg : ∀ y, 0 ≤ B₁ y y)
    (h₂nonneg : ∀ y, 0 ≤ B₂ y y)
    (u v m : V) :
    0 ≤ twoBlockFormMismatch B₁ B₂ u v m :=
  add_nonneg (h₁nonneg _) (h₂nonneg _)

/-- A stationary point minimizes the total two-block loss. -/
theorem twoBlockForm_commonOptimizer_minimizes
    (B₁ B₂ : RealBilin V)
    (h₁symm : ∀ x y, B₁ x y = B₁ y x)
    (h₂symm : ∀ x y, B₂ x y = B₂ y x)
    (h₁nonneg : ∀ y, 0 ≤ B₁ y y)
    (h₂nonneg : ∀ y, 0 ≤ B₂ y y)
    (u v m x : V)
    (hm : TwoBlockFormStationary B₁ B₂ u v m) :
    twoBlockFormLoss B₁ B₂ u v m ≤
      twoBlockFormLoss B₁ B₂ u v x := by
  change twoBlockFormMismatch B₁ B₂ u v m ≤
    twoBlockFormLoss B₁ B₂ u v x
  rw [twoBlockForm_commonOptimizer_identity
    B₁ B₂ h₁symm h₂symm u v m x hm]
  have hres :
      0 ≤ B₁ (x - m) (x - m) + B₂ (x - m) (x - m) :=
    add_nonneg (h₁nonneg _) (h₂nonneg _)
  linarith

/-- A definite summed quadratic makes the stationary point the unique
minimizer. -/
theorem twoBlockForm_commonOptimizer_eq_iff
    (B₁ B₂ : RealBilin V)
    (h₁symm : ∀ x y, B₁ x y = B₁ y x)
    (h₂symm : ∀ x y, B₂ x y = B₂ y x)
    (hsum_zero : ∀ y, B₁ y y + B₂ y y = 0 → y = 0)
    (u v m x : V)
    (hm : TwoBlockFormStationary B₁ B₂ u v m) :
    twoBlockFormLoss B₁ B₂ u v x =
        twoBlockFormLoss B₁ B₂ u v m ↔
      x = m := by
  constructor
  · intro h
    rw [twoBlockForm_commonOptimizer_identity
      B₁ B₂ h₁symm h₂symm u v m x hm] at h
    change
      B₁ (x - m) (x - m) + B₂ (x - m) (x - m) +
          twoBlockFormMismatch B₁ B₂ u v m =
        twoBlockFormMismatch B₁ B₂ u v m at h
    have hzero :
        B₁ (x - m) (x - m) + B₂ (x - m) (x - m) = 0 := by
      linarith
    exact sub_eq_zero.mp (hsum_zero _ hzero)
  · rintro rfl
    rfl

/-- Under positive definiteness of both blocks, the mismatch vanishes exactly
when their separate centers agree. -/
theorem twoBlockFormMismatch_eq_zero_iff
    (B₁ B₂ : RealBilin V)
    (h₁nonneg : ∀ y, 0 ≤ B₁ y y)
    (h₂nonneg : ∀ y, 0 ≤ B₂ y y)
    (h₁zero : ∀ y, B₁ y y = 0 → y = 0)
    (h₂zero : ∀ y, B₂ y y = 0 → y = 0)
    (u v m : V)
    (hm : TwoBlockFormStationary B₁ B₂ u v m) :
    twoBlockFormMismatch B₁ B₂ u v m = 0 ↔ u = v := by
  constructor
  · intro h
    have h₁z : B₁ (m - u) (m - u) = 0 := by
      have h₁n := h₁nonneg (m - u)
      have h₂n := h₂nonneg (m - v)
      simp only [twoBlockFormMismatch] at h
      linarith
    have h₂z : B₂ (m - v) (m - v) = 0 := by
      have h₁n := h₁nonneg (m - u)
      have h₂n := h₂nonneg (m - v)
      simp only [twoBlockFormMismatch] at h
      linarith
    have hmu : m = u := sub_eq_zero.mp (h₁zero _ h₁z)
    have hmv : m = v := sub_eq_zero.mp (h₂zero _ h₂z)
    exact hmu.symm.trans hmv
  · intro huv
    subst v
    have hs := hm (m - u)
    have h₁n := h₁nonneg (m - u)
    have h₂n := h₂nonneg (m - u)
    have h₁z : B₁ (m - u) (m - u) = 0 := by
      linarith
    have hmu : m = u := sub_eq_zero.mp (h₁zero _ h₁z)
    subst m
    simp [twoBlockFormMismatch]

/-- A definite diagonal sum makes the summed bilinear form nondegenerate. -/
theorem twoBlockFormSum_nondegenerate
    (B₁ B₂ : RealBilin V)
    (hsum_zero : ∀ y, B₁ y y + B₂ y y = 0 → y = 0) :
    (B₁ + B₂).Nondegenerate := by
  constructor
  · intro x hx
    apply hsum_zero x
    simpa only [LinearMap.add_apply] using hx x
  · intro y hy
    apply hsum_zero y
    simpa only [LinearMap.add_apply] using hy y

/-- The common optimizer obtained by inverting the summed normal map. -/
def twoBlockFormOptimizer
    [FiniteDimensional ℝ V]
    (B₁ B₂ : RealBilin V)
    (hnd : (B₁ + B₂).Nondegenerate)
    (u v : V) : V :=
  ((B₁ + B₂).toDual hnd).symm (B₁ u + B₂ v)

/-- The inverse-normal-map optimizer satisfies the exact stationarity
condition. -/
theorem twoBlockFormOptimizer_stationary
    [FiniteDimensional ℝ V]
    (B₁ B₂ : RealBilin V)
    (hnd : (B₁ + B₂).Nondegenerate)
    (u v : V) :
    TwoBlockFormStationary B₁ B₂ u v
      (twoBlockFormOptimizer B₁ B₂ hnd u v) := by
  rw [twoBlockFormStationary_iff_normalEquation]
  apply LinearMap.ext
  intro y
  exact LinearMap.BilinForm.apply_toDual_symm_apply
    (B := B₁ + B₂) (hB := hnd) (B₁ u + B₂ v) y

/-- The constructed optimizer gives exact completion for two distinct
symmetric forms. -/
theorem twoBlockFormOptimizer_identity
    [FiniteDimensional ℝ V]
    (B₁ B₂ : RealBilin V)
    (h₁symm : ∀ x y, B₁ x y = B₁ y x)
    (h₂symm : ∀ x y, B₂ x y = B₂ y x)
    (hnd : (B₁ + B₂).Nondegenerate)
    (u v x : V) :
    twoBlockFormLoss B₁ B₂ u v x =
      (B₁ (x - twoBlockFormOptimizer B₁ B₂ hnd u v)
          (x - twoBlockFormOptimizer B₁ B₂ hnd u v) +
        B₂ (x - twoBlockFormOptimizer B₁ B₂ hnd u v)
          (x - twoBlockFormOptimizer B₁ B₂ hnd u v)) +
        twoBlockFormMismatch B₁ B₂ u v
          (twoBlockFormOptimizer B₁ B₂ hnd u v) := by
  exact twoBlockForm_commonOptimizer_identity
    B₁ B₂ h₁symm h₂symm u v
      (twoBlockFormOptimizer B₁ B₂ hnd u v) x
      (twoBlockFormOptimizer_stationary B₁ B₂ hnd u v)

/-- Finite-dimensional symmetric blocks with a definite summed diagonal have
an explicit unique global common optimizer. -/
theorem twoBlockFormOptimizer_uniqueMinimizer
    [FiniteDimensional ℝ V]
    (B₁ B₂ : RealBilin V)
    (h₁symm : ∀ x y, B₁ x y = B₁ y x)
    (h₂symm : ∀ x y, B₂ x y = B₂ y x)
    (h₁nonneg : ∀ y, 0 ≤ B₁ y y)
    (h₂nonneg : ∀ y, 0 ≤ B₂ y y)
    (hsum_zero : ∀ y, B₁ y y + B₂ y y = 0 → y = 0)
    (u v x : V) :
    let hnd := twoBlockFormSum_nondegenerate B₁ B₂ hsum_zero
    let m := twoBlockFormOptimizer B₁ B₂ hnd u v
    twoBlockFormLoss B₁ B₂ u v m ≤ twoBlockFormLoss B₁ B₂ u v x ∧
      (twoBlockFormLoss B₁ B₂ u v x =
          twoBlockFormLoss B₁ B₂ u v m ↔ x = m) := by
  dsimp only
  let hnd := twoBlockFormSum_nondegenerate B₁ B₂ hsum_zero
  let m := twoBlockFormOptimizer B₁ B₂ hnd u v
  have hm : TwoBlockFormStationary B₁ B₂ u v m :=
    twoBlockFormOptimizer_stationary B₁ B₂ hnd u v
  exact ⟨
    twoBlockForm_commonOptimizer_minimizes
      B₁ B₂ h₁symm h₂symm h₁nonneg h₂nonneg u v m x hm,
    twoBlockForm_commonOptimizer_eq_iff
      B₁ B₂ h₁symm h₂symm hsum_zero u v m x hm⟩

/-- A positive-definite first block and nonnegative second block make the
summed diagonal definite. -/
theorem twoBlockFormSum_zero_imp
    (B₁ B₂ : RealBilin V)
    (h₁nonneg : ∀ y, 0 ≤ B₁ y y)
    (h₂nonneg : ∀ y, 0 ≤ B₂ y y)
    (h₁zero : ∀ y, B₁ y y = 0 → y = 0) :
    ∀ y, B₁ y y + B₂ y y = 0 → y = 0 := by
  intro y hsum
  apply h₁zero y
  have h₁ := h₁nonneg y
  have h₂ := h₂nonneg y
  linarith

/-- The inverse-normal-map point is the unique global minimizer. -/
theorem existsUnique_twoBlockForm_minimizer
    [FiniteDimensional ℝ V]
    (B₁ B₂ : RealBilin V)
    (h₁symm : ∀ x y, B₁ x y = B₁ y x)
    (h₂symm : ∀ x y, B₂ x y = B₂ y x)
    (h₁nonneg : ∀ y, 0 ≤ B₁ y y)
    (h₂nonneg : ∀ y, 0 ≤ B₂ y y)
    (h₁zero : ∀ y, B₁ y y = 0 → y = 0)
    (u v : V) :
    ∃! m, ∀ x,
      twoBlockFormLoss B₁ B₂ u v m ≤
        twoBlockFormLoss B₁ B₂ u v x := by
  let hsum_zero :=
    twoBlockFormSum_zero_imp B₁ B₂ h₁nonneg h₂nonneg h₁zero
  let hnd := twoBlockFormSum_nondegenerate B₁ B₂ hsum_zero
  let m := twoBlockFormOptimizer B₁ B₂ hnd u v
  have hm : TwoBlockFormStationary B₁ B₂ u v m :=
    twoBlockFormOptimizer_stationary B₁ B₂ hnd u v
  refine ⟨m, ?_, ?_⟩
  · intro x
    exact twoBlockForm_commonOptimizer_minimizes
      B₁ B₂ h₁symm h₂symm h₁nonneg h₂nonneg u v m x hm
  · intro z hz
    have hzm :
        twoBlockFormLoss B₁ B₂ u v z ≤
          twoBlockFormLoss B₁ B₂ u v m :=
      hz m
    have hmz :
        twoBlockFormLoss B₁ B₂ u v m ≤
          twoBlockFormLoss B₁ B₂ u v z :=
      twoBlockForm_commonOptimizer_minimizes
        B₁ B₂ h₁symm h₂symm h₁nonneg h₂nonneg u v m z hm
    have heq :
        twoBlockFormLoss B₁ B₂ u v z =
          twoBlockFormLoss B₁ B₂ u v m :=
      le_antisymm hzm hmz
    exact (twoBlockForm_commonOptimizer_eq_iff
      B₁ B₂ h₁symm h₂symm hsum_zero u v m z hm).mp heq

/-- For the constructed optimizer, the Schur mismatch is zero exactly when
the two centers coincide. -/
theorem twoBlockFormOptimizer_mismatch_eq_zero_iff
    [FiniteDimensional ℝ V]
    (B₁ B₂ : RealBilin V)
    (h₁nonneg : ∀ y, 0 ≤ B₁ y y)
    (h₂nonneg : ∀ y, 0 ≤ B₂ y y)
    (h₁zero : ∀ y, B₁ y y = 0 → y = 0)
    (h₂zero : ∀ y, B₂ y y = 0 → y = 0)
    (u v : V) :
    let hsum_zero :=
      twoBlockFormSum_zero_imp B₁ B₂ h₁nonneg h₂nonneg h₁zero
    let hnd := twoBlockFormSum_nondegenerate B₁ B₂ hsum_zero
    let m := twoBlockFormOptimizer B₁ B₂ hnd u v
    twoBlockFormMismatch B₁ B₂ u v m = 0 ↔ u = v := by
  dsimp only
  let hsum_zero :=
    twoBlockFormSum_zero_imp B₁ B₂ h₁nonneg h₂nonneg h₁zero
  let hnd := twoBlockFormSum_nondegenerate B₁ B₂ hsum_zero
  let m := twoBlockFormOptimizer B₁ B₂ hnd u v
  exact twoBlockFormMismatch_eq_zero_iff
    B₁ B₂ h₁nonneg h₂nonneg h₁zero h₂zero u v m
      (twoBlockFormOptimizer_stationary B₁ B₂ hnd u v)

/-! ## One form with scalar block weights -/

/-- Two centered losses using one form with scalar block weights. -/
def weightedTwoBlockLoss
    (B : RealBilin V) (a b : ℝ) (u v x : V) : ℝ :=
  a * B (x - u) (x - u) + b * B (x - v) (x - v)

/-- Closed common optimizer when both blocks use scalar multiples of one form. -/
def weightedTwoBlockOptimizer (a b : ℝ) (u v : V) : V :=
  (a / (a + b)) • u + (b / (a + b)) • v

/-- Closed parallel-sum mismatch for the scalar-weighted problem. -/
def weightedTwoBlockMismatch
    (B : RealBilin V) (a b : ℝ) (u v : V) : ℝ :=
  (a * b / (a + b)) * B (u - v) (u - v)

theorem weightedTwoBlockOptimizer_sub_left
    {a b : ℝ} (hden : a + b ≠ 0) (u v : V) :
    weightedTwoBlockOptimizer a b u v - u =
      (b / (a + b)) • (v - u) := by
  have hsum : a / (a + b) + b / (a + b) = 1 := by
    field_simp
  unfold weightedTwoBlockOptimizer
  calc
    (a / (a + b)) • u + (b / (a + b)) • v - u =
        (a / (a + b)) • u + (b / (a + b)) • v -
          (a / (a + b) + b / (a + b)) • u := by
            rw [hsum, one_smul]
    _ = (b / (a + b)) • (v - u) := by module

theorem weightedTwoBlockOptimizer_sub_right
    {a b : ℝ} (hden : a + b ≠ 0) (u v : V) :
    weightedTwoBlockOptimizer a b u v - v =
      (a / (a + b)) • (u - v) := by
  have hsum : a / (a + b) + b / (a + b) = 1 := by
    field_simp
  unfold weightedTwoBlockOptimizer
  calc
    (a / (a + b)) • u + (b / (a + b)) • v - v =
        (a / (a + b)) • u + (b / (a + b)) • v -
          (a / (a + b) + b / (a + b)) • v := by
            rw [hsum, one_smul]
    _ = (a / (a + b)) • (u - v) := by module

theorem weightedTwoBlockOptimizer_stationary
    {a b : ℝ} (hden : a + b ≠ 0) (u v : V) :
    a • (weightedTwoBlockOptimizer a b u v - u) +
        b • (weightedTwoBlockOptimizer a b u v - v) = 0 := by
  rw [weightedTwoBlockOptimizer_sub_left hden,
    weightedTwoBlockOptimizer_sub_right hden]
  rw [smul_smul, smul_smul]
  have hcross : a * (b / (a + b)) = b * (a / (a + b)) := by
    ring
  rw [hcross]
  module

/-- Completion around any point satisfying the vector stationarity equation. -/
theorem weightedTwoBlockLoss_completion_at_stationary
    (B : RealBilin V)
    (a b : ℝ) (u v m x : V)
    (hstat : a • (m - u) + b • (m - v) = 0) :
    weightedTwoBlockLoss B a b u v x =
      weightedTwoBlockLoss B a b u v m +
        (a + b) * B (x - m) (x - m) := by
  have hxu : x - u = (x - m) + (m - u) := by abel
  have hxv : x - v = (x - m) + (m - v) := by abel
  have hleft :
      a * B (m - u) (x - m) + b * B (m - v) (x - m) = 0 := by
    calc
      a * B (m - u) (x - m) + b * B (m - v) (x - m) =
          B (a • (m - u) + b • (m - v)) (x - m) := by
            simp only [map_add, map_smul, LinearMap.add_apply,
              LinearMap.smul_apply, smul_eq_mul]
      _ = 0 := by rw [hstat]; simp
  have hright :
      a * B (x - m) (m - u) + b * B (x - m) (m - v) = 0 := by
    calc
      a * B (x - m) (m - u) + b * B (x - m) (m - v) =
          B (x - m) (a • (m - u) + b • (m - v)) := by
            simp only [map_add, map_smul, smul_eq_mul]
      _ = 0 := by rw [hstat]; simp
  unfold weightedTwoBlockLoss
  rw [hxu, hxv]
  simp only [map_add, LinearMap.add_apply]
  linear_combination hleft + hright

/-- The closed optimizer has exactly the parallel-sum mismatch energy. -/
theorem weightedTwoBlockLoss_at_optimizer
    (B : RealBilin V)
    {a b : ℝ} (hden : a + b ≠ 0) (u v : V) :
    weightedTwoBlockLoss B a b u v
        (weightedTwoBlockOptimizer a b u v) =
      weightedTwoBlockMismatch B a b u v := by
  rw [weightedTwoBlockLoss, weightedTwoBlockOptimizer_sub_left hden,
    weightedTwoBlockOptimizer_sub_right hden, weightedTwoBlockMismatch]
  have hvu : v - u = -(u - v) := by abel
  rw [hvu]
  simp only [map_smul, map_neg, LinearMap.smul_apply, LinearMap.neg_apply,
    smul_eq_mul, mul_neg, neg_neg]
  field_simp
  ring

/-- Exact scalar-weighted completion with a closed Schur mismatch. -/
theorem weightedTwoBlockLoss_completion
    (B : RealBilin V)
    {a b : ℝ} (hden : a + b ≠ 0) (u v x : V) :
    weightedTwoBlockLoss B a b u v x =
      (a + b) *
          B (x - weightedTwoBlockOptimizer a b u v)
            (x - weightedTwoBlockOptimizer a b u v) +
        weightedTwoBlockMismatch B a b u v := by
  rw [weightedTwoBlockLoss_completion_at_stationary B a b u v
    (weightedTwoBlockOptimizer a b u v) x
    (weightedTwoBlockOptimizer_stationary hden u v)]
  rw [weightedTwoBlockLoss_at_optimizer B hden]
  ring

theorem weightedTwoBlockMismatch_nonneg
    (B : RealBilin V)
    (hB : ∀ y, 0 ≤ B y y)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u v : V) :
    0 ≤ weightedTwoBlockMismatch B a b u v := by
  have hab : 0 < a * b / (a + b) :=
    div_pos (mul_pos ha hb) (add_pos ha hb)
  exact mul_nonneg hab.le (hB (u - v))

theorem weightedTwoBlockOptimizer_minimizes
    (B : RealBilin V)
    (hB : ∀ y, 0 ≤ B y y)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (u v x : V) :
    weightedTwoBlockLoss B a b u v
        (weightedTwoBlockOptimizer a b u v) ≤
      weightedTwoBlockLoss B a b u v x := by
  have hden : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  rw [weightedTwoBlockLoss_at_optimizer B hden,
    weightedTwoBlockLoss_completion B hden]
  have hsquare :
      0 ≤ (a + b) *
        B (x - weightedTwoBlockOptimizer a b u v)
          (x - weightedTwoBlockOptimizer a b u v) :=
    mul_nonneg (add_pos ha hb).le
      (hB (x - weightedTwoBlockOptimizer a b u v))
  linarith

theorem weightedTwoBlockLoss_eq_optimizer_iff
    (B : RealBilin V)
    (hzero : ∀ y, B y y = 0 ↔ y = 0)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (u v x : V) :
    weightedTwoBlockLoss B a b u v x =
        weightedTwoBlockLoss B a b u v
          (weightedTwoBlockOptimizer a b u v) ↔
      x = weightedTwoBlockOptimizer a b u v := by
  have hden : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  rw [weightedTwoBlockLoss_completion B hden,
    weightedTwoBlockLoss_at_optimizer B hden]
  constructor
  · intro h
    have hprod :
        (a + b) *
          B (x - weightedTwoBlockOptimizer a b u v)
            (x - weightedTwoBlockOptimizer a b u v) = 0 := by
      linarith
    have hquad :
        B (x - weightedTwoBlockOptimizer a b u v)
          (x - weightedTwoBlockOptimizer a b u v) = 0 :=
      (mul_eq_zero.mp hprod).resolve_left hden
    exact sub_eq_zero.mp ((hzero _).mp hquad)
  · intro h
    subst x
    simp

theorem weightedTwoBlockMismatch_eq_zero_iff
    (B : RealBilin V)
    (hzero : ∀ y, B y y = 0 ↔ y = 0)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (u v : V) :
    weightedTwoBlockMismatch B a b u v = 0 ↔ u = v := by
  have hcoef : a * b / (a + b) ≠ 0 :=
    ne_of_gt (div_pos (mul_pos ha hb) (add_pos ha hb))
  unfold weightedTwoBlockMismatch
  constructor
  · intro h
    have hquad : B (u - v) (u - v) = 0 :=
      (mul_eq_zero.mp h).resolve_left hcoef
    exact sub_eq_zero.mp ((hzero _).mp hquad)
  · rintro rfl
    simp

end

end RiemannResearch.LinearAlgebra
