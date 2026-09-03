/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Adjacent prime-gap curvature and optimizer gluing

This module formalizes the exact finite-dimensional algebra behind the
adjacent-curvature compression in the user-provided RH continuation dated
2026-09-03.  It does not assert the unresolved arithmetic estimate for the
actual Nyman--Beurling signal and does not assert localized Weil positivity.

The main checked ingredients are:

* adjacent divided second differences annihilate affine signals;
* vanishing adjacent curvature forces a finite signal to be affine;
* consecutive three-point determinants are gap products times adjacent
  curvature;
* kernel-orthogonal lifts minimize any nonnegative symmetric bilinear energy;
* the two-block common-optimizer penalty is the exact scalar Schur term;
* the bandwidth-two forward-substitution recursion is exact and its diagonal
  energy is nonnegative when the pivots are positive.

Source: user-provided argument, `rh_irreducible_targets_progress_2026-09-03`.
The source supports the statements and proof strategy.  The asymptotic
actual-signal estimate, the all-window Weil statement, and the transcendental
interval certificate remain separate obligations.
-/

namespace RiemannResearch.RH.PrimeGapCurvature

open scoped BigOperators

/-- The adjacent gap `t (i+1) - t i`. -/
def gap (t : ℕ → ℝ) (i : ℕ) : ℝ :=
  t (i + 1) - t i

/-- The secant slope over the adjacent pair `i,i+1`. -/
def adjacentSlope (t z : ℕ → ℝ) (i : ℕ) : ℝ :=
  (z (i + 1) - z i) / gap t i

/-- The divided second difference on the consecutive triple `i,i+1,i+2`. -/
def adjacentCurvature (t z : ℕ → ℝ) (i : ℕ) : ℝ :=
  adjacentSlope t z (i + 1) - adjacentSlope t z i

/-- Adjacent curvature vanishes exactly when the two neighboring slopes agree. -/
theorem adjacentCurvature_eq_zero_iff (t z : ℕ → ℝ) (i : ℕ) :
    adjacentCurvature t z i = 0 ↔
      adjacentSlope t z (i + 1) = adjacentSlope t z i := by
  simp [adjacentCurvature]

/-- Every affine function of the coordinate `t` has zero adjacent curvature. -/
theorem adjacentCurvature_affine
    (t : ℕ → ℝ) (a b : ℝ) (i : ℕ)
    (hgap₀ : gap t i ≠ 0) (hgap₁ : gap t (i + 1) ≠ 0) :
    adjacentCurvature t (fun n ↦ a + b * t n) i = 0 := by
  simp only [adjacentCurvature, adjacentSlope, gap]
  field_simp [hgap₀, hgap₁]
  ring

/-- Adding an affine signal does not change adjacent curvature. -/
theorem adjacentCurvature_add_affine
    (t z : ℕ → ℝ) (a b : ℝ) (i : ℕ)
    (hgap₀ : gap t i ≠ 0) (hgap₁ : gap t (i + 1) ≠ 0) :
    adjacentCurvature t (fun n ↦ z n + (a + b * t n)) i =
      adjacentCurvature t z i := by
  simp only [adjacentCurvature, adjacentSlope, gap]
  field_simp [hgap₀, hgap₁]
  ring

/-- The oriented determinant of the three rows `(1,t,z)` at `i,j,k`. -/
def tripleDet (t z : ℕ → ℝ) (i j k : ℕ) : ℝ :=
  (t j - t i) * (z k - z i) - (t k - t i) * (z j - z i)

/-- A three-point determinant is the product of the two gaps and the
corresponding difference of secant slopes. -/
theorem tripleDet_eq_gap_mul_gap_mul_slopeDiff
    (t z : ℕ → ℝ) (i j k : ℕ)
    (hij : t j - t i ≠ 0) (hjk : t k - t j ≠ 0) :
    tripleDet t z i j k =
      (t j - t i) * (t k - t j) *
        ((z k - z j) / (t k - t j) -
          (z j - z i) / (t j - t i)) := by
  simp only [tripleDet]
  field_simp [hij, hjk]
  ring

/-- For a consecutive triple, the determinant is exactly the product of the
adjacent gaps and the adjacent curvature. -/
theorem consecutiveTripleDet_eq
    (t z : ℕ → ℝ) (i : ℕ)
    (hgap₀ : gap t i ≠ 0) (hgap₁ : gap t (i + 1) ≠ 0) :
    tripleDet t z i (i + 1) (i + 2) =
      gap t i * gap t (i + 1) * adjacentCurvature t z i := by
  simp only [tripleDet, adjacentCurvature, adjacentSlope, gap]
  field_simp [hgap₀, hgap₁]
  ring

/-- Zero adjacent curvature propagates equality of consecutive slopes. -/
theorem adjacentSlope_succ_eq_of_curvature_eq_zero
    (t z : ℕ → ℝ) (i : ℕ)
    (h : adjacentCurvature t z i = 0) :
    adjacentSlope t z (i + 1) = adjacentSlope t z i :=
  (adjacentCurvature_eq_zero_iff t z i).mp h

/-- If the first `n` adjacent curvatures vanish, then every one of the first
`n+1` adjacent slopes equals the initial slope. -/
theorem adjacentSlope_eq_zeroSlope_of_curvature_eq_zero
    (t z : ℕ → ℝ) (n : ℕ)
    (hcurv : ∀ i < n, adjacentCurvature t z i = 0) :
    ∀ i ≤ n, adjacentSlope t z i = adjacentSlope t z 0 := by
  intro i
  induction i with
  | zero =>
      intro _
      rfl
  | succ i ih =>
      intro hi
      have hlt : i < n := Nat.lt_of_succ_le hi
      calc
        adjacentSlope t z (Nat.succ i) = adjacentSlope t z i := by
          simpa [Nat.succ_eq_add_one] using
            adjacentSlope_succ_eq_of_curvature_eq_zero t z i (hcurv i hlt)
        _ = adjacentSlope t z 0 := ih (Nat.le_of_succ_le hi)

/-- On a finite interval with nonzero adjacent gaps, zero adjacent curvature
forces the signal to be affine in `t`. -/
theorem exists_affine_on_range_of_curvature_eq_zero
    (t z : ℕ → ℝ) (n : ℕ)
    (hgap : ∀ i ≤ n, gap t i ≠ 0)
    (hcurv : ∀ i < n, adjacentCurvature t z i = 0) :
    ∃ a b : ℝ, ∀ i ≤ n + 1, z i = a + b * t i := by
  let b := adjacentSlope t z 0
  let a := z 0 - b * t 0
  refine ⟨a, b, ?_⟩
  intro i
  induction i with
  | zero =>
      intro _
      simp [a]
  | succ i ih =>
      intro hi
      have hin : i ≤ n := by
        exact Nat.succ_le_succ_iff.mp (by simpa [Nat.succ_eq_add_one] using hi)
      have hiPrev : i ≤ n + 1 := hin.trans (Nat.le_succ n)
      have ihz : z i = a + b * t i := ih hiPrev
      have hslope : adjacentSlope t z i = b := by
        dsimp only [b]
        exact adjacentSlope_eq_zeroSlope_of_curvature_eq_zero t z n hcurv i hin
      have hdiff : z (i + 1) - z i = b * gap t i :=
        (div_eq_iff (hgap i hin)).mp hslope
      change z (i + 1) = a + b * t (i + 1)
      rw [show z (i + 1) = z i + b * gap t i by linarith]
      rw [ihz]
      simp only [gap]
      ring

/-- Finite kernel characterization: adjacent curvatures vanish exactly for
signals affine in the coordinate `t`. -/
theorem curvature_eq_zero_iff_exists_affine_on_range
    (t z : ℕ → ℝ) (n : ℕ)
    (hgap : ∀ i ≤ n, gap t i ≠ 0) :
    (∀ i < n, adjacentCurvature t z i = 0) ↔
      ∃ a b : ℝ, ∀ i ≤ n + 1, z i = a + b * t i := by
  constructor
  · exact exists_affine_on_range_of_curvature_eq_zero t z n hgap
  · rintro ⟨a, b, hz⟩ i hi
    have hiLe : i ≤ n := Nat.le_of_lt hi
    have hiSuccLe : i + 1 ≤ n := by
      simpa [Nat.succ_eq_add_one] using (Nat.succ_le_iff.mpr hi)
    have hi₀ : i ≤ n + 1 := hiLe.trans (Nat.le_succ n)
    have hi₁ : i + 1 ≤ n + 1 := hiSuccLe.trans (Nat.le_succ n)
    have hi₂ : i + 2 ≤ n + 1 := by
      simpa [Nat.succ_eq_add_one] using Nat.succ_le_succ hiSuccLe
    have hgap₀ : gap t i ≠ 0 := hgap i hiLe
    have hgap₁ : gap t (i + 1) ≠ 0 := hgap (i + 1) hiSuccLe
    simp only [adjacentCurvature, adjacentSlope]
    rw [hz i hi₀, hz (i + 1) hi₁, hz (i + 2) hi₂]
    exact adjacentCurvature_affine t a b i hgap₀ hgap₁

section BilinearEnergy

variable {E F : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- Exact Pythagorean decomposition for a symmetric bilinear energy when a
chosen lift is orthogonal to the kernel of the constraint map. -/
theorem bilinearEnergy_decomposition
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hSymm : ∀ x y, B x y = B y x)
    (D : E →ₗ[ℝ] F)
    (q r : E)
    (hSame : D r = D q)
    (hOrth : ∀ k, D k = 0 → B q k = 0) :
    B r r = B q q + B (r - q) (r - q) := by
  have hker : D (r - q) = 0 := by
    rw [map_sub, hSame, sub_self]
  have hqk : B q (r - q) = 0 := hOrth (r - q) hker
  have hkq : B (r - q) q = 0 := by
    rw [hSymm, hqk]
  calc
    B r r = B (q + (r - q)) (q + (r - q)) := by
      congr 1 <;> abel
    _ = B q q + B q (r - q) + B (r - q) q + B (r - q) (r - q) := by
      simp only [map_add]
      ring
    _ = B q q + B (r - q) (r - q) := by rw [hqk, hkq]; ring

/-- A kernel-orthogonal lift minimizes every nonnegative symmetric bilinear
energy among vectors with the same constraint image. -/
theorem bilinearEnergy_minimum
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hSymm : ∀ x y, B x y = B y x)
    (hNonneg : ∀ x, 0 ≤ B x x)
    (D : E →ₗ[ℝ] F)
    (q r : E)
    (hSame : D r = D q)
    (hOrth : ∀ k, D k = 0 → B q k = 0) :
    B q q ≤ B r r := by
  rw [bilinearEnergy_decomposition B hSymm D q r hSame hOrth]
  exact le_add_of_nonneg_right (hNonneg (r - q))

end BilinearEnergy

/-- Weighted mean of two scalar block optimizers. -/
def twoBlockMean (a b u v : ℝ) : ℝ :=
  (a * u + b * v) / (a + b)

/-- Exact two-block completion of squares.  The final term is the scalar
common-optimizer gluing penalty. -/
theorem twoBlock_schur_identity
    (a b u v x : ℝ) (hab : a + b ≠ 0) :
    a * (x - u) ^ 2 + b * (x - v) ^ 2 =
      (a + b) * (x - twoBlockMean a b u v) ^ 2 +
        (a * b / (a + b)) * (u - v) ^ 2 := by
  simp only [twoBlockMean]
  field_simp [hab]
  ring

/-- The common weighted optimizer has exactly the Schur gluing cost. -/
theorem twoBlock_value_at_mean
    (a b u v : ℝ) (hab : a + b ≠ 0) :
    a * (twoBlockMean a b u v - u) ^ 2 +
        b * (twoBlockMean a b u v - v) ^ 2 =
      (a * b / (a + b)) * (u - v) ^ 2 := by
  simpa using twoBlock_schur_identity a b u v (twoBlockMean a b u v) hab

/-- With positive block weights, the Schur gluing penalty is nonnegative. -/
theorem twoBlock_gluing_nonneg
    (a b u v : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    0 ≤ (a * b / (a + b)) * (u - v) ^ 2 := by
  positivity

/-- With positive block weights, the common weighted mean minimizes the sum of
the two block losses. -/
theorem twoBlock_mean_minimizes
    (a b u v x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    a * (twoBlockMean a b u v - u) ^ 2 +
        b * (twoBlockMean a b u v - v) ^ 2 ≤
      a * (x - u) ^ 2 + b * (x - v) ^ 2 := by
  calc
    a * (twoBlockMean a b u v - u) ^ 2 +
          b * (twoBlockMean a b u v - v) ^ 2 =
        (a * b / (a + b)) * (u - v) ^ 2 :=
      twoBlock_value_at_mean a b u v hab.ne'
    _ ≤ (a + b) * (x - twoBlockMean a b u v) ^ 2 +
          (a * b / (a + b)) * (u - v) ^ 2 := by
      exact le_add_of_nonneg_left (mul_nonneg hab.le (sq_nonneg _))
    _ = a * (x - u) ^ 2 + b * (x - v) ^ 2 :=
      (twoBlock_schur_identity a b u v x hab.ne').symm

/-- Forward substitution for a unit lower-triangular operator with two strict
subdiagonals. -/
def bandwidthTwoInnovation
    (ell second delta : ℕ → ℝ) : ℕ → ℝ
  | 0 => delta 0
  | 1 => delta 1 - ell 1 * delta 0
  | n + 2 =>
      delta (n + 2) - ell (n + 2) * bandwidthTwoInnovation ell second delta (n + 1) -
        second (n + 2) * bandwidthTwoInnovation ell second delta n

/-- The innovation recursion solves the bandwidth-two forward system exactly. -/
theorem bandwidthTwoInnovation_forward
    (ell second delta : ℕ → ℝ) :
    (bandwidthTwoInnovation ell second delta 0 = delta 0) ∧
      (bandwidthTwoInnovation ell second delta 1 +
          ell 1 * bandwidthTwoInnovation ell second delta 0 = delta 1) ∧
      (∀ n,
        bandwidthTwoInnovation ell second delta (n + 2) +
            ell (n + 2) * bandwidthTwoInnovation ell second delta (n + 1) +
            second (n + 2) * bandwidthTwoInnovation ell second delta n =
          delta (n + 2)) := by
  constructor
  · rfl
  constructor
  · simp [bandwidthTwoInnovation]
  · intro n
    simp [bandwidthTwoInnovation]
    ring

/-- The diagonal innovation energy associated with positive pivots. -/
def bandwidthTwoEnergy
    (pivot ell second delta : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N,
    (bandwidthTwoInnovation ell second delta i) ^ 2 / pivot i

/-- Positive pivots make every finite bandwidth-two innovation energy
nonnegative. -/
theorem bandwidthTwoEnergy_nonneg
    (pivot ell second delta : ℕ → ℝ) (N : ℕ)
    (hpivot : ∀ i < N, 0 < pivot i) :
    0 ≤ bandwidthTwoEnergy pivot ell second delta N := by
  apply Finset.sum_nonneg
  intro i hi
  simp only [Finset.mem_range] at hi
  exact div_nonneg (sq_nonneg _) (hpivot i hi).le

/-- Algebraic bookkeeping for retaining the signed prime-power contribution
until after multiplication by the actual Rayleigh factor. -/
theorem signedReturn_mul_rayleigh
    (return diagonal eta primePower remainder rayleigh : ℝ)
    (hreturn : return = diagonal - eta * primePower + remainder) :
    return * rayleigh =
      (diagonal - eta * primePower + remainder) * rayleigh := by
  rw [hreturn]

end RiemannResearch.RH.PrimeGapCurvature
