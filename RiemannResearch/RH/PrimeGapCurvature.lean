/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Adjacent prime-gap curvature and optimizer gluing

This module formalizes the exact finite-dimensional algebra behind the
adjacent-curvature compression in the user-provided RH continuation dated
2026-09-03. It does not assert the unresolved arithmetic estimate for the
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
The source supports the statements and proof strategy. The asymptotic
actual-signal estimate, the all-window Weil statement, and the transcendental
interval certificate remain separate obligations.
-/

namespace RiemannResearch.RH.PrimeGapCurvature

noncomputable section

open scoped BigOperators
open Filter Asymptotics

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
  change adjacentSlope t z (i + 1) - adjacentSlope t z i = 0 ↔ _
  exact sub_eq_zero

/-- Every affine function of the coordinate `t` has zero adjacent curvature. -/
theorem adjacentCurvature_affine
    (t : ℕ → ℝ) (a b : ℝ) (i : ℕ)
    (hgap₀ : gap t i ≠ 0) (hgap₁ : gap t (i + 1) ≠ 0) :
    adjacentCurvature t (fun n ↦ a + b * t n) i = 0 := by
  simp only [adjacentCurvature, adjacentSlope, gap] at hgap₀ hgap₁ ⊢
  field_simp [hgap₀, hgap₁]
  ring

/-- Adding an affine signal does not change adjacent curvature. -/
theorem adjacentCurvature_add_affine
    (t z : ℕ → ℝ) (a b : ℝ) (i : ℕ)
    (hgap₀ : gap t i ≠ 0) (hgap₁ : gap t (i + 1) ≠ 0) :
    adjacentCurvature t (fun n ↦ z n + (a + b * t n)) i =
      adjacentCurvature t z i := by
  simp only [adjacentCurvature, adjacentSlope, gap] at hgap₀ hgap₁ ⊢
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
  simp only [tripleDet, adjacentCurvature, adjacentSlope, gap] at hgap₀ hgap₁ ⊢
  field_simp [hgap₀, hgap₁]
  ring

lemma sum_curvature_range (t z : ℕ → ℝ) (i n : ℕ) :
    (∑ r ∈ Finset.range n, adjacentCurvature t z (i + r)) =
      adjacentSlope t z (i + n) - adjacentSlope t z i := by
  simpa only [adjacentCurvature, Nat.add_zero, Nat.add_assoc] using
    Finset.sum_range_sub (fun r ↦ adjacentSlope t z (i + r)) n

lemma mul_sum_range_real (a : ℝ) (f : ℕ → ℝ) (n : ℕ) :
    a * (∑ r ∈ Finset.range n, f r) =
      ∑ r ∈ Finset.range n, a * f r := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, ih]

lemma weighted_curvature_prefix
    (t z : ℕ → ℝ) (i n : ℕ)
    (hgap : ∀ r < n, gap t (i + r) ≠ 0) :
    (∑ r ∈ Finset.range n,
        (t (i + r + 1) - t i) * adjacentCurvature t z (i + r)) =
      (t (i + n) - t i) * adjacentSlope t z (i + n) -
        (z (i + n) - z i) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hgap' : ∀ r < n, gap t (i + r) ≠ 0 :=
        fun r hr ↦ hgap r (Nat.lt_succ_of_lt hr)
      rw [ih hgap']
      have hlast : gap t (i + n) ≠ 0 :=
        hgap n (Nat.lt_succ_self n)
      have hslope :
          gap t (i + n) * adjacentSlope t z (i + n) =
            z (i + n + 1) - z (i + n) := by
        simp only [adjacentSlope]
        field_simp [hlast]
      simp only [adjacentCurvature]
      simp only [Nat.add_assoc] at hslope ⊢
      simp only [gap] at hslope
      ring_nf at hslope ⊢
      linarith

lemma weighted_curvature_suffix
    (t z : ℕ → ℝ) (i n : ℕ)
    (hgap : ∀ r ≤ n, gap t (i + r) ≠ 0) :
    (∑ r ∈ Finset.range n,
        (t (i + n + 1) - t (i + r + 1)) *
          adjacentCurvature t z (i + r)) =
      (z (i + n + 1) - z i) -
        (t (i + n + 1) - t i) * adjacentSlope t z i := by
  induction n with
  | zero =>
      have hzero : gap t i ≠ 0 := by
        simpa using hgap 0 (Nat.zero_le 0)
      have hslope :
          gap t i * adjacentSlope t z i = z (i + 1) - z i := by
        simp only [adjacentSlope]
        field_simp [hzero]
      simp only [Finset.range_zero, Finset.sum_empty, Nat.add_zero]
      simp only [gap] at hslope
      linarith
  | succ n ih =>
      have hgap' : ∀ r ≤ n, gap t (i + r) ≠ 0 :=
        fun r hr ↦ hgap r (hr.trans (Nat.le_succ n))
      rw [Finset.sum_range_succ]
      have hshift :
          (∑ r ∈ Finset.range n,
              (t (i + (n + 1) + 1) - t (i + r + 1)) *
                adjacentCurvature t z (i + r)) =
            (∑ r ∈ Finset.range n,
                (t (i + n + 1) - t (i + r + 1)) *
                  adjacentCurvature t z (i + r)) +
              (t (i + (n + 1) + 1) - t (i + n + 1)) *
                (∑ r ∈ Finset.range n,
                  adjacentCurvature t z (i + r)) := by
        rw [mul_sum_range_real]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r _
        ring
      rw [hshift, ih hgap', sum_curvature_range]
      have hlast : gap t (i + n + 1) ≠ 0 := by
        simpa only [Nat.add_assoc] using
          hgap (n + 1) (Nat.le_refl (n + 1))
      have hslope :
          gap t (i + n + 1) * adjacentSlope t z (i + n + 1) =
            z (i + n + 1 + 1) - z (i + n + 1) := by
        simp only [adjacentSlope]
        field_simp [hlast]
      simp only [adjacentCurvature]
      simp only [Nat.add_assoc] at hslope ⊢
      simp only [gap] at hslope
      ring_nf at hslope ⊢
      linarith

/-- Every triple determinant is an exact nonzero-gap weighted combination of
the adjacent curvature coordinates, in offset form. This formalizes equation
(2.10) of the supplied 3 September 2026 progress report. -/
theorem tripleDet_eq_weighted_adjacentCurvatures
    (t z : ℕ → ℝ) (i left right : ℕ)
    (hgap : ∀ r < left + right + 1, gap t (i + r) ≠ 0) :
    tripleDet t z i (i + left) (i + left + right + 1) =
      (t (i + left + right + 1) - t (i + left)) *
        (∑ r ∈ Finset.range left,
          (t (i + r + 1) - t i) *
            adjacentCurvature t z (i + r)) +
      (t (i + left) - t i) *
        (∑ r ∈ Finset.range right,
          (t (i + left + right + 1) - t (i + left + r + 1)) *
            adjacentCurvature t z (i + left + r)) := by
  have hpGap : ∀ r < left, gap t (i + r) ≠ 0 := by
    intro r hr
    exact hgap r (hr.trans_le (Nat.le_add_right left (right + 1)))
  have hsGap : ∀ r ≤ right, gap t ((i + left) + r) ≠ 0 := by
    intro r hr
    have hr' : left + r < left + right + 1 :=
      Nat.add_lt_add_left (Nat.lt_succ_iff.mpr hr) left
    simpa only [Nat.add_assoc] using hgap (left + r) hr'
  rw [weighted_curvature_prefix t z i left hpGap]
  have hs := weighted_curvature_suffix t z (i + left) right hsGap
  simp only [Nat.add_assoc] at hs ⊢
  rw [hs]
  simp only [tripleDet]
  ring

/-- Direct `i < j < k` form of the triple-to-adjacent-curvature telescoping
identity from equation (2.10) of the supplied report. -/
theorem tripleDet_eq_weighted_adjacentCurvatures_of_lt
    (t z : ℕ → ℝ) (i j k : ℕ) (hij : i < j) (hjk : j < k)
    (hgap : ∀ q, i ≤ q → q < k → gap t q ≠ 0) :
    tripleDet t z i j k =
      (t k - t j) *
        (∑ r ∈ Finset.range (j - i),
          (t (i + r + 1) - t i) *
            adjacentCurvature t z (i + r)) +
      (t j - t i) *
        (∑ r ∈ Finset.range (k - j - 1),
          (t k - t (j + r + 1)) *
            adjacentCurvature t z (j + r)) := by
  have hoffsetGap :
      ∀ r < (j - i) + (k - j - 1) + 1,
        gap t (i + r) ≠ 0 := by
    intro r hr
    apply hgap (i + r) (Nat.le_add_right i r)
    omega
  have hmain :=
    tripleDet_eq_weighted_adjacentCurvatures
      t z i (j - i) (k - j - 1) hoffsetGap
  have hij' : i + (j - i) = j := by omega
  have hjk' : j + (k - j - 1 + 1) = k := by omega
  simpa only [hij', hjk', Nat.add_assoc] using hmain

/-- Zero adjacent curvature propagates equality of consecutive slopes. -/
theorem adjacentSlope_succ_eq_of_curvature_eq_zero
    (t z : ℕ → ℝ) (i : ℕ)
    (h : adjacentCurvature t z i = 0) :
    adjacentSlope t z (i + 1) = adjacentSlope t z i :=
  (adjacentCurvature_eq_zero_iff t z i).mp h

/-- The change in adjacent slope across any finite run is exactly the sum of
the intervening adjacent curvatures. This is the telescoping core of the
all-triple compression in the progress report. -/
theorem adjacentSlope_telescoping
    (t z : ℕ → ℝ) (i n : ℕ) :
    adjacentSlope t z (i + n) =
      adjacentSlope t z i +
        ∑ k ∈ Finset.range n, adjacentCurvature t z (i + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Nat.add_succ]
      rw [show adjacentCurvature t z (i + n) =
          adjacentSlope t z (i + n + 1) - adjacentSlope t z (i + n) by
        rfl]
      rw [ih]
      ring

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
    simpa only [adjacentCurvature, adjacentSlope] using
      adjacentCurvature_affine t a b i hgap₀ hgap₁

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
      simp only [map_add, LinearMap.add_apply]
      ring
    _ = B q q + B (r - q) (r - q) := by
      rw [hqk, hkq]
      ring

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

/-- Exact two-block completion of squares. The final term is the scalar
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
  exact mul_nonneg (div_nonneg (mul_nonneg ha hb) hab.le) (sq_nonneg _)

/-- For strictly positive block weights, the common-optimizer penalty vanishes
exactly when the two separate optimizers agree. -/
theorem twoBlock_gluing_eq_zero_iff
    (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a * b / (a + b)) * (u - v) ^ 2 = 0 ↔ u = v := by
  have hc : 0 < a * b / (a + b) :=
    div_pos (mul_pos ha hb) (add_pos ha hb)
  constructor
  · intro h
    have hs : (u - v) ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_left (ne_of_gt hc)
    nlinarith
  · rintro rfl
    ring

/-- A positive activated atom below `p*q` cannot belong to the fibers of two
distinct primes `p` and `q`. The positivity assumption is essential because
every natural number divides zero. -/
theorem distinct_prime_fibers_disjoint_below_product
    {p q g Y : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hg : 0 < g) (hgY : g ≤ Y) (hY : Y < p * q) :
    ¬(p ∣ g ∧ q ∣ g) := by
  rintro ⟨hpg, hqg⟩
  have hcop : p.Coprime q := (Nat.coprime_primes hp hq).2 hpq
  have hpqg : p * q ∣ g := hcop.mul_dvd_of_dvd_of_dvd hpg hqg
  have hle : p * q ≤ g := Nat.le_of_dvd hg hpqg
  exact (not_lt_of_ge (hle.trans hgY)) hY

/-- Division-free form of activated-atom locality. If `4Y < x²`, no positive
`g ≤ Y` is divisible by two distinct primes lying above `x/2`. -/
theorem no_two_large_prime_divisors
    {x Y g p q : ℕ}
    (hY : 4 * Y < x ^ 2) (hgY : g ≤ Y) (hg : 0 < g)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpx : x < 2 * p) (hqx : x < 2 * q)
    (hpg : p ∣ g) (hqg : q ∣ g) : False := by
  have hcop : p.Coprime q := (Nat.coprime_primes hp hq).2 hpq
  have hpqdvd : p * q ∣ g := hcop.mul_dvd_of_dvd_of_dvd hpg hqg
  have hpqle : p * q ≤ g := Nat.le_of_dvd hg hpqdvd
  nlinarith

/-- With positive total weight, the common weighted mean minimizes the sum of
the two block losses. -/
theorem twoBlock_mean_minimizes
    (a b u v x : ℝ) (hab : 0 < a + b) :
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
    (returnEnergy diagonal eta primePower remainder rayleigh : ℝ)
    (hreturn : returnEnergy = diagonal - eta * primePower + remainder) :
    returnEnergy * rayleigh =
      (diagonal - eta * primePower + remainder) * rayleigh := by
  rw [hreturn]

/-- Normalizing the coordinate by a nonzero common scale changes curvature by
that scale and its one-row Green denominator by the square, so the normalized
certificate is invariant. This removes the artificial `1/x` denominators
from exact arithmetic. -/
theorem scaled_curvature_ratio
    (scale delta green : ℝ) (hscale : scale ≠ 0) (hgreen : green ≠ 0) :
    (scale * delta) ^ 2 / (scale ^ 2 * green) =
      delta ^ 2 / green := by
  field_simp [hscale, hgreen]

/-- The exact asymptotic scale in revised target N4/M1: the supplied
nonnegative energy must be little-o of the reciprocal logarithm. This
definition records the open target and supplies no witness. -/
def ActualInnovationLittleO (energy : ℕ → ℝ) : Prop :=
  energy =o[atTop] (fun n : ℕ => (Real.log (n : ℝ))⁻¹)

/-- The report's revised local-to-global target requires both the internal
innovation energy and the boundary gluing energy at the same reciprocal-log
scale. -/
def RevisedN4M1Target (innovationEnergy boundaryEnergy : ℕ → ℝ) : Prop :=
  ActualInnovationLittleO innovationEnergy ∧
    ActualInnovationLittleO boundaryEnergy

theorem RevisedN4M1Target.innovation
    {innovationEnergy boundaryEnergy : ℕ → ℝ}
    (h : RevisedN4M1Target innovationEnergy boundaryEnergy) :
    ActualInnovationLittleO innovationEnergy := h.1

theorem RevisedN4M1Target.boundary
    {innovationEnergy boundaryEnergy : ℕ → ℝ}
    (h : RevisedN4M1Target innovationEnergy boundaryEnergy) :
    ActualInnovationLittleO boundaryEnergy := h.2

end

end RiemannResearch.RH.PrimeGapCurvature
