/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.BigOperators
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open scoped BigOperators

/-!
# Rational interval certificates for real computations

The endpoints are exact rationals. Soundness is proved in `ℝ`, and every
numerical endpoint check can be discharged by `norm_num`. In particular,
square-root endpoints are supplied with rational squared-bound certificates;
this does not depend on an unverified floating-point square-root computation.
-/

namespace RiemannResearch

structure RatInterval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

namespace RatInterval

def Contains (I : RatInterval) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def point (q : ℚ) : RatInterval := ⟨q, q⟩
def add (I J : RatInterval) : RatInterval := ⟨I.lo + J.lo, I.hi + J.hi⟩
def neg (I : RatInterval) : RatInterval := ⟨-I.hi, -I.lo⟩
def sub (I J : RatInterval) : RatInterval := add I (neg J)
def mul (I J : RatInterval) : RatInterval :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩
def inv (I : RatInterval) : RatInterval := ⟨I.hi⁻¹, I.lo⁻¹⟩
def div (I J : RatInterval) : RatInterval := mul I (inv J)

variable {I J : RatInterval} {x y : ℝ}

theorem contains_point (q : ℚ) : (point q).Contains (q : ℝ) :=
  ⟨le_rfl, le_rfl⟩

theorem contains_weaken (hx : I.Contains x)
    (hl : J.lo ≤ I.lo) (hu : I.hi ≤ J.hi) : J.Contains x := by
  have hl' : (J.lo : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hl
  have hu' : (I.hi : ℝ) ≤ (J.hi : ℝ) := by exact_mod_cast hu
  exact ⟨hl'.trans hx.1, hx.2.trans hu'⟩

theorem contains_add (hx : I.Contains x) (hy : J.Contains y) :
    (add I J).Contains (x + y) := by
  simpa only [Contains, add, Rat.cast_add] using
    And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem contains_neg (hx : I.Contains x) : (neg I).Contains (-x) := by
  simpa only [Contains, neg, Rat.cast_neg] using
    And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)

theorem contains_sub (hx : I.Contains x) (hy : J.Contains y) :
    (sub I J).Contains (x - y) := by
  simpa only [sub, sub_eq_add_neg] using contains_add hx (contains_neg hy)

private theorem mul_rectangle_bounds {a b c d x y : ℝ}
    (hxa : a ≤ x) (hxb : x ≤ b) (hyc : c ≤ y) (hyd : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  let L := min (min (a * c) (a * d)) (min (b * c) (b * d))
  let U := max (max (a * c) (a * d)) (max (b * c) (b * d))
  have hlac : L ≤ a * c := (min_le_left _ _).trans (min_le_left _ _)
  have hlad : L ≤ a * d := (min_le_left _ _).trans (min_le_right _ _)
  have hlbc : L ≤ b * c := (min_le_right _ _).trans (min_le_left _ _)
  have hlbd : L ≤ b * d := (min_le_right _ _).trans (min_le_right _ _)
  have huac : a * c ≤ U := (le_max_left _ _).trans (le_max_left _ _)
  have huad : a * d ≤ U := (le_max_right _ _).trans (le_max_left _ _)
  have hubc : b * c ≤ U := (le_max_left _ _).trans (le_max_right _ _)
  have hubd : b * d ≤ U := (le_max_right _ _).trans (le_max_right _ _)
  change L ≤ x * y ∧ x * y ≤ U
  constructor
  · by_cases hy : 0 ≤ y
    · have hla : L ≤ a * y := by
        by_cases ha : 0 ≤ a
        · exact hlac.trans (mul_le_mul_of_nonneg_left hyc ha)
        · exact hlad.trans (mul_le_mul_of_nonpos_left hyd (le_of_not_ge ha))
      exact hla.trans (mul_le_mul_of_nonneg_right hxa hy)
    · have hlb : L ≤ b * y := by
        by_cases hb : 0 ≤ b
        · exact hlbc.trans (mul_le_mul_of_nonneg_left hyc hb)
        · exact hlbd.trans (mul_le_mul_of_nonpos_left hyd (le_of_not_ge hb))
      exact hlb.trans (mul_le_mul_of_nonpos_right hxb (le_of_not_ge hy))
  · by_cases hy : 0 ≤ y
    · have hbu : b * y ≤ U := by
        by_cases hb : 0 ≤ b
        · exact (mul_le_mul_of_nonneg_left hyd hb).trans hubd
        · exact (mul_le_mul_of_nonpos_left hyc (le_of_not_ge hb)).trans hubc
      exact (mul_le_mul_of_nonneg_right hxb hy).trans hbu
    · have hau : a * y ≤ U := by
        by_cases ha : 0 ≤ a
        · exact (mul_le_mul_of_nonneg_left hyd ha).trans huad
        · exact (mul_le_mul_of_nonpos_left hyc (le_of_not_ge ha)).trans huac
      exact (mul_le_mul_of_nonpos_right hxa (le_of_not_ge hy)).trans hau

/-- The four-corner product enclosure is sound for arbitrary endpoint signs. -/
theorem contains_mul (hx : I.Contains x) (hy : J.Contains y) :
    (mul I J).Contains (x * y) := by
  simpa only [Contains, mul, Rat.cast_min, Rat.cast_max, Rat.cast_mul] using
    mul_rectangle_bounds hx.1 hx.2 hy.1 hy.2

/-- Finite sums use the sums of the two endpoint families. -/
def sum {ι : Type*} (s : Finset ι) (f : ι → RatInterval) : RatInterval :=
  ⟨∑ i ∈ s, (f i).lo, ∑ i ∈ s, (f i).hi⟩

theorem contains_sum {ι : Type*} (s : Finset ι)
    (f : ι → RatInterval) (g : ι → ℝ)
    (h : ∀ i ∈ s, (f i).Contains (g i)) :
    (sum s f).Contains (∑ i ∈ s, g i) := by
  simpa [Contains, sum] using
    And.intro (Finset.sum_le_sum (fun i hi => (h i hi).1))
      (Finset.sum_le_sum (fun i hi => (h i hi).2))

/-- Endpoint products give a sharp enclosure when all factors are nonnegative.
This applies directly to the unsigned products in a Gram determinant expansion. -/
def prodNonneg {ι : Type*} (s : Finset ι) (f : ι → RatInterval) : RatInterval :=
  ⟨∏ i ∈ s, (f i).lo, ∏ i ∈ s, (f i).hi⟩

theorem contains_prodNonneg {ι : Type*} (s : Finset ι)
    (f : ι → RatInterval) (g : ι → ℝ)
    (h : ∀ i ∈ s, (f i).Contains (g i))
    (h0 : ∀ i ∈ s, 0 ≤ (f i).lo) :
    (prodNonneg s f).Contains (∏ i ∈ s, g i) := by
  have hl : ∀ i ∈ s, (0 : ℝ) ≤ ((f i).lo : ℝ) := by
    intro i hi
    exact_mod_cast h0 i hi
  have hg : ∀ i ∈ s, (0 : ℝ) ≤ g i :=
    fun i hi => (hl i hi).trans (h i hi).1
  simpa [Contains, prodNonneg] using
    And.intro (Finset.prod_le_prod hl (fun i hi => (h i hi).1))
      (Finset.prod_le_prod hg (fun i hi => (h i hi).2))

/-- A product in a specified list order also supports arbitrary signs. -/
def listProd : List RatInterval → RatInterval
  | [] => point 1
  | I :: Is => mul I (listProd Is)

theorem contains_listProd {ι : Type*} (l : List ι)
    (f : ι → RatInterval) (g : ι → ℝ) :
    (∀ i ∈ l, (f i).Contains (g i)) →
      (listProd (l.map f)).Contains ((l.map g).prod) := by
  induction l with
  | nil =>
      intro h
      simpa [listProd, point, Contains]
  | cons a l ih =>
      intro h
      have ha : (f a).Contains (g a) := h a (by simp)
      have ht : ∀ i ∈ l, (f i).Contains (g i) := by
        intro i hi
        exact h i (by simp [hi])
      simpa only [List.map_cons, List.prod_cons, listProd] using contains_mul ha (ih ht)

/-- Reciprocal endpoints reverse order on a positive interval. -/
theorem contains_inv_pos (hx : I.Contains x) (hl : 0 < I.lo) :
    (inv I).Contains x⁻¹ := by
  have hl' : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hl
  have hx' : 0 < x := lt_of_lt_of_le hl' hx.1
  have hu' : (0 : ℝ) < (I.hi : ℝ) := lt_of_lt_of_le hx' hx.2
  have h1 : (I.hi : ℝ)⁻¹ ≤ x⁻¹ := (inv_le_inv₀ hu' hx').mpr hx.2
  have h2 : x⁻¹ ≤ (I.lo : ℝ)⁻¹ := (inv_le_inv₀ hx' hl').mpr hx.1
  simpa only [Contains, inv, Rat.cast_inv] using And.intro h1 h2

/-- The same reciprocal rule holds on a negative interval. -/
theorem contains_inv_neg (hx : I.Contains x) (hu : I.hi < 0) :
    (inv I).Contains x⁻¹ := by
  have hpos : 0 < (neg I).lo := neg_pos.mpr hu
  have h := contains_neg (contains_inv_pos (contains_neg hx) hpos)
  simpa only [Contains, neg, inv, Rat.cast_neg, Rat.cast_inv, inv_neg,
    neg_neg] using h

theorem contains_div_pos (hx : I.Contains x) (hy : J.Contains y)
    (hl : 0 < J.lo) : (div I J).Contains (x / y) := by
  simpa only [div, div_eq_mul_inv] using contains_mul hx (contains_inv_pos hy hl)

theorem contains_div_neg (hx : I.Contains x) (hy : J.Contains y)
    (hu : J.hi < 0) : (div I J).Contains (x / y) := by
  simpa only [div, div_eq_mul_inv] using contains_mul hx (contains_inv_neg hy hu)

/-- A square-root enclosure needs only rational endpoint square comparisons.
No rational approximation algorithm is trusted by this theorem. -/
theorem contains_sqrt (hx : I.Contains x) (a b : ℚ)
    (hb : 0 ≤ b) (ha2 : a ^ 2 ≤ I.lo) (hb2 : I.hi ≤ b ^ 2) :
    (⟨a, b⟩ : RatInterval).Contains (Real.sqrt x) := by
  have hb' : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have ha2' : (a : ℝ) ^ 2 ≤ (I.lo : ℝ) := by exact_mod_cast ha2
  have hb2' : (I.hi : ℝ) ≤ (b : ℝ) ^ 2 := by exact_mod_cast hb2
  exact ⟨Real.le_sqrt_of_sq_le (ha2'.trans hx.1),
    (Real.sqrt_le_left hb').mpr (hx.2.trans hb2')⟩

/-- Turn a certified interval into the stated absolute decimal error bound. -/
theorem abs_error_le (hx : I.Contains x) (q ε : ℚ)
    (hl : q - ε ≤ I.lo) (hu : I.hi ≤ q + ε) : |x - (q : ℝ)| ≤ (ε : ℝ) := by
  have hl' : (q : ℝ) - (ε : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hl
  have hu' : (I.hi : ℝ) ≤ (q : ℝ) + (ε : ℝ) := by exact_mod_cast hu
  have hxl := hx.1
  have hxu := hx.2
  apply abs_le.mpr
  constructor <;> linarith

end RatInterval
end RiemannResearch
