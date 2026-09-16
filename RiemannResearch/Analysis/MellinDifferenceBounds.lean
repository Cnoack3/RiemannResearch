/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CesaroFiniteCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Quantitative first and second Mellin differences, proved by real-variable calculus. -/
noncomputable section
open Set
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Analysis.Cesaro

/-- A second finite difference is bounded by the supremum of the actual second derivative. -/
theorem norm_second_difference_le (f f' f'' : ℝ → ℂ) (a B : ℝ)
    (h1 : ∀ x ∈ Icc a (a + 2), HasDerivAt f (f' x) x)
    (h2 : ∀ x ∈ Icc a (a + 2), HasDerivAt f' (f'' x) x)
    (hb : ∀ x ∈ Icc a (a + 2), ‖f'' x‖ ≤ B) :
    ‖f a - 2 * f (a + 1) + f (a + 2)‖ ≤ B := by
  let g : ℝ → ℂ := fun x => f (x + 1) - f x
  let g' : ℝ → ℂ := fun x => f' (x + 1) - f' x
  have hd : ∀ x ∈ Icc a (a + 1), HasDerivAt g (g' x) x := by
    intro x hx
    have hx0 : x ∈ Icc a (a + 2) := ⟨hx.1, by linarith [hx.2]⟩
    have hx1 : x + 1 ∈ Icc a (a + 2) := by
      constructor <;> linarith [hx.1, hx.2]
    have hh : HasDerivAt (fun y => f (y + 1)) (f' (x + 1)) x :=
      (h1 (x + 1) hx1).comp_add_const x 1
    have h := hh.sub (h1 x hx0)
    change HasDerivAt (fun y => f (y + 1) - f y) (f' (x + 1) - f' x) x at h
    exact h
  have hg : ∀ x ∈ Ico a (a + 1), ‖g' x‖ ≤ B := by
    intro x hx
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := f') (f' := f'') (a := x) (b := x + 1) (C := B)
      (fun y hy => (h2 y (by constructor <;> linarith [hx.1, hx.2, hy.1, hy.2])).hasDerivWithinAt)
      (fun y hy => hb y (by constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]))
      (x + 1) (by constructor <;> linarith)
    simpa [g'] using h
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := g) (f' := g') (a := a) (b := a + 1) (C := B)
    (fun x hx => (hd x hx).hasDerivWithinAt) hg
    (a + 1) (by constructor <;> linarith)
  have he : g (a + 1) - g a = f a - 2 * f (a + 1) + f (a + 2) := by
    dsimp [g]
    rw [show a + 1 + 1 = a + 2 by ring]
    ring
  rw [he] at h
  simpa using h

/-- Derivative of the Mellin power on the positive real half-line. -/
theorem power_hasDerivAt (s : ℂ) (hs : 0 < s.re) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s))
      (-s * (x : ℂ) ^ (-s - 1)) x := by
  have hs0 : s ≠ 0 := by intro h; simpa [h] using hs
  exact hasDerivAt_ofReal_cpow_const (ne_of_gt hx) (neg_ne_zero.mpr hs0)

/-- The actual second derivative, without an assumed smoothness oracle. -/
theorem power_derivative_hasDerivAt (s : ℂ) (hs : 0 < s.re) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => -s * (y : ℂ) ^ (-s - 1))
      (s * (s + 1) * (x : ℂ) ^ (-s - 2)) x := by
  have he : -s - 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.zero_re] at hr
    linarith
  have h := (hasDerivAt_ofReal_cpow_const (ne_of_gt hx) he).const_mul (-s)
  rw [show -s - 1 - 1 = -s - 2 by ring] at h
  exact h.congr_deriv (by ring)

/-- First Mellin difference bound at an arbitrary positive real base. -/
theorem real_first_difference_bound (s : ℂ) (hs : 0 < s.re) (a : ℝ) (ha : 0 < a) :
    ‖(a : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s)‖ ≤
      ‖s‖ * a ^ (-s.re - 1) := by
  have hd : ∀ x ∈ Icc a (a + 1),
      HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (-s))
        (-s * (x : ℂ) ^ (-s - 1)) (Icc a (a + 1)) x := by
    intro x hx
    exact (power_hasDerivAt s hs x (lt_of_lt_of_le ha hx.1)).hasDerivWithinAt
  have hb : ∀ x ∈ Ico a (a + 1),
      ‖-s * (x : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
    intro x hx
    rw [norm_mul, norm_neg,
      Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le ha hx.1)]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha hx.1 (by linarith)) (norm_nonneg s)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb
    (a + 1) (by constructor <;> linarith)
  rw [norm_sub_rev]
  simpa using h

/-- The weighted second coefficient has one additional power of decay. -/
theorem mellinSecond_norm_le (s : ℂ) (hs : 0 < s.re) (n : ℕ) (hn : 0 < n) :
    ‖mellinSecond s n‖ ≤ ‖s * (s + 1)‖ * (n : ℝ) ^ (-s.re - 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd1 : ∀ x ∈ Icc (n : ℝ) ((n : ℝ) + 2),
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x :=
    fun x hx => power_hasDerivAt s hs x (lt_of_lt_of_le hnR hx.1)
  have hd2 : ∀ x ∈ Icc (n : ℝ) ((n : ℝ) + 2),
      HasDerivAt (fun y : ℝ => -s * (y : ℂ) ^ (-s - 1))
        (s * (s + 1) * (x : ℂ) ^ (-s - 2)) x :=
    fun x hx => power_derivative_hasDerivAt s hs x (lt_of_lt_of_le hnR hx.1)
  have hb : ∀ x ∈ Icc (n : ℝ) ((n : ℝ) + 2),
      ‖s * (s + 1) * (x : ℂ) ^ (-s - 2)‖ ≤
        ‖s * (s + 1)‖ * (n : ℝ) ^ (-s.re - 2) := by
    intro x hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le hnR hx.1)]
    simp only [Complex.sub_re, Complex.neg_re, Complex.re_ofNat]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hnR hx.1 (by linarith)) (norm_nonneg _)
  have h := norm_second_difference_le _ _ _ (n : ℝ)
    (‖s * (s + 1)‖ * (n : ℝ) ^ (-s.re - 2)) hd1 hd2 hb
  have he : mellinSecond s n = (n : ℂ) *
      ((n : ℂ) ^ (-s) - 2 * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) +
        (((n : ℝ) + 2 : ℝ) : ℂ) ^ (-s)) := by
    simp only [mellinSecond, mellinFirst, show n + 1 + 1 = n + 2 by omega, Nat.cast_add, Nat.cast_one,
      Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_ofNat,
      Nat.cast_ofNat]
    ring
  rw [he, norm_mul, Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)).trans_eq
  have hp : (n : ℝ) * (n : ℝ) ^ (-s.re - 2) = (n : ℝ) ^ (-s.re - 1) := by
    calc
      _ = (n : ℝ) ^ (1 + (-s.re - 2)) := by rw [Real.rpow_add hnR, Real.rpow_one]
      _ = _ := by congr 1 <;> ring
  calc
    _ = ‖s * (s + 1)‖ * ((n : ℝ) * (n : ℝ) ^ (-s.re - 2)) := by ring
    _ = _ := by rw [hp]

/-- First coefficient bound in the positive integer convention used in the series. -/
theorem mellinFirst_norm_le (s : ℂ) (hs : 0 < s.re) (n : ℕ) (hn : 0 < n) :
    ‖mellinFirst s n‖ ≤ ‖s‖ * (n : ℝ) ^ (-s.re - 1) := by
  simpa [mellinFirst, Nat.cast_add, Nat.cast_one] using
    real_first_difference_bound s hs (n : ℝ) (by exact_mod_cast hn)

end RiemannResearch.Analysis.Cesaro
