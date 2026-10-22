/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact two-prime squarefree convolution logarithm and exponential

The triple (a,b,c) represents 1+a*X+b*Y+c*X*Y in
R[X,Y]/(X^2,Y^2). Its convolution logarithm is (a,b,c-a*b),
and its exponential has mixed coefficient c+a*b.

Source: T. Sinclair, *Finite free convolution via reproducing kernels and
squarefree algebras*, arXiv:2606.10870v2, Section 4, for the nilpotent
logarithm and cumulant formula. This module specializes those standard
formulas to two labeled primes. The reciprocal-slope calculation is the
application needed for the user's squarefree legal lattice proposal.

No ordinary pointwise exponential or ordinary Dirichlet convolution is
identified with this nilpotent product. No Hilbert energy estimate is assumed.
-/

noncomputable section
namespace RiemannResearch.NumberTheory.SquarefreeCumulantPair

abbrev Coordinates := ℝ × ℝ × ℝ

/-- Product of normalized squarefree coefficient arrays. -/
def star (x y : Coordinates) : Coordinates :=
  (x.1 + y.1, x.2.1 + y.2.1,
    x.2.2 + y.2.2 + x.1 * y.2.1 + x.2.1 * y.1)

/-- Nilpotent logarithm, with the constant coefficient suppressed. -/
def logStar (x : Coordinates) : Coordinates :=
  (x.1, x.2.1, x.2.2 - x.1 * x.2.1)

/-- Nilpotent exponential, whose suppressed constant coefficient is one. -/
def expStar (x : Coordinates) : Coordinates :=
  (x.1, x.2.1, x.2.2 + x.1 * x.2.1)

@[simp] theorem logStar_expStar (x : Coordinates) : logStar (expStar x) = x := by
  rcases x with ⟨a, b, c⟩
  ext <;> dsimp [logStar, expStar]
  all_goals ring

@[simp] theorem expStar_logStar (x : Coordinates) : expStar (logStar x) = x := by
  rcases x with ⟨a, b, c⟩
  ext <;> dsimp [logStar, expStar]
  all_goals ring

/-- The convolution logarithm linearizes the actual squarefree product. -/
theorem logStar_star (x y : Coordinates) :
    logStar (star x y) = logStar x + logStar y := by
  rcases x with ⟨a, b, c⟩
  rcases y with ⟨u, v, w⟩
  ext <;> dsimp [logStar, star]
  all_goals ring

theorem expStar_add (x y : Coordinates) :
    expStar (x + y) = star (expStar x) (expStar y) := by
  rcases x with ⟨a, b, c⟩
  rcases y with ⟨u, v, w⟩
  ext <;> dsimp [expStar, star]
  all_goals ring

theorem star_assoc (x y z : Coordinates) :
    star (star x y) z = star x (star y z) := by
  rcases x with ⟨a, b, c⟩
  rcases y with ⟨u, v, w⟩
  rcases z with ⟨r, s, t⟩
  ext <;> dsimp [star] <;> ring

theorem star_comm (x y : Coordinates) : star x y = star y x := by
  rcases x with ⟨a, b, c⟩
  rcases y with ⟨u, v, w⟩
  ext <;> dsimp [star] <;> ring

/-- The mean-zero primitive constraint is a linear functional of moments. -/
def reciprocalSlope (p q : ℝ) (x : Coordinates) : ℝ :=
  1 + x.1 / p + x.2.1 / q + x.2.2 / (p * q)

theorem reciprocalSlope_expStar (p q a b k : ℝ) (hp : p ≠ 0) (hq : q ≠ 0) :
    reciprocalSlope p q (expStar (a, b, k)) =
      (1 + a / p) * (1 + b / q) + k / (p * q) := by
  dsimp [reciprocalSlope, expStar]
  field_simp [hp, hq]
  ring

/-- An arbitrary pair of prime cumulants has exactly one composite
cumulant giving a balanced legal primitive. -/
theorem reciprocalSlope_expStar_eq_zero_iff (p q a b k : ℝ)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    reciprocalSlope p q (expStar (a, b, k)) = 0 ↔ k = -(p + a) * (q + b) := by
  dsimp [reciprocalSlope, expStar]
  field_simp [hp, hq]
  constructor <;> intro h <;> nlinarith

/-- Reciprocal slope is not a character of the nilpotent coefficient
algebra. This is the exact defect even on a single prime. -/
theorem reciprocalSlope_singleton_defect (p q a b : ℝ) (hp : p ≠ 0) :
    reciprocalSlope p q (star (a, 0, 0) (b, 0, 0)) =
      reciprocalSlope p q (a, 0, 0) * reciprocalSlope p q (b, 0, 0) -
        a * b / p ^ 2 := by
  simp only [reciprocalSlope, star, zero_div, zero_mul, mul_zero, add_zero]
  field_simp [hp]
  ring

end RiemannResearch.NumberTheory.SquarefreeCumulantPair
