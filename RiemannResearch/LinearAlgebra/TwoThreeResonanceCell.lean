/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The finite quadratic form of a two-three resonance cell

Source: independently derived continuation of Christian Noack's arithmetic
research, 15 September 2026. This module verifies the finite leading quadratic
form and its exact dual optimum. It does not assert an asymptotic estimate
for the actual packet Gram matrix, or a lower bound for residual correlations.
-/

namespace RiemannResearch.LinearAlgebra.TwoThreeResonanceCell
noncomputable section

structure CellVector where
  x0 : ℝ
  x1 : ℝ
  x2 : ℝ
  y0 : ℝ
  y1 : ℝ

def binarySum (a : CellVector) : ℝ := a.x0 + a.x1 + a.x2
def ternarySum (a : CellVector) : ℝ := a.y0 + a.y1
def curvature (a : CellVector) : ℝ := a.x0 - 2 * a.x1 + a.x2
def binaryDifference (a : CellVector) : ℝ := a.x0 - a.x2
def ternaryDifference (a : CellVector) : ℝ := a.y0 - a.y1

def Compatible (a : CellVector) : Prop := binarySum a = ternarySum a

def dot (h a : CellVector) : ℝ :=
  h.x0*a.x0 + h.x1*a.x1 + h.x2*a.x2 + h.y0*a.y0 + h.y1*a.y1

def sizeSq (a : CellVector) : ℝ :=
  a.x0^2 + a.x1^2 + a.x2^2 + a.y0^2 + a.y1^2

/-- Leading Gram energy after screening the two old packets. -/
def energy (a : CellVector) : ℝ :=
  a.x0^2 + a.x1^2 + a.x2^2 + 2*(a.y0^2+a.y1^2) +
    (2:ℝ)/3 * (2*a.x0*a.y0 + a.x1*a.y0 + a.x1*a.y1 + 2*a.x2*a.y1) -
    (binarySum a)^2/9 - (ternarySum a)^2/2

/-- Exact sum of four squares; the fifth direction is the cycle relation. -/
theorem energy_squares (a : CellVector) :
    energy a = (2*binarySum a + 3*ternarySum a)^2/18 +
      (curvature a)^2/6 +
      (binaryDifference a + 2*ternaryDifference a/3)^2/2 +
      7*(ternaryDifference a)^2/9 := by
  unfold energy binarySum ternarySum curvature binaryDifference ternaryDifference
  ring

theorem energy_nonneg (a : CellVector) : 0 ≤ energy a := by
  rw [energy_squares]
  positivity

/-- Only scalar multiples of the exact five-packet cycle have zero energy. -/
theorem energy_eq_zero_iff (a : CellVector) :
    energy a = 0 ↔ ∃ t : ℝ, a.x0=t ∧ a.x1=t ∧ a.x2=t ∧ a.y0= -t ∧ a.y1= -t := by
  constructor
  · intro hz
    have he := energy_squares a
    have h0 : (2*binarySum a + 3*ternarySum a)^2 = 0 := by
      nlinarith [sq_nonneg (curvature a),
        sq_nonneg (binaryDifference a + 2*ternaryDifference a/3),
        sq_nonneg (ternaryDifference a)]
    have h1 : (curvature a)^2 = 0 := by
      nlinarith [sq_nonneg (2*binarySum a + 3*ternarySum a),
        sq_nonneg (binaryDifference a + 2*ternaryDifference a/3),
        sq_nonneg (ternaryDifference a)]
    have h2 : (binaryDifference a + 2*ternaryDifference a/3)^2 = 0 := by
      nlinarith [sq_nonneg (2*binarySum a + 3*ternarySum a),
        sq_nonneg (curvature a), sq_nonneg (ternaryDifference a)]
    have h3 : (ternaryDifference a)^2 = 0 := by
      nlinarith [sq_nonneg (2*binarySum a + 3*ternarySum a),
        sq_nonneg (curvature a),
        sq_nonneg (binaryDifference a + 2*ternaryDifference a/3)]
    have z0 := (sq_eq_zero_iff).mp h0
    have z1 := (sq_eq_zero_iff).mp h1
    have z2 := (sq_eq_zero_iff).mp h2
    have z3 := (sq_eq_zero_iff).mp h3
    unfold binarySum ternarySum curvature binaryDifference ternaryDifference at *
    exact ⟨a.x0, rfl, by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨t, h0, h1, h2, h3, h4⟩
    simp only [energy, binarySum, ternarySum, h0, h1, h2, h3, h4]
    ring

/-- Uniform upper eigenvalue bound, including the cycle direction. -/
theorem energy_le (a : CellVector) : energy a ≤ (7:ℝ)/3 * sizeSq a := by
  have hid : (7:ℝ)/3 * sizeSq a - energy a =
      (5*binarySum a-3*ternarySum a)^2/45 + 7*(ternarySum a)^2/15 +
      2*(curvature a)^2/9 + (2*binaryDifference a-ternaryDifference a)^2/6 := by
    unfold sizeSq energy binarySum ternarySum curvature binaryDifference ternaryDifference
    ring
  have hn : 0 ≤ (7:ℝ)/3 * sizeSq a - energy a := by rw [hid]; positivity
  linarith

/-- Coercivity on the orthogonal complement of the cycle. -/
theorem compatible_coercivity (a : CellVector) (ha : Compatible a) :
    (2:ℝ)/3 * sizeSq a ≤ energy a := by
  have hy : a.y1 = a.x0+a.x1+a.x2-a.y0 := by
    unfold Compatible binarySum ternarySum at ha
    linarith
  have hid : energy a - (2:ℝ)/3 * sizeSq a =
      5*(binarySum a)^2/6 + (curvature a)^2/18 +
      (binaryDifference a+2*ternaryDifference a)^2/6 := by
    unfold sizeSq energy binarySum ternarySum curvature binaryDifference ternaryDifference
    rw [hy]
    ring
  have hn : 0 ≤ energy a - (2:ℝ)/3 * sizeSq a := by rw [hid]; positivity
  linarith

/-- Four actual source quantities determine the leading dual gain. -/
def sourceEnergy (h : CellVector) : ℝ :=
  (binarySum h)^2/2 + (curvature h)^2/6 +
    (9:ℝ)/14 * (binaryDifference h-ternaryDifference h/3)^2 +
    (ternaryDifference h)^2/4

theorem sourceEnergy_alternative (h : CellVector) :
    sourceEnergy h = (binarySum h)^2/2 + (curvature h)^2/6 +
      (binaryDifference h)^2/2 +
      (9:ℝ)/28 * (ternaryDifference h-2*binaryDifference h/3)^2 := by
  unfold sourceEnergy
  ring

/-- Completion of squares gives the exact dual upper bound, without an inverse. -/
theorem dual_completion (h a : CellVector) (hh : Compatible h) :
    sourceEnergy h - (2*dot h a-energy a) =
      (2*binarySum a+3*ternarySum a-3*binarySum h)^2/18 +
      (curvature a-curvature h)^2/6 +
      (binaryDifference a+2*ternaryDifference a/3-binaryDifference h)^2/2 +
      (7:ℝ)/9 * (ternaryDifference a -
        (9:ℝ)/14*(ternaryDifference h-2*binaryDifference h/3))^2 := by
  have hy : h.y1 = h.x0+h.x1+h.x2-h.y0 := by
    unfold Compatible binarySum ternarySum at hh
    linarith
  unfold sourceEnergy dot energy binarySum ternarySum curvature binaryDifference ternaryDifference
  rw [hy]
  ring

theorem dual_le_sourceEnergy (h a : CellVector) (hh : Compatible h) :
    2*dot h a - energy a ≤ sourceEnergy h := by
  have hn : 0 ≤ sourceEnergy h - (2*dot h a-energy a) := by
    rw [dual_completion h a hh]
    positivity
  linarith

/-- The unique maximizing coefficient vector in the compatible gauge. -/
def optimizer (h : CellVector) : CellVector :=
  let s := 3*binarySum h/5
  let w := curvature h
  let v := (9:ℝ)/14*(ternaryDifference h-2*binaryDifference h/3)
  let u := binaryDifference h-2*v/3
  ⟨s/3+w/6+u/2, s/3-w/3, s/3+w/6-u/2, s/2+v/2, s/2-v/2⟩

theorem optimizer_compatible (h : CellVector) : Compatible (optimizer h) := by
  unfold Compatible binarySum ternarySum optimizer
  dsimp
  ring

theorem optimizer_attains (h : CellVector) (hh : Compatible h) :
    2*dot h (optimizer h)-energy (optimizer h) = sourceEnergy h := by
  have he := dual_completion h (optimizer h) hh
  have hz : sourceEnergy h-(2*dot h (optimizer h)-energy (optimizer h)) = 0 := by
    rw [he]
    unfold optimizer binarySum ternarySum curvature binaryDifference ternaryDifference
    dsimp
    ring
  linarith

/-- Sharp lower control of compatible source size by the dual energy. -/
theorem sourceEnergy_ge (h : CellVector) (hh : Compatible h) :
    (3:ℝ)/7 * sizeSq h ≤ sourceEnergy h := by
  have hy : h.y1 = h.x0+h.x1+h.x2-h.y0 := by
    unfold Compatible binarySum ternarySum at hh
    linarith
  have hid : sourceEnergy h-(3:ℝ)/7 * sizeSq h =
      (binarySum h)^2/7 + 2*(curvature h)^2/21 +
      (3:ℝ)/28 * (2*binaryDifference h-ternaryDifference h)^2 := by
    unfold sourceEnergy sizeSq binarySum curvature binaryDifference ternaryDifference
    rw [hy]
    ring
  have hn : 0 ≤ sourceEnergy h-(3:ℝ)/7 * sizeSq h := by rw [hid]; positivity
  linarith

end
end RiemannResearch.LinearAlgebra.TwoThreeResonanceCell
