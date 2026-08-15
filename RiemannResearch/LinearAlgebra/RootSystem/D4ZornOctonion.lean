/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The split Zorn octonion and its triality tensor

This file gives an explicit eight-coordinate presentation of the split Zorn
octonion over an arbitrary commutative ring. It proves, coefficient by
coefficient, multiplicativity of the norm, the conjugation laws, and the
cyclic and conjugate-reflection symmetries of the para-octonion triality
tensor.

The cyclic/reflection distinction is essential. The tensor is invariant
under cyclic permutation. A transposition is a symmetry only after applying
octonion conjugation in all three slots. Consequently this file does not
identify concrete octonionic triality with the stronger pure-relabeling
interface OrthogonalTrialityTensor.IsSymmetric.

The formulas and the related-triple strategy follow Alsaody--Gille,
*Isotopes of Octonion Algebras, G2-Torsors and Triality*, Remark 3.2,
Lemma 3.3, Proposition 3.10, and Theorem 3.12:
<https://arxiv.org/abs/1704.05229>.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

universe u

namespace Zorn

variable (K : Type u) [CommRing K]

abbrev Octonion := Fin 8 → K

def mul (x y : Octonion K) : Octonion K := ![
  x 0 * y 0 + x 1 * y 4 + x 2 * y 5 + x 3 * y 6,
  x 0 * y 1 + y 7 * x 1 - x 5 * y 6 + x 6 * y 5,
  x 0 * y 2 + y 7 * x 2 - x 6 * y 4 + x 4 * y 6,
  x 0 * y 3 + y 7 * x 3 - x 4 * y 5 + x 5 * y 4,
  y 0 * x 4 + x 7 * y 4 + x 2 * y 3 - x 3 * y 2,
  y 0 * x 5 + x 7 * y 5 + x 3 * y 1 - x 1 * y 3,
  y 0 * x 6 + x 7 * y 6 + x 1 * y 2 - x 2 * y 1,
  x 4 * y 1 + x 5 * y 2 + x 6 * y 3 + x 7 * y 7
]

def norm (x : Octonion K) : K :=
  x 0 * x 7 - x 1 * x 4 - x 2 * x 5 - x 3 * x 6

def conjugate (x : Octonion K) : Octonion K :=
  ![x 7, -x 1, -x 2, -x 3, -x 4, -x 5, -x 6, x 0]

def paraMul (x y : Octonion K) : Octonion K :=
  mul K (conjugate K x) (conjugate K y)

def normPolar (x y : Octonion K) : K :=
  norm K (x + y) - norm K x - norm K y

def trialityTensor (w x y : Octonion K) : K :=
  normPolar K w (paraMul K x y)

def mulLinear : Octonion K →ₗ[K] Octonion K →ₗ[K] Octonion K :=
  LinearMap.mk₂ K (mul K)
    (by
      intro x y z
      ext i
      fin_cases i <;> simp [mul] <;> ring)
    (by
      intro a x y
      ext i
      fin_cases i <;> simp [mul] <;> ring)
    (by
      intro x y z
      ext i
      fin_cases i <;> simp [mul] <;> ring)
    (by
      intro a x y
      ext i
      fin_cases i <;> simp [mul] <;> ring)

def normForm : QuadraticForm K (Octonion K) :=
  QuadraticMap.ofPolar (norm K)
    (by
      intro a x
      simp [norm]
      ring)
    (by
      intro x x' y
      simp [QuadraticMap.polar, norm]
      ring)
    (by
      intro a x y
      simp [QuadraticMap.polar, norm]
      ring)

@[simp] theorem normForm_apply (x : Octonion K) :
    normForm K x = norm K x :=
  rfl

def conjugationLinearEquiv : Octonion K ≃ₗ[K] Octonion K where
  toFun := conjugate K
  invFun := conjugate K
  left_inv x := by
    ext i
    fin_cases i <;> simp [conjugate]
  right_inv x := by
    ext i
    fin_cases i <;> simp [conjugate]
  map_add' x y := by
    ext i
    fin_cases i <;> simp [conjugate] <;> ring
  map_smul' a x := by
    ext i
    fin_cases i <;> simp [conjugate]

@[simp] theorem conjugate_involutive (x : Octonion K) :
    conjugate K (conjugate K x) = x :=
  (conjugationLinearEquiv K).left_inv x

@[simp] theorem conjugate_neg (x : Octonion K) :
    conjugate K (-x) = -conjugate K x := by
  exact (conjugationLinearEquiv K).map_neg x

@[simp] theorem conjugationLinearEquiv_apply (x : Octonion K) :
    conjugationLinearEquiv K x = conjugate K x :=
  rfl

theorem norm_mul (x y : Octonion K) :
    norm K (mul K x y) = norm K x * norm K y := by
  simp [norm, mul]
  ring

@[simp] theorem norm_conjugate (x : Octonion K) :
    norm K (conjugate K x) = norm K x := by
  simp [norm, conjugate]
  ring

theorem conjugate_mul_reverse (x y : Octonion K) :
    conjugate K (mul K x y) =
      mul K (conjugate K y) (conjugate K x) := by
  ext i
  fin_cases i <;> simp [conjugate, mul] <;> ring

theorem conjugate_para_reverse (x y : Octonion K) :
    conjugate K (paraMul K x y) =
      paraMul K (conjugate K y) (conjugate K x) := by
  unfold paraMul
  rw [conjugate_mul_reverse, conjugate_involutive,
    conjugate_involutive]

theorem norm_paraMul (x y : Octonion K) :
    norm K (paraMul K x y) = norm K x * norm K y := by
  rw [paraMul, norm_mul, norm_conjugate, norm_conjugate]

theorem trialityTensor_cycle (w x y : Octonion K) :
    trialityTensor K w x y = trialityTensor K x y w := by
  simp [trialityTensor, normPolar, paraMul, norm, mul, conjugate]
  ring

theorem trialityTensor_cycle_two (w x y : Octonion K) :
    trialityTensor K w x y = trialityTensor K y w x := by
  rw [trialityTensor_cycle K w x y, trialityTensor_cycle K x y w]

theorem trialityTensor_conjugate_reflection (w x y : Octonion K) :
    trialityTensor K (conjugate K w) (conjugate K y)
        (conjugate K x) =
      trialityTensor K w x y := by
  simp [trialityTensor, normPolar, paraMul, norm, mul, conjugate]
  ring

end Zorn

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality
