/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib

/-!
# Arithmetic of the order-nine A9 triality packet

This file checks the signed half-spin residue calculation used for the
order-nine example in the ramified inflation channel.  It verifies only the
finite arithmetic after the triality model has been chosen; it does not
construct the `A₉` embedding in the `E₈` Weyl group.
-/

namespace RiemannResearch.E8

abbrev SignPattern := Fin 4 → ℤ

/-- A half-spin exponent modulo nine.  Multiplication by five is division by
two in `ZMod 9`. -/
def halfSpinResidue (s : SignPattern) : ZMod 9 :=
  (5 : ZMod 9) * (s 0 + 2 * s 1 + 3 * s 2 + 4 * s 3)

def signPattern (a b c d : ℤ) : SignPattern
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => d

def oddHalfSpinResidues : List (ZMod 9) :=
  [signPattern 1 1 1 (-1), signPattern 1 1 (-1) 1,
   signPattern 1 (-1) 1 1, signPattern 1 (-1) (-1) (-1),
   signPattern (-1) 1 1 1, signPattern (-1) 1 (-1) (-1),
   signPattern (-1) (-1) 1 (-1), signPattern (-1) (-1) (-1) 1].map
    halfSpinResidue

def evenHalfSpinResidues : List (ZMod 9) :=
  [signPattern 1 1 1 1, signPattern 1 1 (-1) (-1),
   signPattern 1 (-1) 1 (-1), signPattern 1 (-1) (-1) 1,
   signPattern (-1) 1 1 (-1), signPattern (-1) 1 (-1) 1,
   signPattern (-1) (-1) 1 1, signPattern (-1) (-1) (-1) (-1)].map
    halfSpinResidue

/-- One half-spin parity gives all eight nonzero residues modulo nine. -/
theorem oddHalfSpinResidues_perm :
    oddHalfSpinResidues.Perm ([1, 2, 3, 4, 5, 6, 7, 8] : List (ZMod 9)) := by
  decide

/-- The other half-spin parity gives two fixed exponents and the six primitive
ninth-root exponents. -/
theorem evenHalfSpinResidues_perm :
    evenHalfSpinResidues.Perm ([0, 0, 1, 2, 4, 5, 7, 8] : List (ZMod 9)) := by
  decide

/-- The fixed-point-free characteristic polynomial `Φ₃ Φ₉` has determinant
nine at one. -/
theorem a9Triality_determinant_order :
    ((Polynomial.cyclotomic 3 ℤ).eval 1) *
      ((Polynomial.cyclotomic 9 ℤ).eval 1) = 9 := by
  rw [Polynomial.eval_one_cyclotomic_prime (R := ℤ) (p := 3)
    (hn := ⟨by norm_num⟩)]
  have h9 : (9 : ℕ) = 3 ^ (1 + 1) := by norm_num
  rw [h9, Polynomial.eval_one_cyclotomic_prime_pow (R := ℤ) (p := 3) 1
    (hn := ⟨by norm_num⟩)]
  norm_num

end RiemannResearch.E8
