/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib

/-!
# Appendix-A binary-icosahedral row: inner `D₄ ⊔ D₄` certificate

Matrices act on row vectors from the right.  For a norm-two row root `a`,
`refl a` is `I - (Q aᵀ) a`, hence sends `x` to
`x - (x Q aᵀ) a`.

The matrices `w`, `j`, and `r` below are the evaluated Appendix-A words

* `w = B A B A B B A B A`,
* `j = B B A B`,
* `r = A A A B A`.

The long reflection products are grouped into blocks of at most four
reflections.  Every block equality is checked by `decide`; this avoids the
exponential kernel reduction caused by one left-associated product of twelve
function-valued matrices.
-/

open Matrix

namespace RiemannResearch.E8.BinaryIcosahedralAtlas

abbrev I8 := Fin 8
abbrev Vec8 := I8 → ℤ
abbrev Mat8 := Matrix I8 I8 ℤ

def A : Mat8 := ![
  ![ 0,  1,  0,  0,  0,  0,  0,  0],
  ![-1,  0,  0,  0,  0,  0,  0,  0],
  ![-1,  0,  0,  1, -1,  1, -1, -1],
  ![ 0, -1, -1,  0, -1, -1,  1, -1],
  ![ 1,  0, -1,  1, -1, -1,  0, -1],
  ![ 0,  1, -1, -1,  1, -1,  1,  0],
  ![-1,  0, -1, -1,  0, -1,  1, -1],
  ![ 0, -1,  1, -1,  1,  0,  1,  1]
]

def B : Mat8 := ![
  ![0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0],
  ![1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1]
]

def Q : Mat8 := ![
  ![ 2,  0,  0, -1,  0,  1,  0, -1],
  ![ 0,  2,  1,  0, -1,  0,  1,  0],
  ![ 0,  1,  2,  0,  0, -1,  0, -1],
  ![-1,  0,  0,  2,  1,  0,  1,  0],
  ![ 0, -1,  0,  1,  2,  0,  0, -1],
  ![ 1,  0, -1,  0,  0,  2,  1,  0],
  ![ 0,  1,  0,  1,  0,  1,  2,  0],
  ![-1,  0, -1,  0, -1,  0,  0,  2]
]

-- Evaluated forms of `BABABBABA`, `BBAB`, and `AAABA`.
def w : Mat8 := ![
  ![ 0,  1,  0,  0,  0,  0,  0,  0],
  ![-1,  0,  0,  0,  0,  0,  0,  0],
  ![-1,  0,  1, -1,  1,  1,  0,  1],
  ![ 0, -1,  1,  1, -1,  1, -1,  0],
  ![ 1,  0,  1,  1,  0,  1, -1,  1],
  ![ 0,  1, -1,  1, -1,  0, -1, -1],
  ![-1,  0,  0,  1, -1,  1, -1, -1],
  ![ 0, -1, -1,  0, -1, -1,  1, -1]
]

def j : Mat8 := ![
  ![-1, -1,  1,  0, -1,  1,  0, -1],
  ![ 1, -1,  0,  1, -1, -1,  1,  0],
  ![ 0,  0,  0,  1,  0,  0,  0,  0],
  ![ 0,  0, -1,  0,  0,  0,  0,  0],
  ![-1,  1, -1,  0,  0,  1, -1, -1],
  ![-1, -1,  0, -1, -1,  0,  1, -1],
  ![ 0, -1, -1,  0, -1, -1,  1, -1],
  ![ 1,  0,  0, -1,  1, -1,  1,  1]
]

def r : Mat8 := ![
  ![ 0,  1,  1,  0,  1,  1, -1,  1],
  ![-1,  0,  0,  1, -1,  1, -1, -1],
  ![-1, -1,  1,  0, -1,  1,  0, -1],
  ![ 1, -1,  0,  1, -1, -1,  1,  0],
  ![ 1, -1,  1,  0,  0, -1,  1,  1],
  ![ 1,  1,  0,  1,  1,  0, -1,  1],
  ![ 0,  0,  0,  1,  0,  0,  0,  0],
  ![ 0,  0, -1,  0,  0,  0,  0,  0]
]

/-! ## Certificates for the Appendix-A words -/

-- `BAB | ABB | ABA`.
def wWord1 : Mat8 := B * A * B
def wWord2 : Mat8 := A * B * B
def wWord3 : Mat8 := A * B * A

def wWord1Val : Mat8 := ![
  ![-1,1,-1,0,0,1,-1,-1], ![-1,-1,0,-1,-1,0,1,-1],
  ![-1,-1,1,0,-1,1,0,-1], ![1,-1,0,1,-1,-1,1,0],
  ![0,0,0,1,0,0,0,0], ![0,0,-1,0,0,0,0,0],
  ![0,-1,-1,0,-1,-1,1,-1], ![1,0,0,-1,1,-1,1,1]
]

def wWord2Val : Mat8 := ![
  ![0,0,0,0,0,1,0,0], ![0,0,0,0,-1,0,0,0],
  ![0,1,-1,1,-1,0,-1,-1], ![-1,0,-1,-1,0,-1,1,-1],
  ![-1,1,-1,-1,1,0,0,-1], ![-1,-1,1,-1,0,1,1,0],
  ![-1,-1,0,-1,-1,0,1,-1], ![1,-1,1,0,0,-1,1,1]
]

def wWord3Val : Mat8 := ![
  ![0,-1,-1,0,-1,-1,1,-1], ![1,0,0,-1,1,-1,1,1],
  ![1,1,-1,0,1,-1,0,1], ![-1,1,0,-1,1,1,-1,0],
  ![-1,1,-1,0,0,1,-1,-1], ![-1,-1,0,-1,-1,0,1,-1],
  ![0,0,0,-1,0,0,0,0], ![0,0,1,0,0,0,0,0]
]

theorem wWord1_eq : wWord1 = wWord1Val := by decide
theorem wWord2_eq : wWord2 = wWord2Val := by decide
theorem wWord3_eq : wWord3 = wWord3Val := by decide

theorem w_eq_AB_word :
    w = (B * A * B) * (A * B * B) * (A * B * A) := by
  change w = wWord1 * wWord2 * wWord3
  rw [wWord1_eq, wWord2_eq, wWord3_eq]
  decide

-- `BB | AB`.
def jWord1 : Mat8 := B * B
def jWord2 : Mat8 := A * B

def jWord1Val : Mat8 := ![
  ![0,0,0,0,1,0,0,0], ![0,0,0,0,0,1,0,0],
  ![1,0,0,0,0,0,0,0], ![0,1,0,0,0,0,0,0],
  ![0,0,1,0,0,0,0,0], ![0,0,0,1,0,0,0,0],
  ![0,0,0,0,0,0,1,0], ![0,0,0,0,0,0,0,1]
]

def jWord2Val : Mat8 := ![
  ![0,0,0,1,0,0,0,0], ![0,0,-1,0,0,0,0,0],
  ![-1,1,-1,0,0,1,-1,-1], ![-1,-1,0,-1,-1,0,1,-1],
  ![-1,-1,1,0,-1,1,0,-1], ![1,-1,0,1,-1,-1,1,0],
  ![0,-1,-1,0,-1,-1,1,-1], ![1,0,0,-1,1,-1,1,1]
]

theorem jWord1_eq : jWord1 = jWord1Val := by decide
theorem jWord2_eq : jWord2 = jWord2Val := by decide

theorem j_eq_AB_word : j = (B * B) * (A * B) := by
  change j = jWord1 * jWord2
  rw [jWord1_eq, jWord2_eq]
  decide

-- `AAA | BA`.
def rWord1 : Mat8 := A * A * A
def rWord2 : Mat8 := B * A

def rWord1Val : Mat8 := ![
  ![0,-1,0,0,0,0,0,0], ![1,0,0,0,0,0,0,0],
  ![1,0,0,-1,1,-1,1,1], ![0,1,1,0,1,1,-1,1],
  ![-1,0,1,-1,1,1,0,1], ![0,-1,1,1,-1,1,-1,0],
  ![1,0,1,1,0,1,-1,1], ![0,1,-1,1,-1,0,-1,-1]
]

def rWord2Val : Mat8 := ![
  ![-1,0,0,1,-1,1,-1,-1], ![0,-1,-1,0,-1,-1,1,-1],
  ![1,0,-1,1,-1,-1,0,-1], ![0,1,-1,-1,1,-1,1,0],
  ![0,1,0,0,0,0,0,0], ![-1,0,0,0,0,0,0,0],
  ![-1,0,-1,-1,0,-1,1,-1], ![0,-1,1,-1,1,0,1,1]
]

theorem rWord1_eq : rWord1 = rWord1Val := by decide
theorem rWord2_eq : rWord2 = rWord2Val := by decide

theorem r_eq_AB_word : r = (A * A * A) * (B * A) := by
  change r = rWord1 * rWord2
  rw [rWord1_eq, rWord2_eq]
  decide

/-! ## Small relation and order certificates for `⟨w,j,r⟩` -/

theorem w_sq : w * w = -(1 : Mat8) := by decide
theorem j_sq : j * j = -(1 : Mat8) := by decide
theorem w_pow_four : w * w * w * w = (1 : Mat8) := by decide
theorem j_pow_four : j * j * j * j = (1 : Mat8) := by decide
theorem r_pow_three : r * r * r = (1 : Mat8) := by decide
theorem w_sq_ne_one : w * w ≠ (1 : Mat8) := by decide
theorem j_sq_ne_one : j * j ≠ (1 : Mat8) := by decide
theorem r_ne_one : r ≠ (1 : Mat8) := by decide

-- Inverse-free forms of `jwj⁻¹ = w⁻¹`, `rwr⁻¹ = w²j`, and `rjr⁻¹ = wj`.
theorem j_w_j : j * w * j = w := by decide
theorem r_w_relation : r * w = w * w * j * r := by decide
theorem r_j_relation : r * j = w * j * r := by decide

-- Simple roots: central node first, followed by the three leaves.
def a0 : Vec8 := ![-1, -1, 0, -1,  0, 0,  1,  0]
def a1 : Vec8 := ![ 0,  0, 0,  1, -1, 1, -1, -1]
def a2 : Vec8 := ![ 0,  1, 0,  0,  0, 0, -1,  0]
def a3 : Vec8 := ![ 1,  0, 1,  1,  0, 0,  0,  1]

def b0 : Vec8 := ![-1,  0, 0, -1, 0, 0,  1, -1]
def b1 : Vec8 := ![ 0,  0, 0,  1, 0, 0, -1,  0]
def b2 : Vec8 := ![ 0,  1, 0,  0, 1, 1, -1,  1]
def b3 : Vec8 := ![ 1, -1, 1,  0, 0, 0,  0,  1]

def roots : I8 → Vec8 := ![a0, a1, a2, a3, b0, b1, b2, b3]

def rootGram : Mat8 :=
  fun i j => ∑ k : I8, ∑ l : I8, roots i k * Q k l * roots j l

def d4d4Gram : Mat8 := ![
  ![ 2, -1, -1, -1,  0,  0,  0,  0],
  ![-1,  2,  0,  0,  0,  0,  0,  0],
  ![-1,  0,  2,  0,  0,  0,  0,  0],
  ![-1,  0,  0,  2,  0,  0,  0,  0],
  ![ 0,  0,  0,  0,  2, -1, -1, -1],
  ![ 0,  0,  0,  0, -1,  2,  0,  0],
  ![ 0,  0,  0,  0, -1,  0,  2,  0],
  ![ 0,  0,  0,  0, -1,  0,  0,  2]
]

theorem rootGram_eq_d4d4 : rootGram = d4d4Gram := by
  decide

def refl (root : Vec8) : Mat8 :=
  fun i j =>
    (if i = j then 1 else 0) -
      (∑ k : I8, Q i k * root k) * root j

/-! ## Reflection blocks for `w` -/

def wA1 : Mat8 := refl a0 * refl a1 * refl a2
def wA2 : Mat8 := refl a0 * refl a1 * refl a3
def wB1 : Mat8 := refl b2 * refl b0 * refl b1
def wB2 : Mat8 := refl b3 * refl b0 * refl b1

def wA1Val : Mat8 := ![
  ![0,0,0,-1,0,0,0,0], ![-1,0,0,0,-1,1,0,-1],
  ![-1,-1,1,0,-1,1,0,-1], ![0,1,0,1,0,0,-1,0],
  ![0,1,0,0,1,0,-1,0], ![0,1,0,-1,1,0,0,1],
  ![0,1,0,0,0,0,0,0], ![1,0,0,1,0,0,0,1]
]

def wA2Val : Mat8 := ![
  ![1,-1,1,0,0,0,1,1], ![-1,0,0,0,-1,1,0,-1],
  ![-1,-1,1,0,-1,1,0,-1], ![-1,0,-1,0,0,0,0,-1],
  ![0,0,0,0,1,0,0,0], ![0,0,0,-1,1,0,1,1],
  ![-1,0,-1,-1,0,0,1,-1], ![0,1,-1,0,0,0,-1,0]
]

def wB1Val : Mat8 := ![
  ![1,0,0,1,0,0,-1,0], ![1,1,0,1,0,0,-1,1],
  ![0,1,1,0,1,1,-1,1], ![0,0,0,0,0,0,1,0],
  ![0,0,0,-1,1,0,1,0], ![1,-1,0,1,-1,0,0,0],
  ![1,0,0,1,0,0,0,1], ![0,-1,0,0,-1,-1,1,0]
]

def wB2Val : Mat8 := ![
  ![1,1,-1,1,0,0,-1,0], ![1,0,1,1,0,0,-1,1],
  ![1,0,1,0,0,0,0,1], ![0,-1,1,0,0,0,1,0],
  ![0,0,0,-1,1,0,1,0], ![0,0,0,1,0,1,-1,0],
  ![1,-1,1,1,0,0,0,1], ![-1,0,0,0,0,0,0,0]
]

theorem wA1_eq : wA1 = wA1Val := by decide
theorem wA2_eq : wA2 = wA2Val := by decide
theorem wB1_eq : wB1 = wB1Val := by decide
theorem wB2_eq : wB2 = wB2Val := by decide

theorem w_eq_reflections :
    w =
      (refl a0 * refl a1 * refl a2) *
      (refl a0 * refl a1 * refl a3) *
      (refl b2 * refl b0 * refl b1) *
      (refl b3 * refl b0 * refl b1) := by
  change w = wA1 * wA2 * wB1 * wB2
  rw [wA1_eq, wA2_eq, wB1_eq, wB2_eq]
  decide

/-! ## Reflection blocks for `j` -/

def jA1 : Mat8 := refl a0 * refl a2 * refl a3
def jA2 : Mat8 := refl a0 * refl a1 * refl a2
def jB1 : Mat8 := refl b0 * refl b1 * refl b2
def jB2 : Mat8 := refl b0 * refl b1 * refl b3

def jA1Val : Mat8 := ![
  ![1,0,1,0,0,0,0,1], ![-1,0,0,-1,0,0,1,0],
  ![-1,-1,1,-1,0,0,1,0], ![-1,1,-1,0,0,0,-1,-1],
  ![0,1,0,0,1,0,-1,0], ![0,1,0,0,0,1,-1,0],
  ![-1,1,-1,-1,0,0,0,-1], ![0,0,-1,0,0,0,0,0]
]

def jB1Val : Mat8 := ![
  ![1,0,0,1,0,0,-1,0], ![1,0,0,1,-1,-1,0,0],
  ![1,0,1,0,0,0,0,1], ![0,0,0,0,0,0,1,0],
  ![0,0,0,-1,1,0,1,0], ![0,-1,0,1,-1,0,0,-1],
  ![1,-1,0,1,-1,-1,1,0], ![-1,0,0,0,0,0,0,0]
]

def jB2Val : Mat8 := ![
  ![0,1,-1,1,0,0,-1,-1], ![1,1,0,1,0,0,-1,1],
  ![0,1,0,0,0,0,0,0], ![1,-1,1,0,0,0,1,1],
  ![0,0,0,-1,1,0,1,0], ![0,0,0,1,0,1,-1,0],
  ![1,0,0,1,0,0,0,1], ![0,-1,1,0,0,0,0,1]
]

theorem jA1_eq : jA1 = jA1Val := by decide
theorem jA2_eq : jA2 = wA1Val := by decide
theorem jB1_eq : jB1 = jB1Val := by decide
theorem jB2_eq : jB2 = jB2Val := by decide

theorem j_eq_reflections :
    j =
      (refl a0 * refl a2 * refl a3) *
      (refl a0 * refl a1 * refl a2) *
      (refl b0 * refl b1 * refl b2) *
      (refl b0 * refl b1 * refl b3) := by
  change j = jA1 * jA2 * jB1 * jB2
  rw [jA1_eq, jA2_eq, jB1_eq, jB2_eq]
  decide

/-! ## Reflection blocks for `r` -/

def rA1 : Mat8 := refl a0 * refl a1 * refl a0 * refl a2
def rA2 : Mat8 := refl a0 * refl a3 * refl a0 * refl a2
def rB : Mat8 := refl b1 * refl b0 * refl b2 * refl b0

def rA1Val : Mat8 := ![
  ![1,0,0,0,0,0,0,0], ![-1,0,0,0,-1,1,0,-1],
  ![-1,-1,1,0,-1,1,0,-1], ![0,1,0,1,0,0,-1,0],
  ![0,1,0,0,1,0,-1,0], ![1,1,0,0,1,0,0,1],
  ![0,1,0,0,0,0,0,0], ![0,0,0,0,0,0,0,1]
]

def rA2Val : Mat8 := ![
  ![1,0,1,0,0,0,0,1], ![0,0,0,0,0,0,1,0],
  ![0,-1,1,0,0,0,1,0], ![0,1,-1,1,0,0,-1,-1],
  ![0,1,0,0,1,0,-1,0], ![0,1,0,0,0,1,-1,0],
  ![0,1,-1,0,0,0,0,-1], ![0,0,-1,0,0,0,0,0]
]

def rBVal : Mat8 := ![
  ![0,1,0,0,1,1,-1,0], ![0,1,0,1,0,0,-1,0],
  ![0,0,1,0,0,0,0,0], ![1,-1,0,1,-1,-1,1,0],
  ![1,-1,0,0,0,-1,1,0], ![0,0,0,1,0,1,-1,0],
  ![0,0,0,1,0,0,0,0], ![0,0,0,0,0,0,0,1]
]

theorem rA1_eq : rA1 = rA1Val := by decide
theorem rA2_eq : rA2 = rA2Val := by decide
theorem rB_eq : rB = rBVal := by decide

theorem r_eq_reflections :
    r =
      (refl a0 * refl a1 * refl a0 * refl a2) *
      (refl a0 * refl a3 * refl a0 * refl a2) *
      (refl b1 * refl b0 * refl b2 * refl b0) := by
  change r = rA1 * rA2 * rB
  rw [rA1_eq, rA2_eq, rB_eq]
  decide

end RiemannResearch.E8.BinaryIcosahedralAtlas
