/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Rational-involution finite certificates

Incidence, binary, determinant, dimension, cohomology-rank, and stabilizer
arithmetic from the paper *Rational Involutions and Hidden Weyl-7 Monodromy
toward Serre's Conjecture II for E8* (27 July 2026).
-/

namespace RiemannResearch.E8.RationalInvolutionsAudit

/-! ## The 15 by 15 complement-incidence matrix -/

def dot4 (x y : Nat) : Bool :=
  (Nat.testBit x 0 && Nat.testBit y 0) ^^
  (Nat.testBit x 1 && Nat.testBit y 1) ^^
  (Nat.testBit x 2 && Nat.testBit y 2) ^^
  (Nat.testBit x 3 && Nat.testBit y 3)

def incidenceEntry (i j : Fin 15) : ℤ :=
  if dot4 (i.val + 1) (j.val + 1) then 1 else 0

theorem incidence_row_sum :
    ∀ i : Fin 15, ∑ j : Fin 15, incidenceEntry i j = 8 := by
  set_option maxRecDepth 100000 in decide

/-- Exact Gram identity B B-transpose = 4 (I + J), entry by entry. -/
theorem incidence_gram :
    ∀ i j : Fin 15,
      ∑ u : Fin 15, incidenceEntry i u * incidenceEntry j u =
        if i = j then 8 else 4 := by
  set_option maxRecDepth 100000 in decide

theorem incidence_trace :
    ∑ i : Fin 15, incidenceEntry i i = 8 := by
  set_option maxRecDepth 100000 in decide

/-! ## Printed binary certificates -/

theorem tits_binary_certificate :
    Nat.xor (Nat.xor (Nat.xor (Nat.xor 0x10024 0x88) 0xfe) 0x9600) 0x9652 =
      0x10000 := by
  set_option maxRecDepth 100000 in decide

/-- The printed decimal right side of (14.4) is 2^32. -/
theorem s4_overlap_binary_certificate :
    Nat.xor (Nat.xor (Nat.xor (Nat.xor 169 118) 222) 43374) 4295010671 =
      2 ^ 32 := by
  set_option maxRecDepth 100000 in decide

theorem kleinFour_binary_certificate :
    Nat.xor (Nat.xor 168 42240) 107944 = 2 ^ 16 := by
  set_option maxRecDepth 100000 in decide

/-! ## Integral degree-56 defect and dimension arithmetic -/

def degree56OrbitDeterminant (c1 c2 c3 c4 : ℤ) : ℤ :=
  -16 * (c2 - 2 * c3) ^ 3 * (c2 - c4) ^ 3 * (3 * c2 - c4) *
    (-4 * c1 + c2 + 2 * c3 + 2 * c4)

theorem degree56OrbitDeterminant_divisible_by_sixteen
    (c1 c2 c3 c4 : ℤ) :
    16 ∣ degree56OrbitDeterminant c1 c2 c3 c4 := by
  refine ⟨-((c2 - 2 * c3) ^ 3 * (c2 - c4) ^ 3 * (3 * c2 - c4) *
    (-4 * c1 + c2 + 2 * c3 + 2 * c4)), ?_⟩
  simp [degree56OrbitDeterminant]
  ring

theorem degree56OrbitDeterminant_minimizer :
    degree56OrbitDeterminant (-1) (-1) 0 (-2) = 16 := by
  norm_num [degree56OrbitDeterminant]

theorem cartanTransporter_dimension_arithmetic :
    248 * 247 / 2 = 30628 ∧
    120 * 119 / 2 + 128 * 127 / 2 = 15268 ∧
    15268 + 128 = 15396 ∧
    30628 - 15396 = 15232 ∧
    15268 - 120 = 15148 := by
  norm_num

theorem cartanTransporter_cubicEquation_count :
    (120 * 119 / 2) * 128 + (128 * 127 * 126 / 6) = 1255296 := by
  norm_num

/-- Arithmetic consistency of tables (14.2), (14.6), (14.8), and (14.11). -/
theorem finiteCohomology_rank_arithmetic :
    8 - 7 = 1 ∧ 7 - 7 = 0 ∧ 8 - 8 = 0 ∧
    10 - 5 = 5 ∧ 8 - 6 = 2 ∧
    5 + 3 = 8 ∧ 2 + 2 = 4 ∧
    4232 - 4054 - 176 = 2 ∧
    72 - 52 - 16 = 4 ∧
    8 - 6 = 2 := by
  norm_num

theorem packetStabilizer_order_arithmetic :
    20160 / 15 = 1344 ∧
    20160 / 35 = 576 ∧
    16 * (6 * 6) = 576 ∧
    16 * 360 = 5760 ∧
    5760 = 10 * 576 := by
  norm_num

end RiemannResearch.E8.RationalInvolutionsAudit
