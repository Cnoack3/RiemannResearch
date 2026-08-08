/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.E8.SerreIIProgramChecks

/-!
# Section 7 and Appendix arithmetic audit

This module records the finite arithmetic printed in Section 7 and Appendix A
of the 5 August 2026 E8 Serre II manuscript. It also gives a concrete finite
counterexample to the inference immediately after Proposition 7.5: subgroups
whose images generate a presentation quotient need not generate the ambient
group. The final conjunct shows the missing repair—adjoin the quotient kernel.

None of these declarations verifies the reported GAP subgroup enumeration.
-/

namespace RiemannResearch.GroupTheory

/-- Ambient additive group for the quotient-generation audit. -/
abbrev quotientGenerationAmbient := ZMod 2 × ZMod 3

/-- Projection onto the finite quotient used in the audit. -/
def quotientGenerationProjection : quotientGenerationAmbient →+ ZMod 2 where
  toFun := Prod.fst
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A two-primary lift that surjects onto the quotient but misses the
three-primary kernel direction. -/
def quotientGenerationLift : AddSubgroup quotientGenerationAmbient :=
  AddSubgroup.prod ⊤ ⊥

/-- The lift maps onto the quotient but is a proper subgroup of the source.
Adding the quotient kernel repairs generation.

This is the finite additive model of the omitted-kernel issue after PDF
Proposition 7.5.
-/
theorem quotientGeneration_counterexample :
    quotientGenerationLift.map quotientGenerationProjection = ⊤ ∧
      quotientGenerationLift ≠ ⊤ ∧
      quotientGenerationLift ⊔ quotientGenerationProjection.ker = ⊤ := by
  constructor
  · apply top_unique
    intro q hq
    change q ∈ quotientGenerationLift.map quotientGenerationProjection
    refine ⟨(q, 0), ?_, rfl⟩
    change (q, 0) ∈
      (⊤ : AddSubgroup (ZMod 2)).prod (⊥ : AddSubgroup (ZMod 3))
    rw [AddSubgroup.mem_prod]
    simp
  constructor
  · intro htop
    have hm : ((0, 1) : quotientGenerationAmbient) ∈
        quotientGenerationLift := by
      rw [htop]
      trivial
    change
      (0 ∈ (⊤ : AddSubgroup (ZMod 2)) ∧
        1 ∈ (⊥ : AddSubgroup (ZMod 3))) at hm
    norm_num at hm
  · apply top_unique
    rintro ⟨a, b⟩ _
    rw [show (a, b) = (a, 0) + (0, b) by simp]
    have ha : (a, 0) ∈ quotientGenerationLift := by
      change (a, 0) ∈
        (⊤ : AddSubgroup (ZMod 2)).prod (⊥ : AddSubgroup (ZMod 3))
      rw [AddSubgroup.mem_prod]
      simp
    have hb : (0, b) ∈ quotientGenerationProjection.ker := by
      change quotientGenerationProjection (0, b) = 0
      rfl
    exact (quotientGenerationLift ⊔ quotientGenerationProjection.ker).add_mem
      ((show quotientGenerationLift ≤
          quotientGenerationLift ⊔ quotientGenerationProjection.ker from
        le_sup_left) ha)
      ((show quotientGenerationProjection.ker ≤
          quotientGenerationLift ⊔ quotientGenerationProjection.ker from
        le_sup_right) hb)

end RiemannResearch.GroupTheory

namespace RiemannResearch.E8

/-- The count, orbit-cardinality, and binary-icosahedral order arithmetic
printed in Section 7 and Appendix A. -/
theorem sectionSevenAppendix_arithmetic :
    (2880 : ℕ) = 2 ^ 6 * 3 ^ 2 * 5 ∧
      313 - 10 = 303 ∧
      150 + 153 = 303 ∧
      5 + 5 + 1 + 1 = 12 ∧
      120 / 12 + 120 / 120 = 11 ∧
      120 / 20 + 120 / 24 = 11 ∧
      24 * 20 / 4 = 120 := by
  norm_num

/-- The full-Weyl and five survivor-envelope Bezout identities, together
with the five corresponding gcd computations. -/
theorem sectionSevenAppendix_bezout_and_gcd :
    ((-1417 : ℤ) * 135 + 16 * 11200 + 12096 = 1) ∧
      ((-73 : ℤ) * 135 - 2 * 1120 + 12096 = 1) ∧
      ((15 : ℤ) * 15 - 5 * 1120 + 5376 = 1) ∧
      ((-17 : ℤ) * 135 - 2 * 1120 + 4536 = 1) ∧
      ((-57 : ℤ) * 135 - 2 * 40 + 7776 = 1) ∧
      ((13 : ℤ) * 25 - 9 * 36 = 1) ∧
      Nat.gcd (Nat.gcd 135 1120) 12096 = 1 ∧
      Nat.gcd (Nat.gcd 15 1120) 5376 = 1 ∧
      Nat.gcd (Nat.gcd 135 1120) 4536 = 1 ∧
      Nat.gcd (Nat.gcd 135 40) 7776 = 1 ∧
      Nat.gcd 25 36 = 1 := by
  norm_num

end RiemannResearch.E8
