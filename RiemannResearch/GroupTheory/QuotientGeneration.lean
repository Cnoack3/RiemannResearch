/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Quotient-image generation and the missing-kernel obstruction

A finite counterexample showing that subgroups whose images generate a
quotient need not generate the ambient group; adjoining the quotient kernel
repairs the conclusion.

Source: user-provided 5 August 2026 E8 manuscript, discussion after
Proposition 7.5. This module formalizes the counterexample and repair only.
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
