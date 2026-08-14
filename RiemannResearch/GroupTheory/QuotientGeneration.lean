/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.Basic
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

/-- If subgroup images generate a quotient, then the original subgroups
together with the homomorphism kernel generate the source.

This is the general repair for the omitted-kernel step following Proposition
7.5 of the user-provided 5 August 2026 E8 memorandum. No surjectivity
hypothesis is needed: generation of the target by the subgroup images already
forces it.
-/
theorem kernel_sup_iSup_eq_top_of_iSup_map_eq_top
    {G Q I : Type*} [Group G] [Group Q]
    (f : G →* Q) (H : I → Subgroup G)
    (hgen : (⨆ i, (H i).map f) = ⊤) :
    f.ker ⊔ (⨆ i, H i) = ⊤ := by
  apply top_unique
  intro g hg
  have hker : f.ker ≤ f.ker ⊔ (⨆ i, H i) := le_sup_left
  have hmapped : (f.ker ⊔ (⨆ i, H i)).map f = ⊤ := by
    rw [Subgroup.map_sup, Subgroup.map_iSup, hgen]
    simp
  have hg' : g ∈ ((f.ker ⊔ (⨆ i, H i)).map f).comap f := by
    change f g ∈ (f.ker ⊔ (⨆ i, H i)).map f
    rw [hmapped]
    trivial
  rwa [Subgroup.comap_map_eq_self hker] at hg'

/-- Corrected simultaneous fixed-point principle for quotient presentations.

A point fixed by the presentation kernel and by every lifted subgroup is
globally fixed when the lifted subgroup images generate the presentation
quotient. In the Galois application, the kernel is
`Gal(k_s / E)`, and its fixed-point coset is supplied by the chosen finite
Galois splitting field `E/k`.
-/
theorem fixed_of_fixed_on_kernel_and_quotient_generators
    {G Q X I : Type*} [Group G] [Group Q] [MulAction G X]
    (f : G →* Q) (H : I → Subgroup G)
    (hgen : (⨆ i, (H i).map f) = ⊤) {x : X}
    (hker : ∀ n : f.ker, (n : G) • x = x)
    (hH : ∀ i (h : H i), (h : G) • x = x) :
    ∀ g : G, g • x = x := by
  intro g
  have hkernel_le : f.ker ≤ MulAction.stabilizer G x := by
    intro n hn
    exact hker ⟨n, hn⟩
  have hfamily_le : (⨆ i, H i) ≤ MulAction.stabilizer G x := by
    apply iSup_le
    intro i h hh
    exact hH i ⟨h, hh⟩
  have htop : (⊤ : Subgroup G) ≤ MulAction.stabilizer G x := by
    rw [← kernel_sup_iSup_eq_top_of_iSup_map_eq_top f H hgen]
    exact sup_le hkernel_le hfamily_le
  exact htop (by simp)

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
