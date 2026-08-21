/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.ContinuousNonabelianH1

/-!
# Refinement functoriality for finite-stage continuous nonabelian H¹

This module constructs the transition maps between the finite quotients
attached to action-compatible factorizations of one continuous cocycle.  It
also records the contravariant inclusion of kernel-fixed coefficient groups,
proves pointwise compatibility of the descended cocycles, and constructs a
common refinement of any two chosen finite stages.

Source for the finite-stage viewpoint and terminology: J.-P. Serre,
*Galois Cohomology*, Chapter I, §5.  The formal transition-map construction is
the quotient-group functoriality of nested open normal subgroups.
-/

namespace RiemannResearch.GaloisCohomology

universe u v

variable {Γ : Type u} {G : Type v}
variable [Group Γ] [Group G] [MulDistribMulAction Γ G]
variable [TopologicalSpace Γ] [TopologicalSpace G]

namespace ContinuousNonabelianCocycle.ActionCompatibleFiniteQuotientFactorization

variable {a : ContinuousNonabelianCocycle Γ G}

/-- A refinement from `D` to `E` means that the kernel chosen by `D` is
contained in the kernel chosen by `E`.  Thus the finite quotient of `D` maps
canonically to the finite quotient of `E`. -/
structure Refinement
    (D E : ActionCompatibleFiniteQuotientFactorization a) : Prop where
  subgroup_le : D.subgroup ≤ E.subgroup

namespace Refinement

variable {D E F : ActionCompatibleFiniteQuotientFactorization a}

/-- Every finite-stage factorization refines itself. -/
protected theorem refl
    (D : ActionCompatibleFiniteQuotientFactorization a) : Refinement D D :=
  ⟨le_rfl⟩

/-- Refinements compose by inclusion of their open normal kernels. -/
protected theorem trans (r : Refinement D E) (s : Refinement E F) :
    Refinement D F :=
  ⟨r.subgroup_le.trans s.subgroup_le⟩

/-- The transition homomorphism from a finer quotient to a coarser quotient. -/
def quotientMap (r : Refinement D E) :
    Γ ⧸ (D.subgroup : Subgroup Γ) →*
      Γ ⧸ (E.subgroup : Subgroup Γ) :=
  QuotientGroup.map (D.subgroup : Subgroup Γ)
    (E.subgroup : Subgroup Γ) (MonoidHom.id Γ) (by
      intro σ hσ
      change σ ∈ (E.subgroup : Subgroup Γ)
      exact r.subgroup_le hσ)

/-- The transition homomorphism sends the class of an element to its class at
the coarser stage. -/
@[simp] theorem quotientMap_mk (r : Refinement D E) (σ : Γ) :
    r.quotientMap (QuotientGroup.mk σ) = QuotientGroup.mk σ := by
  rfl

/-- The identity refinement induces the identity quotient map. -/
@[simp] theorem quotientMap_refl
    (D : ActionCompatibleFiniteQuotientFactorization a)
    (q : Γ ⧸ (D.subgroup : Subgroup Γ)) :
    (Refinement.refl D).quotientMap q = q := by
  refine Quotient.inductionOn' q ?_
  intro σ
  rfl

/-- Quotient transition maps respect composition of refinements. -/
@[simp] theorem quotientMap_trans
    (r : Refinement D E) (s : Refinement E F)
    (q : Γ ⧸ (D.subgroup : Subgroup Γ)) :
    (r.trans s).quotientMap q = s.quotientMap (r.quotientMap q) := by
  refine Quotient.inductionOn' q ?_
  intro σ
  rfl

/-- Kernel-fixed coefficients at the coarser stage include into the
kernel-fixed coefficients at the finer stage. -/
def fixedCoefficientMap (r : Refinement D E) :
    E.FixedCoefficientGroup →* D.FixedCoefficientGroup where
  toFun x :=
    ⟨x.1, (FixedPoints.mem_subgroup D.subgroup G x.1).2 (by
      intro h
      exact (FixedPoints.mem_subgroup E.subgroup G x.1).1 x.2
        ⟨h.1, r.subgroup_le h.2⟩)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The coefficient inclusion is equivariant for the corresponding quotient
transition map. -/
theorem fixedCoefficientMap_smul
    (r : Refinement D E)
    (q : Γ ⧸ (D.subgroup : Subgroup Γ))
    (x : E.FixedCoefficientGroup) :
    r.fixedCoefficientMap (r.quotientMap q • x) =
      q • r.fixedCoefficientMap x := by
  refine Quotient.inductionOn' q ?_
  intro σ
  rfl

/-- Raw descended cocycle functions agree after quotient transition. -/
theorem descended_quotientMap
    (r : Refinement D E)
    (q : Γ ⧸ (D.subgroup : Subgroup Γ)) :
    E.descended (r.quotientMap q) = D.descended q := by
  refine Quotient.inductionOn' q ?_
  intro σ
  rw [quotientMap_mk, E.factor σ, D.factor σ]

/-- The genuine descended cocycles are compatible with both the quotient
transition map and the inclusion of fixed coefficient groups. -/
@[simp] theorem fixedCoefficientMap_descendedCocycle
    (r : Refinement D E)
    (q : Γ ⧸ (D.subgroup : Subgroup Γ)) :
    r.fixedCoefficientMap (E.descendedCocycle (r.quotientMap q)) =
      D.descendedCocycle q := by
  apply Subtype.ext
  exact r.descended_quotientMap q

end Refinement

/-- Restrict an action-compatible factorization to a smaller open normal
kernel. -/
def pullbackToSubgroup
    (D : ActionCompatibleFiniteQuotientFactorization a)
    (H : OpenNormalSubgroup Γ) (hH : H ≤ D.subgroup) :
    ActionCompatibleFiniteQuotientFactorization a := by
  have htriv : ∀ h : H, a h.1 = 1 := by
    intro h
    exact D.trivial_on ⟨h.1, hH h.2⟩
  have hfix : ∀ h : H, ∀ σ : Γ, h.1 • a σ = a σ := by
    intro h σ
    exact D.fixes_range ⟨h.1, hH h.2⟩ σ
  have hinv : ∀ (σ : Γ) (h : H), a (σ * h.1) = a σ := by
    intro σ h
    rw [a.1.map_mul', htriv h]
    simp
  let descended : Γ ⧸ (H : Subgroup Γ) → G :=
    fun q => Quotient.liftOn' q (fun σ => a σ) (by
      intro x y hxy
      have hmem : x⁻¹ * y ∈ (H : Subgroup Γ) :=
        QuotientGroup.leftRel_apply.mp hxy
      let h : H := ⟨x⁻¹ * y, hmem⟩
      have hmul : x * h.1 = y := by
        simp [h]
      rw [← hmul, hinv x h])
  refine ⟨⟨H, htriv, descended, ?_⟩, hfix⟩
  intro σ
  exact QuotientGroup.quotient_liftOn_mk (fun σ => a σ) _ σ

/-- A common action-compatible refinement of any two finite-stage
factorizations of the same cocycle. -/
def commonRefinement
    (D E : ActionCompatibleFiniteQuotientFactorization a) :
    ActionCompatibleFiniteQuotientFactorization a :=
  D.pullbackToSubgroup (D.subgroup ⊓ E.subgroup) inf_le_left

/-- The common refinement maps to its left-hand stage. -/
theorem commonRefinementLeft
    (D E : ActionCompatibleFiniteQuotientFactorization a) :
    Refinement (D.commonRefinement E) D :=
  ⟨inf_le_left⟩

/-- The common refinement maps to its right-hand stage. -/
theorem commonRefinementRight
    (D E : ActionCompatibleFiniteQuotientFactorization a) :
    Refinement (D.commonRefinement E) E :=
  ⟨inf_le_right⟩

end ContinuousNonabelianCocycle.ActionCompatibleFiniteQuotientFactorization

end RiemannResearch.GaloisCohomology
