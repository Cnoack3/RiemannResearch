/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Basic
import RiemannResearch.GaloisCohomology.NonabelianH1

/-!
# Continuous nonabelian first cohomology

This module forms the pointed quotient of continuous nonabelian one-cocycles
by gauge equivalence. It is the continuous version of `NonabelianH1` needed
for the Krull-topological absolute Galois group.

The definition follows the standard pointed-set construction of nonabelian
Galois cohomology; see J.-P. Serre, *Galois Cohomology*, Chapter I, §5. The
reference supports the definition and terminology.
-/

namespace RiemannResearch.GaloisCohomology

universe u v

variable (Γ : Type u) (G : Type v)
variable [Group Γ] [Group G] [MulDistribMulAction Γ G]
variable [TopologicalSpace Γ] [TopologicalSpace G]

/-- A nonabelian one-cocycle whose underlying map is continuous. -/
def ContinuousNonabelianCocycle :=
  {a : NonabelianCocycle Γ G // Continuous a}

namespace ContinuousNonabelianCocycle

variable {Γ G}

instance : CoeFun (ContinuousNonabelianCocycle Γ G) (fun _ => Γ → G) :=
  ⟨fun a => a.1⟩

/-- The continuous trivial cocycle. -/
def trivial : ContinuousNonabelianCocycle Γ G :=
  ⟨NonabelianCocycle.trivial, continuous_const⟩

/-- A nonabelian one-cocycle sends the identity to the identity. -/
theorem map_one (a : ContinuousNonabelianCocycle Γ G) :
    a 1 = 1 := by
  have h := a.1.map_mul' 1 1
  have h' := congrArg (fun x => (a 1)⁻¹ * x) h
  symm
  simpa using h'

/-- A continuous cocycle from a compact space to a discrete coefficient group
has finite image. -/
theorem finite_range
    [CompactSpace Γ] [DiscreteTopology G]
    (a : ContinuousNonabelianCocycle Γ G) :
    (Set.range fun σ => a σ).Finite := by
  exact (isCompact_range a.2).finite_of_discrete

/-- Factorization data for the underlying function of a continuous cocycle
through an open-normal finite quotient.

This deliberately does not claim that descended is a cocycle. To make it a
cocycle one must also descend the Γ-action on the coefficient group, usually
to the subgroup fixed by subgroup. -/
structure FiniteQuotientFactorization
    (a : ContinuousNonabelianCocycle Γ G) where
  /-- The open normal subgroup through which the cocycle function factors. -/
  subgroup : OpenNormalSubgroup Γ
  /-- The cocycle is trivial on the chosen open normal subgroup. -/
  trivial_on : ∀ h : subgroup, a h.1 = 1
  /-- The descended function on the quotient. -/
  descended : Γ ⧸ (subgroup : Subgroup Γ) → G
  /-- Pullback of the descended function is the original cocycle. -/
  factor : ∀ σ : Γ, descended (QuotientGroup.mk σ) = a σ

namespace FiniteQuotientFactorization

/-- The quotient occurring in a finite-quotient factorization is finite. -/
theorem quotient_finite
    [ContinuousMul Γ] [CompactSpace Γ]
    {a : ContinuousNonabelianCocycle Γ G}
    (D : FiniteQuotientFactorization a) :
    Finite (Γ ⧸ (D.subgroup : Subgroup Γ)) :=
  Subgroup.quotient_finite_of_isOpen _
    D.subgroup.toOpenSubgroup.isOpen

end FiniteQuotientFactorization

/-- Every continuous cocycle on a profinite group with discrete coefficients
factors, as a function, through a finite quotient by an open normal subgroup.

The cocycle identity makes the function constant on right cosets once the
chosen subgroup lies in the fiber over 1. -/
theorem exists_finiteQuotientFactorization
    [IsTopologicalGroup Γ] [CompactSpace Γ]
    [TotallyDisconnectedSpace Γ] [DiscreteTopology G]
    (a : ContinuousNonabelianCocycle Γ G) :
    Nonempty (FiniteQuotientFactorization a) := by
  let U : Set Γ := (fun σ => a σ) ⁻¹' ({1} : Set G)
  have hUOpen : IsOpen U :=
    a.2.isOpen_preimage _ (isOpen_discrete {1})
  have hOne : (1 : Γ) ∈ U := map_one a
  obtain ⟨H, hHU⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUOpen hOne
  have htriv : ∀ h : H, a h.1 = 1 := fun h => hHU h.2
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
  refine ⟨⟨H, htriv, descended, ?_⟩⟩
  intro σ
  exact QuotientGroup.quotient_liftOn_mk (fun σ => a σ) _ σ

/-- Gauge equivalence of continuous cocycles. Both endpoints already carry
their continuity proofs, so no separate continuity hypothesis on a chosen
gauge is required. -/
def Cohomologous
    (a b : ContinuousNonabelianCocycle Γ G) : Prop :=
  a.1.Cohomologous b.1

theorem cohomologous_refl
    (a : ContinuousNonabelianCocycle Γ G) : a.Cohomologous a :=
  NonabelianCocycle.cohomologous_refl a.1

theorem cohomologous_symm
    {a b : ContinuousNonabelianCocycle Γ G} :
    a.Cohomologous b → b.Cohomologous a :=
  NonabelianCocycle.cohomologous_symm

theorem cohomologous_trans
    {a b c : ContinuousNonabelianCocycle Γ G} :
    a.Cohomologous b → b.Cohomologous c → a.Cohomologous c :=
  NonabelianCocycle.cohomologous_trans

def setoid : Setoid (ContinuousNonabelianCocycle Γ G) where
  r := Cohomologous
  iseqv := ⟨cohomologous_refl, cohomologous_symm, cohomologous_trans⟩

instance : Setoid (ContinuousNonabelianCocycle Γ G) :=
  setoid

end ContinuousNonabelianCocycle

/-- Continuous nonabelian first cohomology as a pointed quotient. -/
def ContinuousNonabelianH1 :=
  Quotient (ContinuousNonabelianCocycle.setoid (Γ := Γ) (G := G))

namespace ContinuousNonabelianH1

variable {Γ G}

def classOf (a : ContinuousNonabelianCocycle Γ G) :
    ContinuousNonabelianH1 Γ G :=
  Quotient.mk _ a

/-- The distinguished neutral cohomology class. -/
def neutral : ContinuousNonabelianH1 Γ G :=
  classOf ContinuousNonabelianCocycle.trivial

instance : One (ContinuousNonabelianH1 Γ G) :=
  ⟨neutral⟩

/-- Every continuous H¹ class has a representative whose underlying
function factors through a finite quotient of the profinite source. -/
theorem exists_representative_finiteQuotientFactorization
    [IsTopologicalGroup Γ] [CompactSpace Γ]
    [TotallyDisconnectedSpace Γ] [DiscreteTopology G]
    (ξ : ContinuousNonabelianH1 Γ G) :
    ∃ a : ContinuousNonabelianCocycle Γ G,
      classOf a = ξ ∧
        Nonempty
          (ContinuousNonabelianCocycle.FiniteQuotientFactorization a) := by
  refine Quotient.inductionOn ξ ?_
  intro a
  exact
    ⟨a, rfl,
      ContinuousNonabelianCocycle.exists_finiteQuotientFactorization a⟩

end ContinuousNonabelianH1

end RiemannResearch.GaloisCohomology
