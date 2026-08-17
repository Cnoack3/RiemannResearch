/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
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

end ContinuousNonabelianH1

end RiemannResearch.GaloisCohomology
