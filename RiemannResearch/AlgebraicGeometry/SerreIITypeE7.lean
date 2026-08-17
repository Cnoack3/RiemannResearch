/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIIFamilyHierarchy
import RiemannResearch.E7.D6A1FiniteCertificate
import RiemannResearch.Logic.PointedKernel

/-!
# The type-E7 Serre-II reduction

This module keeps the project's single Serre-II target unchanged: the base
predicate still denotes perfect fields of cohomological dimension at most two.
It separates the known quasi-split E7 theorem from two precise possible routes
through the arbitrary-form problem.

The first route iterates trivial relative kernels along cyclic extensions of
degree two or three. Chernousov proves that an E7 group becomes split over a
chain of such extensions. The existence of that splitting chain alone does
not supply the relative-kernel statement for each non-quasi-split intermediate
form, so every step records its kernel theorem explicitly.

The second route is the D6+A1 index reduction. The finite certificate in
`E7.D6A1FiniteCertificate` proves that, in the index-four branch, one of the
other two labelled trialitarian components is split. Lean then closes the E7
class from three explicit geometric bridges: the distinguished component of
index less than four neutralizes the class, and a split labelled 12- or
13-component neutralizes the class.

The existing D4 coordinate-module descent theorem helps construct the
underlying descended module needed by this route. It does not yet descend
multiplication, Hopf structure, the D4 group scheme, or the map on fpqc H1, so
it does not construct these three bridges.

Consequently the terminal declarations below are conditional research
reductions, not an unconditional proof for arbitrary E7 forms. They do prove
an exact family-E7 provider once the displayed inputs are supplied, and show
that a counterexample must be non-quasi-split and must evade both routes.

Sources:

* V. Chernousov, *The kernel of the Rost invariant, Serre's Conjecture II and
  the Hasse principle for quasi-split groups 3,6D4, E6, E7*, Math. Ann. 326
  (2003), Theorem 7.1,
  <https://www.math.ualberta.ca/~chernous/ChernousovPublications/RostKernel.pdf>.
* The same paper, Theorem 8.2, proves arbitrary-form E7 only over C2 fields;
  the paper explicitly notes that C2 is stronger than cohomological dimension
  at most two.
-/

universe u x

namespace RiemannResearch.AlgebraicGeometry.SerreII

open RiemannResearch.E7.D6A1FiniteCertificate
open RiemannResearch.Logic

/-- The two form scopes needed to separate Chernousov's quasi-split theorem
from the arbitrary-form E7 problem. -/
inductive E7FormKind
  | quasiSplit
  | nonQuasiSplit
  deriving DecidableEq

namespace E7FormKind

/-- Select the quasi-split E7 scope. -/
def IsQuasiSplit : E7FormKind → Prop
  | .quasiSplit => True
  | .nonQuasiSplit => False

/-- Select the non-quasi-split E7 scope. -/
def IsNonQuasiSplit : E7FormKind → Prop
  | .quasiSplit => False
  | .nonQuasiSplit => True

/-- Every supplied E7 form is in exactly one scope. -/
theorem quasiSplit_or_nonQuasiSplit (kind : E7FormKind) :
    kind.IsQuasiSplit ∨ kind.IsNonQuasiSplit := by
  cases kind <;> simp [IsQuasiSplit, IsNonQuasiSplit]

end E7FormKind

/-- Abstract classifier distinguishing quasi-split and non-quasi-split E7
forms. Constructing it for concrete group schemes is a separate obligation.
-/
abbrev E7FormClassifier :=
  (R A : CommRingCat.{u}) → [HopfAlgebra R A] → E7FormKind

/-- Neutrality for a selected scope of supplied E7 forms. -/
abbrev E7FormNeutralityProvider
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (formKind : E7FormClassifier)
    (Select : E7FormKind → Prop) : Prop :=
  ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
    Base R →
    Group R A →
    family R A = .E7 →
    Select (formKind R A) →
    Subsingleton (FpqcH1.{u, u} R A)

/-! ## Cyclic-prime relative-kernel route -/

/-- A finite tower of cyclic-prime restriction steps.

Every successor stores the exact pointed-set conclusion needed from a cyclic
relative-kernel theorem. The terminal equality is normally supplied by
quasi-split E7 neutrality after the group has become split. Merely knowing
that the group splits at the top does not construct the intermediate
`kernel` fields. -/
inductive E7CyclicPrimeKernelTower :
    {X : Type x} → (neutral point : X) → Nat → Type (x + 1)
  | terminal {X : Type x} {neutral point : X}
      (h : point = neutral) :
      E7CyclicPrimeKernelTower neutral point 0
  | step {X : Type x} {neutral point : X} {n : Nat}
      (Y : Type x)
      (localNeutral : Y)
      (restrict : X → Y)
      (degree : Nat)
      (degreeSupported : degree = 2 ∨ degree = 3)
      (kernel : HasTrivialKernel neutral localNeutral restrict)
      (tail : E7CyclicPrimeKernelTower localNeutral (restrict point) n) :
      E7CyclicPrimeKernelTower neutral point (n + 1)

namespace E7CyclicPrimeKernelTower

/-- Iterating the recorded cyclic relative kernels descends terminal
neutrality all the way to the original class. -/
theorem eq_basepoint
    {X : Type x} {neutral point : X} {n : Nat}
    (T : E7CyclicPrimeKernelTower neutral point n) :
    point = neutral := by
  induction T with
  | terminal h => exact h
  | step Y localNeutral restrict degree degreeSupported kernel tail ih =>
      exact (kernel _).1 ih

end E7CyclicPrimeKernelTower

/-- Every selected E7 class has a finite 2/3-primary restriction tower
with a trivial relative kernel at every step and a neutral terminal class. -/
abbrev E7CyclicPrimeKernelTowerProvider
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (formKind : E7FormClassifier)
    (Select : E7FormKind → Prop) : Prop :=
  ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
    Base R →
    Group R A →
    family R A = .E7 →
    Select (formKind R A) →
    ∀ ξ : FpqcH1.{u, u} R A,
      ∃ n : Nat,
        Nonempty
          (E7CyclicPrimeKernelTower
            (FpqcH1.neutral R A) ξ n)

/-- Cyclic-prime towers with trivial kernels give neutrality for the selected
E7 form scope. -/
theorem e7FormNeutralityProvider_of_cyclicPrimeKernelTowers
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (formKind : E7FormClassifier)
    (Select : E7FormKind → Prop)
    (towers : E7CyclicPrimeKernelTowerProvider
      Base Group family formKind Select) :
    E7FormNeutralityProvider Base Group family formKind Select := by
  intro R A _ hBase hGroup hE7 hSelect
  constructor
  intro ξ η
  obtain ⟨nξ, ⟨Tξ⟩⟩ :=
    towers R A hBase hGroup hE7 hSelect ξ
  obtain ⟨nη, ⟨Tη⟩⟩ :=
    towers R A hBase hGroup hE7 hSelect η
  exact Tξ.eq_basepoint.trans Tη.eq_basepoint.symm

/-! ## D6+A1 index route -/

/-- The three labelled trialitarian indices attached by the D6+A1 reduction,
together with the sourced finite classification table.

The definition records the table but does not assert that an arbitrary E7
torsor has been geometrically attached to these three components. -/
structure E7D6A1IndexData where
  i12 : Nat
  i13 : Nat
  i23 : Nat
  allowed : AllowedTrialitarianIndexTriple i12 i13 i23

namespace E7D6A1IndexData

/-- Either the distinguished component has index below four, or one of the
other labelled components is split. -/
theorem lowIndex_or_labelledSplit (D : E7D6A1IndexData) :
    D.i23 ≠ 4 ∨ D.i12 = 1 ∨ D.i13 = 1 := by
  by_cases h23 : D.i23 = 4
  · exact Or.inr
      (index_four_forces_labelled_split D.allowed h23)
  · exact Or.inl h23

end E7D6A1IndexData

/-- The three group-scheme/H1 bridges that turn the finite D6+A1 index split
into neutrality of the original E7 class.

These fields are deliberately separate from the finite index table. Effective
descent of the underlying D4 coordinate module does not construct them. -/
structure E7D6A1NeutralityBridges
    {X : Type x} (point neutral : X)
    (D : E7D6A1IndexData) : Prop where
  lowIndex : D.i23 ≠ 4 → point = neutral
  split12 : D.i12 = 1 → point = neutral
  split13 : D.i13 = 1 → point = neutral

namespace E7D6A1NeutralityBridges

/-- The finite index split and three geometric bridges neutralize the class. -/
theorem eq_basepoint
    {X : Type x} {point neutral : X}
    {D : E7D6A1IndexData}
    (B : E7D6A1NeutralityBridges point neutral D) :
    point = neutral := by
  rcases D.lowIndex_or_labelledSplit with hlow | h12 | h13
  · exact B.lowIndex hlow
  · exact B.split12 h12
  · exact B.split13 h13

end E7D6A1NeutralityBridges

/-- Every selected E7 class has D6+A1 index data and the three required
neutrality bridges. -/
abbrev E7D6A1ReductionProvider
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (formKind : E7FormClassifier)
    (Select : E7FormKind → Prop) : Prop :=
  ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
    Base R →
    Group R A →
    family R A = .E7 →
    Select (formKind R A) →
    ∀ ξ : FpqcH1.{u, u} R A,
      ∃ D : E7D6A1IndexData,
        E7D6A1NeutralityBridges
          ξ (FpqcH1.neutral R A) D

/-- D6+A1 reductions give neutrality for the selected E7 form scope. -/
theorem e7FormNeutralityProvider_of_d6a1Reductions
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (formKind : E7FormClassifier)
    (Select : E7FormKind → Prop)
    (reductions : E7D6A1ReductionProvider
      Base Group family formKind Select) :
    E7FormNeutralityProvider Base Group family formKind Select := by
  intro R A _ hBase hGroup hE7 hSelect
  constructor
  intro ξ η
  obtain ⟨Dξ, Bξ⟩ :=
    reductions R A hBase hGroup hE7 hSelect ξ
  obtain ⟨Dη, Bη⟩ :=
    reductions R A hBase hGroup hE7 hSelect η
  exact Bξ.eq_basepoint.trans Bη.eq_basepoint.symm

/-! ## Exact E7 assembly and counterexample constraints -/

/-- Quasi-split and non-quasi-split providers assemble into the exact
family-E7 provider for the unchanged Serre-II target. -/
theorem exactFamilyE7_of_form_providers
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (formKind : E7FormClassifier)
    (quasiSplit : E7FormNeutralityProvider
      Base Group family formKind E7FormKind.IsQuasiSplit)
    (nonQuasiSplit : E7FormNeutralityProvider
      Base Group family formKind E7FormKind.IsNonQuasiSplit) :
    ExactFamilyNeutralityProvider Base Group family .E7 := by
  intro R A _ hBase hGroup hE7
  rcases E7FormKind.quasiSplit_or_nonQuasiSplit
      (formKind R A) with hq | hnq
  · exact quasiSplit R A hBase hGroup hE7 hq
  · exact nonQuasiSplit R A hBase hGroup hE7 hnq

/-- Exact E7 neutrality from the quasi-split scope and cyclic-prime
relative-kernel towers for the remaining forms. -/
theorem
    exactFamilyE7_of_quasiSplit_and_nonQuasiSplitCyclicPrimeKernelTowers
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (formKind : E7FormClassifier)
    (quasiSplit : E7FormNeutralityProvider
      Base Group family formKind E7FormKind.IsQuasiSplit)
    (nonQuasiSplitTowers : E7CyclicPrimeKernelTowerProvider
      Base Group family formKind E7FormKind.IsNonQuasiSplit) :
    ExactFamilyNeutralityProvider Base Group family .E7 :=
  exactFamilyE7_of_form_providers Base Group family formKind quasiSplit
    (e7FormNeutralityProvider_of_cyclicPrimeKernelTowers
      Base Group family formKind E7FormKind.IsNonQuasiSplit
      nonQuasiSplitTowers)

/-- Exact E7 neutrality from the quasi-split scope and the D6+A1 reduction
for the remaining forms. -/
theorem exactFamilyE7_of_quasiSplit_and_nonQuasiSplitD6A1Reductions
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (formKind : E7FormClassifier)
    (quasiSplit : E7FormNeutralityProvider
      Base Group family formKind E7FormKind.IsQuasiSplit)
    (nonQuasiSplitReductions : E7D6A1ReductionProvider
      Base Group family formKind E7FormKind.IsNonQuasiSplit) :
    ExactFamilyNeutralityProvider Base Group family .E7 :=
  exactFamilyE7_of_form_providers Base Group family formKind quasiSplit
    (e7FormNeutralityProvider_of_d6a1Reductions
      Base Group family formKind E7FormKind.IsNonQuasiSplit
      nonQuasiSplitReductions)

/-- Relative to a quasi-split E7 provider, a nonneutral E7 class must be
non-quasi-split, has no complete cyclic-prime kernel tower, and has no
complete D6+A1 reduction. -/
structure E7CounterexampleConstraints
    (formKind : E7FormClassifier)
    (R A : CommRingCat.{u}) [HopfAlgebra R A]
    (ξ : FpqcH1.{u, u} R A) : Prop where
  nonQuasiSplit :
    E7FormKind.IsNonQuasiSplit (formKind R A)
  noCyclicPrimeKernelTower :
    ¬ ∃ n : Nat,
        Nonempty
          (E7CyclicPrimeKernelTower
            (FpqcH1.neutral R A) ξ n)
  noD6A1Reduction :
    ¬ ∃ D : E7D6A1IndexData,
        E7D6A1NeutralityBridges
          ξ (FpqcH1.neutral R A) D

/-- Every nonneutral E7 class satisfies the displayed constraints. -/
theorem e7CounterexampleConstraints_of_ne
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (formKind : E7FormClassifier)
    (quasiSplit : E7FormNeutralityProvider
      Base Group family formKind E7FormKind.IsQuasiSplit)
    (R A : CommRingCat.{u}) [HopfAlgebra R A]
    (hBase : Base R)
    (hGroup : Group R A)
    (hE7 : family R A = .E7)
    (ξ : FpqcH1.{u, u} R A)
    (hξ : ξ ≠ FpqcH1.neutral R A) :
    E7CounterexampleConstraints formKind R A ξ := by
  constructor
  · rcases E7FormKind.quasiSplit_or_nonQuasiSplit
        (formKind R A) with hq | hnq
    · exact
        (hξ ((quasiSplit R A hBase hGroup hE7 hq).allEq
          ξ (FpqcH1.neutral R A))).elim
    · exact hnq
  · rintro ⟨n, ⟨T⟩⟩
    exact hξ T.eq_basepoint
  · rintro ⟨D, B⟩
    exact hξ B.eq_basepoint

end RiemannResearch.AlgebraicGeometry.SerreII
