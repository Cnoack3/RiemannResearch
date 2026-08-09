/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIITypeB
import RiemannResearch.AlgebraicGeometry.ZeroCycleSplitting

/-!
# Type-D and trialitarian zero-cycle reductions for Serre II

This module refines the exact type-D provider into nontrialitarian forms and
the arbitrary trialitarian forms ³D₄ and ⁶D₄. For the trialitarian branch it
records the following precise implication:

1. every torsor has a finite degree-one splitting cycle;
2. hence its finite neutralizing-extension degrees have gcd one;
3. if coprime restriction detects the neutral fpqc H¹ class, the torsor is
   neutral over the base.

Izquierdo--Lucchini Arteche, "Transfer principles for Galois cohomology and
Serre's conjecture II", Proposition 4.15 and Corollary 4.14,
https://arxiv.org/abs/2308.00903, support the degree-one zero-cycle input for
arbitrary trialitarian D₄ under their stated field hypotheses. They do not
supply the separate index-one-to-rational-point implication represented here
by TrialitarianIndexOneDescentProvider.

The declarations below prove that, once the degree-one-cycle input is supplied
for every class, TrialitarianIndexOneDescentProvider is equivalent to full
fpqc-H¹ neutrality for arbitrary ³D₄ and ⁶D₄ forms. Thus the descent provider
does not by itself reduce the remaining trialitarian Serre-II problem.

These remain conditional interfaces. In particular, the project does not yet
construct scalar extension on FpqcH1, instantiate the
sourced degree-one-cycle provider, or prove coprime restriction descent.
-/

universe u

namespace RiemannResearch.AlgebraicGeometry.SerreII

/-- Inner, ordinary outer, and the two trialitarian kinds of type-D forms. -/
inductive TypeDFormKind
  | inner
  | outer
  | trialitarian3
  | trialitarian6
  deriving DecidableEq

namespace TypeDFormKind

/-- The inner and ordinary outer type-D_n forms, excluding triality. -/
def IsNontrialitarian : TypeDFormKind → Prop
  | .inner | .outer => True
  | .trialitarian3 | .trialitarian6 => False

/-- Exactly the arbitrary ³D₄ and ⁶D₄ form kinds. -/
def IsTrialitarian : TypeDFormKind → Prop
  | .inner | .outer => False
  | .trialitarian3 | .trialitarian6 => True

theorem nontrialitarian_or_trialitarian (kind : TypeDFormKind) :
    kind.IsNontrialitarian ∨ kind.IsTrialitarian := by
  cases kind <;> simp [IsNontrialitarian, IsTrialitarian]

end TypeDFormKind

/-- The rank and triality kind of a type-D_n form.

Every type-D rank is at least four, and the two trialitarian kinds occur
only at rank four. -/
structure TypeDForm where
  rank : Nat
  rank_ge_four : 4 ≤ rank
  kind : TypeDFormKind
  trialitarian_rank : kind.IsTrialitarian → rank = 4

namespace TypeDForm

def IsNontrialitarian (form : TypeDForm) : Prop :=
  form.kind.IsNontrialitarian

def IsTrialitarian (form : TypeDForm) : Prop :=
  form.kind.IsTrialitarian

theorem nontrialitarian_or_trialitarian (form : TypeDForm) :
    form.IsNontrialitarian ∨ form.IsTrialitarian :=
  form.kind.nontrialitarian_or_trialitarian

end TypeDForm

/-- An abstract type-D rank-and-triality classifier. -/
abbrev TypeDFormClassifier :=
  (R A : CommRingCat.{u}) → [HopfAlgebra R A] → TypeDForm

/-- A neutrality provider for selected type-D forms. -/
abbrev TypeDFormNeutralityProvider
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeDForm : TypeDFormClassifier)
    (Select : TypeDForm → Prop) : Prop :=
  ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
    IsPerfectFieldCdAtMostTwo R →
    IsSemisimpleSimplyConnected R A →
    family R A = .D →
    Select (typeDForm R A) →
    Subsingleton (FpqcH1.{u, u} R A)

/-- Abstract scalar-extension data for one global pointed set.

The field restrict_neutral records that scalar extension preserves the
distinguished class. Constructing this data from actual field extensions and
FpqcH1 is a separate obligation. -/
structure TrialitarianRestrictionData
    (X : Type u) (x₀ : X) where
  Extension : Type u
  LocalClass : Extension → Type u
  neutral : ∀ L, LocalClass L
  restrict : ∀ L, X → LocalClass L
  restrict_neutral : ∀ L, restrict L x₀ = neutral L
  isFinite : Extension → Prop
  degree : Extension → ℕ

/-- A choice of restriction data for every candidate type-D group. Its
meaning is guarded by the explicit trialitarian selector in each provider. -/
abbrev TrialitarianRestrictionDataClassifier :=
  (R A : CommRingCat.{u}) → [HopfAlgebra R A] →
    TrialitarianRestrictionData
      (FpqcH1.{u, u} R A) (FpqcH1.neutral R A)

/-- The sourced geometric input: every torsor under every selected arbitrary
trialitarian form has a finite splitting zero-cycle of total degree one. -/
abbrev TrialitarianDegreeOneCycleProvider
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeDForm : TypeDFormClassifier)
    (restrictionData : TrialitarianRestrictionDataClassifier) : Prop :=
  ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
    IsPerfectFieldCdAtMostTwo R →
    IsSemisimpleSimplyConnected R A →
    family R A = .D →
    (typeDForm R A).IsTrialitarian →
    ∀ ξ, Nonempty (DegreeOneSplittingCycle
      (restrictionData R A).isFinite
      (restrictionData R A).degree
      (restrictionData R A).LocalClass
      (restrictionData R A).neutral
      (restrictionData R A).restrict ξ)

/-- Every selected arbitrary trialitarian torsor has point-field index one,
expressed as gcd one for its finite neutralizing extensions. -/
abbrev TrialitarianCoprimeSplittingProvider
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeDForm : TypeDFormClassifier)
    (restrictionData : TrialitarianRestrictionDataClassifier) : Prop :=
  ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
    IsPerfectFieldCdAtMostTwo R →
    IsSemisimpleSimplyConnected R A →
    family R A = .D →
    (typeDForm R A).IsTrialitarian →
    ∀ ξ, HasCoprimeNeutralizingExtensions
      (restrictionData R A).isFinite
      (restrictionData R A).degree
      (restrictionData R A).LocalClass
      (restrictionData R A).neutral
      (restrictionData R A).restrict ξ

/-- The remaining open trialitarian gate: point-field index one detects the
global neutral fpqc H¹ class for every selected arbitrary form. -/
abbrev TrialitarianIndexOneDescentProvider
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeDForm : TypeDFormClassifier)
    (restrictionData : TrialitarianRestrictionDataClassifier) : Prop :=
  ∀ (R A : CommRingCat.{u}) [HopfAlgebra R A],
    IsPerfectFieldCdAtMostTwo R →
    IsSemisimpleSimplyConnected R A →
    family R A = .D →
    (typeDForm R A).IsTrialitarian →
    CoprimeRestrictionDetectsBasepoint
      (FpqcH1.neutral R A)
      (restrictionData R A).isFinite
      (restrictionData R A).degree
      (restrictionData R A).LocalClass
      (restrictionData R A).neutral
      (restrictionData R A).restrict

/-- Degree-one splitting cycles give the coprime-splitting provider for every
arbitrary trialitarian form. No descent conclusion is used here. -/
theorem trialitarianCoprimeSplittingProvider_of_degreeOneCycles
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeDForm : TypeDFormClassifier)
    (restrictionData : TrialitarianRestrictionDataClassifier)
    (cycles : TrialitarianDegreeOneCycleProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm restrictionData) :
    TrialitarianCoprimeSplittingProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm restrictionData := by
  intro R A _ hField hGroup hD hTrialitarian ξ
  obtain ⟨cycle⟩ := cycles R A hField hGroup hD hTrialitarian ξ
  exact hasCoprimeNeutralizingExtensions_of_degreeOneSplittingCycle
    (restrictionData R A).isFinite
    (restrictionData R A).degree
    (restrictionData R A).LocalClass
    (restrictionData R A).neutral
    (restrictionData R A).restrict cycle

/-- Coprime splitting plus the explicit index-one descent provider gives
neutrality for all arbitrary trialitarian forms. -/
theorem trialitarianNeutralityProvider_of_coprimeSplitting
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeDForm : TypeDFormClassifier)
    (restrictionData : TrialitarianRestrictionDataClassifier)
    (splitting : TrialitarianCoprimeSplittingProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm restrictionData)
    (indexOneDescent : TrialitarianIndexOneDescentProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm restrictionData) :
    TypeDFormNeutralityProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm TypeDForm.IsTrialitarian := by
  intro R A _ hField hGroup hD hTrialitarian
  refine ⟨fun ξ η => ?_⟩
  rw [indexOneDescent R A hField hGroup hD hTrialitarian ξ
        (splitting R A hField hGroup hD hTrialitarian ξ),
      indexOneDescent R A hField hGroup hD hTrialitarian η
        (splitting R A hField hGroup hD hTrialitarian η)]

/-- Degree-one splitting cycles plus the separate index-one descent input give
neutrality for both ³D₄ and ⁶D₄ in arbitrary-form scope. -/
theorem trialitarianNeutralityProvider_of_degreeOneCycles
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeDForm : TypeDFormClassifier)
    (restrictionData : TrialitarianRestrictionDataClassifier)
    (cycles : TrialitarianDegreeOneCycleProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm restrictionData)
    (indexOneDescent : TrialitarianIndexOneDescentProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm restrictionData) :
    TypeDFormNeutralityProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm TypeDForm.IsTrialitarian :=
  trialitarianNeutralityProvider_of_coprimeSplitting
    IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
    family typeDForm restrictionData
    (trialitarianCoprimeSplittingProvider_of_degreeOneCycles
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm restrictionData cycles)
    indexOneDescent

/-- Trialitarian neutrality makes index-one descent automatic, independently
of the supplied restriction data. -/
theorem trialitarianIndexOneDescentProvider_of_neutralityProvider
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeDForm : TypeDFormClassifier)
    (restrictionData : TrialitarianRestrictionDataClassifier)
    (neutrality : TypeDFormNeutralityProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm TypeDForm.IsTrialitarian) :
    TrialitarianIndexOneDescentProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm restrictionData := by
  intro R A _ hField hGroup hD hTrialitarian ξ _
  exact @Subsingleton.elim _
    (neutrality R A hField hGroup hD hTrialitarian)
    ξ (FpqcH1.neutral R A)

/-- Once every trialitarian torsor has coprime neutralizing extensions,
index-one descent is equivalent to trialitarian neutrality. -/
theorem trialitarianIndexOneDescentProvider_iff_neutrality_of_coprimeSplitting
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeDForm : TypeDFormClassifier)
    (restrictionData : TrialitarianRestrictionDataClassifier)
    (splitting : TrialitarianCoprimeSplittingProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm restrictionData) :
    TrialitarianIndexOneDescentProvider
        IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
        family typeDForm restrictionData ↔
      TypeDFormNeutralityProvider
        IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
        family typeDForm TypeDForm.IsTrialitarian := by
  constructor
  · exact trialitarianNeutralityProvider_of_coprimeSplitting
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm restrictionData splitting
  · exact trialitarianIndexOneDescentProvider_of_neutralityProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm restrictionData

/-- Under the sourced degree-one-cycle input, the remaining index-one descent
provider is equivalent to Serre-II neutrality for arbitrary trialitarian
forms. -/
theorem trialitarianIndexOneDescentProvider_iff_neutrality_of_degreeOneCycles
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeDForm : TypeDFormClassifier)
    (restrictionData : TrialitarianRestrictionDataClassifier)
    (cycles : TrialitarianDegreeOneCycleProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm restrictionData) :
    TrialitarianIndexOneDescentProvider
        IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
        family typeDForm restrictionData ↔
      TypeDFormNeutralityProvider
        IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
        family typeDForm TypeDForm.IsTrialitarian :=
  trialitarianIndexOneDescentProvider_iff_neutrality_of_coprimeSplitting
    IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
    family typeDForm restrictionData
    (trialitarianCoprimeSplittingProvider_of_degreeOneCycles
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm restrictionData cycles)

/-- Nontrialitarian and trialitarian form providers assemble into the exact
Dynkin-family-D provider. -/
theorem exactFamilyD_of_typeD_form_providers
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeDForm : TypeDFormClassifier)
    (nontrialitarian : TypeDFormNeutralityProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm TypeDForm.IsNontrialitarian)
    (trialitarian : TypeDFormNeutralityProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm TypeDForm.IsTrialitarian) :
    ExactFamilyNeutralityProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected family .D := by
  intro R A _ hField hGroup hD
  rcases TypeDForm.nontrialitarian_or_trialitarian (typeDForm R A) with
    hNon | hTri
  · exact nontrialitarian R A hField hGroup hD hNon
  · exact trialitarian R A hField hGroup hD hTri

/-- The exact type-D provider obtained from nontrialitarian neutrality,
arbitrary-trialitarian degree-one cycles, and the still-explicit index-one
descent provider. -/
theorem exactFamilyD_of_nontrialitarian_and_degreeOneCycles
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeDForm : TypeDFormClassifier)
    (nontrialitarian : TypeDFormNeutralityProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm TypeDForm.IsNontrialitarian)
    (restrictionData : TrialitarianRestrictionDataClassifier)
    (cycles : TrialitarianDegreeOneCycleProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm restrictionData)
    (indexOneDescent : TrialitarianIndexOneDescentProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm restrictionData) :
    ExactFamilyNeutralityProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected family .D :=
  exactFamilyD_of_typeD_form_providers
    IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected family typeDForm
    nontrialitarian
    (trialitarianNeutralityProvider_of_degreeOneCycles
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected family
      typeDForm restrictionData cycles indexOneDescent)

/-- The connected non-E8 reduction with type D refined into
nontrialitarian forms and arbitrary trialitarian degree-one-cycle/descent
inputs. -/
theorem conjecture_nonE8_of_typeA_typeB_and_typeD_zeroCycles
    (IsPerfectFieldCdAtMostTwo : BaseCondition)
    (IsSemisimpleSimplyConnected : GroupCondition)
    (family : DynkinFamilyClassifier)
    (typeAForm : TypeAFormClassifier)
    (innerA : TypeAFormNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family typeAForm TypeAForm.IsInner)
    (outerA : TypeAFormNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family typeAForm TypeAForm.IsOuter)
    (typeBForm : TypeBFormClassifier)
    (rankB : ∀ n, 0 < n →
      TypeBRankNeutralityProvider IsPerfectFieldCdAtMostTwo
        IsSemisimpleSimplyConnected family typeBForm n)
    (c : ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family .C)
    (typeDForm : TypeDFormClassifier)
    (nontrialitarianD : TypeDFormNeutralityProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm TypeDForm.IsNontrialitarian)
    (restrictionData : TrialitarianRestrictionDataClassifier)
    (trialitarianCycles : TrialitarianDegreeOneCycleProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm restrictionData)
    (trialitarianIndexOneDescent : TrialitarianIndexOneDescentProvider
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected
      family typeDForm restrictionData)
    (e6 : ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family .E6)
    (e7 : ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family .E7)
    (f4 : ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family .F4)
    (g2 : ExactFamilyNeutralityProvider IsPerfectFieldCdAtMostTwo
      IsSemisimpleSimplyConnected family .G2) :
    Conjecture IsPerfectFieldCdAtMostTwo
      (NonE8GroupCondition IsSemisimpleSimplyConnected family) :=
  conjecture_nonE8_of_typeA_and_typeB_form_providers
    IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected family
    typeAForm innerA outerA typeBForm rankB c
    (exactFamilyD_of_nontrialitarian_and_degreeOneCycles
      IsPerfectFieldCdAtMostTwo IsSemisimpleSimplyConnected family
      typeDForm nontrialitarianD restrictionData trialitarianCycles
      trialitarianIndexOneDescent)
    e6 e7 f4 g2

end RiemannResearch.AlgebraicGeometry.SerreII
