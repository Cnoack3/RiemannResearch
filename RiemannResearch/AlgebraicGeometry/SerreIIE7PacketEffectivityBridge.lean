/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.SerreIITypeE7
import RiemannResearch.E7.E7BoundaryEffectivity

/-!
# E7 packet effectivity and Galois-H1 neutrality

This module isolates the geometric bridge required to turn the prescribed
trialitarian packet realization theorem into the existing D6+A1 reduction for
type E7.  It does not assume neutrality outright: one must attach two labelled
target packets to each torsor and prove that their effectivity neutralizes the
corresponding split branch.  Constructing those attachments remains a concrete
algebraic-group and Galois-cohomology obligation.
-/

universe u v x

namespace RiemannResearch.AlgebraicGeometry.SerreII

open RiemannResearch.E7.QuaternionTrialityPacket

/-- The exact packet-level geometric data needed to construct the three
neutrality bridges in a D6+A1 reduction. -/
structure E7D6A1PacketNeutralityBridges
    {B : Type v} [AddCommGroup B]
    (C : BoundaryRealization B)
    (IsQuaternionClass : B → Prop)
    {X : Type x} (point neutral : X)
    (D : E7D6A1IndexData) where
  packet12 : BrauerPacket B
  packet12_target :
    IsQuaternionTargetPacket IsQuaternionClass packet12
  packet13 : BrauerPacket B
  packet13_target :
    IsQuaternionTargetPacket IsQuaternionClass packet13
  lowIndex : D.i23 ≠ 4 → point = neutral
  split12 :
    D.i12 = 1 → C.IsEffective packet12 → point = neutral
  split13 :
    D.i13 = 1 → C.IsEffective packet13 → point = neutral

namespace E7D6A1PacketNeutralityBridges

/-- Universal effectivity for quaternion target packets supplies the two
branch effectivity hypotheses required by a D6+A1 neutrality bridge. -/
theorem toNeutralityBridges
    {B : Type v} [AddCommGroup B]
    {C : BoundaryRealization B}
    {IsQuaternionClass : B → Prop}
    {X : Type x} {point neutral : X}
    {D : E7D6A1IndexData}
    (P : E7D6A1PacketNeutralityBridges
      C IsQuaternionClass point neutral D)
    (realize : E7RealizationGoal C IsQuaternionClass) :
    E7D6A1NeutralityBridges point neutral D := by
  constructor
  · exact P.lowIndex
  · intro h12
    apply P.split12 h12
    exact (e7RealizationGoal_iff_targetPackets C IsQuaternionClass).1
      realize P.packet12 P.packet12_target
  · intro h13
    apply P.split13 h13
    exact (e7RealizationGoal_iff_targetPackets C IsQuaternionClass).1
      realize P.packet13 P.packet13_target

/-- Two already-effective attached packets suffice directly, without assuming
the universal `E7RealizationGoal`. -/
theorem toNeutralityBridges_of_effectivePackets
    {B : Type v} [AddCommGroup B]
    {C : BoundaryRealization B}
    {IsQuaternionClass : B → Prop}
    {X : Type x} {point neutral : X}
    {D : E7D6A1IndexData}
    (P : E7D6A1PacketNeutralityBridges
      C IsQuaternionClass point neutral D)
    (effective12 : C.IsEffective P.packet12)
    (effective13 : C.IsEffective P.packet13) :
    E7D6A1NeutralityBridges point neutral D := by
  constructor
  · exact P.lowIndex
  · intro h12
    exact P.split12 h12 effective12
  · intro h13
    exact P.split13 h13 effective13

end E7D6A1PacketNeutralityBridges

/-- A pointwise packet attachment for every selected E7 torsor. -/
abbrev E7D6A1PacketReductionProvider
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (formKind : E7FormClassifier)
    (Select : E7FormKind → Prop)
    {B : Type v} [AddCommGroup B]
    (C : BoundaryRealization B)
    (IsQuaternionClass : B → Prop) : Prop :=
  ∀ (R A : Type u) [Field R] [CommRing A] [HopfAlgebra R A],
    Base R →
    Group R A →
    family R A = .E7 →
    Select (formKind R A) →
    ∀ ξ : GaloisH1 R A,
      ∃ D : E7D6A1IndexData,
        Nonempty
          (E7D6A1PacketNeutralityBridges
            C IsQuaternionClass ξ (GaloisH1.neutral R A) D)

/-- A pointwise packet attachment in which both labelled packets have already
been realized. -/
abbrev E7D6A1EffectivePacketReductionProvider
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (formKind : E7FormClassifier)
    (Select : E7FormKind → Prop)
    {B : Type v} [AddCommGroup B]
    (C : BoundaryRealization B)
    (IsQuaternionClass : B → Prop) : Prop :=
  ∀ (R A : Type u) [Field R] [CommRing A] [HopfAlgebra R A],
    Base R →
    Group R A →
    family R A = .E7 →
    Select (formKind R A) →
    ∀ ξ : GaloisH1 R A,
      ∃ D : E7D6A1IndexData,
        ∃ P : E7D6A1PacketNeutralityBridges
          C IsQuaternionClass ξ (GaloisH1.neutral R A) D,
          C.IsEffective P.packet12 ∧ C.IsEffective P.packet13

/-- Packet attachments plus universal target-packet effectivity construct the
existing D6+A1 reduction provider. -/
theorem e7D6A1ReductionProvider_of_packetReductions
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (formKind : E7FormClassifier)
    (Select : E7FormKind → Prop)
    {B : Type v} [AddCommGroup B]
    (C : BoundaryRealization B)
    (IsQuaternionClass : B → Prop)
    (realize : E7RealizationGoal C IsQuaternionClass)
    (reductions : E7D6A1PacketReductionProvider
      Base Group family formKind Select C IsQuaternionClass) :
    E7D6A1ReductionProvider Base Group family formKind Select := by
  intro R A _ _ _ hBase hGroup hE7 hSelect ξ
  obtain ⟨D, ⟨P⟩⟩ :=
    reductions R A hBase hGroup hE7 hSelect ξ
  exact ⟨D, P.toNeutralityBridges realize⟩

/-- Already-effective attached packets construct the existing D6+A1 reduction
provider without a universal packet-realization hypothesis. -/
theorem e7D6A1ReductionProvider_of_effectivePacketReductions
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (formKind : E7FormClassifier)
    (Select : E7FormKind → Prop)
    {B : Type v} [AddCommGroup B]
    (C : BoundaryRealization B)
    (IsQuaternionClass : B → Prop)
    (reductions : E7D6A1EffectivePacketReductionProvider
      Base Group family formKind Select C IsQuaternionClass) :
    E7D6A1ReductionProvider Base Group family formKind Select := by
  intro R A _ _ _ hBase hGroup hE7 hSelect ξ
  obtain ⟨D, P, effective12, effective13⟩ :=
    reductions R A hBase hGroup hE7 hSelect ξ
  exact ⟨D,
    P.toNeutralityBridges_of_effectivePackets effective12 effective13⟩

/-- Exact family-E7 neutrality from quasi-split neutrality, the universal
packet-realization theorem, and packet attachments for non-quasi-split forms.
-/
theorem exactFamilyE7_of_quasiSplit_and_packetReductions
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (formKind : E7FormClassifier)
    (quasiSplit : E7FormNeutralityProvider
      Base Group family formKind E7FormKind.IsQuasiSplit)
    {B : Type v} [AddCommGroup B]
    (C : BoundaryRealization B)
    (IsQuaternionClass : B → Prop)
    (realize : E7RealizationGoal C IsQuaternionClass)
    (nonQuasiSplitPacketReductions : E7D6A1PacketReductionProvider
      Base Group family formKind E7FormKind.IsNonQuasiSplit
      C IsQuaternionClass) :
    ExactFamilyNeutralityProvider Base Group family .E7 :=
  exactFamilyE7_of_quasiSplit_and_nonQuasiSplitD6A1Reductions
    Base Group family formKind quasiSplit
    (e7D6A1ReductionProvider_of_packetReductions
      Base Group family formKind E7FormKind.IsNonQuasiSplit
      C IsQuaternionClass realize nonQuasiSplitPacketReductions)

/-- Exact family-E7 neutrality from quasi-split neutrality and per-torsor
attachments of two packets that are already effective. -/
theorem exactFamilyE7_of_quasiSplit_and_effectivePacketReductions
    (Base : BaseCondition)
    (Group : GroupCondition)
    (family : DynkinFamilyClassifier)
    (formKind : E7FormClassifier)
    (quasiSplit : E7FormNeutralityProvider
      Base Group family formKind E7FormKind.IsQuasiSplit)
    {B : Type v} [AddCommGroup B]
    (C : BoundaryRealization B)
    (IsQuaternionClass : B → Prop)
    (nonQuasiSplitEffectivePacketReductions :
      E7D6A1EffectivePacketReductionProvider
        Base Group family formKind E7FormKind.IsNonQuasiSplit
        C IsQuaternionClass) :
    ExactFamilyNeutralityProvider Base Group family .E7 :=
  exactFamilyE7_of_quasiSplit_and_nonQuasiSplitD6A1Reductions
    Base Group family formKind quasiSplit
    (e7D6A1ReductionProvider_of_effectivePacketReductions
      Base Group family formKind E7FormKind.IsNonQuasiSplit
      C IsQuaternionClass nonQuasiSplitEffectivePacketReductions)

end RiemannResearch.AlgebraicGeometry.SerreII
