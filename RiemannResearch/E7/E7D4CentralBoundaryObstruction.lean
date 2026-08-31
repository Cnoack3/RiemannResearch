/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.E7IndexEightBoundary

/-!
# The nonabelian central-boundary obstruction in the hard type-E7 stratum

The three quaternion classes in the remaining E7 problem determine a central
Tits datum for `Spin₈`.  This file makes the corresponding effectivity problem
literal: an index-eight datum is effective exactly when it lies in the image
of the map from actual degree-eight boundary realizations to central Tits
data.

For a quaternion triple `(q₁,q₂,q₃)`, the two independent coordinates are

* `q₂ + q₃` on the vector character;
* `q₁ + q₂` on the positive half-spin character.

The negative half-spin value is then forced to be `q₁ + q₃`.  Equality of
these central data is equivalent to diagonal translation of the quaternion
triple, so no information is lost by passing from the three inputs to the
central datum.

The final section packages the exactness statement expected from the
nonabelian cohomology sequence

`H¹(PGO₈⁺) → H²(Z(Spin₈)) → H²(Spin₈)`.

Its `exact_boundary` field is an interface to be instantiated by genuine
Galois or fpqc cohomology.  No obstruction-neutrality theorem, Douai-type
hypothesis, quadratic-pair realization, or E7 effectivity theorem is assumed
in this file.  The resulting equivalences identify the precise next theorem:
neutrality of the actual nonabelian obstruction on the index-eight target
locus.
-/

namespace RiemannResearch.E7.QuaternionTrialityPacket

universe u v w

variable {A : Type u} [AddCommGroup A] [Module (ZMod 2) A]

/-! ## The central datum of a quaternion triple -/

/-- The central Tits datum attached directly to a quaternion triple. -/
def targetCentralTitsMap (q₁ q₂ q₃ : A) :
    D4CenterCharacter →ₗ[ZMod 2] A :=
  centralTitsMap (q₂ + q₃) (q₁ + q₂)

@[simp] theorem targetCentralTitsMap_vectorCharacter
    (q₁ q₂ q₃ : A) :
    targetCentralTitsMap q₁ q₂ q₃ vectorCharacter = q₂ + q₃ := by
  simp [targetCentralTitsMap]

@[simp] theorem targetCentralTitsMap_spinPlusCharacter
    (q₁ q₂ q₃ : A) :
    targetCentralTitsMap q₁ q₂ q₃ spinPlusCharacter = q₁ + q₂ := by
  simp [targetCentralTitsMap]

@[simp] theorem targetCentralTitsMap_spinMinusCharacter
    (q₁ q₂ q₃ : A) :
    targetCentralTitsMap q₁ q₂ q₃ spinMinusCharacter = q₁ + q₃ := by
  simp only [targetCentralTitsMap, centralTitsMap_spinMinusCharacter]
  change (q₂ + q₃) + (q₁ + q₂) = q₁ + q₃
  calc
    (q₂ + q₃) + (q₁ + q₂) =
        (q₂ + q₂) + (q₁ + q₃) := by abel
    _ = q₁ + q₃ := by rw [module_isExponentTwo q₂, zero_add]

/-- Evaluating the target central datum on the three nonzero characters gives
exactly the labelled E7 Brauer packet. -/
@[simp] theorem packetOf_targetCentralTitsMap
    (q₁ q₂ q₃ : A) :
    packetOfCentralTitsMap (targetCentralTitsMap q₁ q₂ q₃) =
      BrauerPacket.ofTriple q₁ q₂ q₃ := by
  apply BrauerPacket.ext
  · exact targetCentralTitsMap_vectorCharacter q₁ q₂ q₃
  · exact targetCentralTitsMap_spinPlusCharacter q₁ q₂ q₃
  · exact targetCentralTitsMap_spinMinusCharacter q₁ q₂ q₃

/-- Two quaternion triples determine the same central Tits datum exactly when
they differ by common diagonal translation. -/
theorem targetCentralTitsMap_eq_iff_diagonal
    (q₁ q₂ q₃ q₁' q₂' q₃' : A) :
    targetCentralTitsMap q₁ q₂ q₃ =
        targetCentralTitsMap q₁' q₂' q₃' ↔
      ∃ r : A,
        q₁' = q₁ + r ∧ q₂' = q₂ + r ∧ q₃' = q₃ + r := by
  constructor
  · intro h
    apply (BrauerPacket.ofTriple_eq_iff_diagonal
      module_isExponentTwo q₁ q₂ q₃ q₁' q₂' q₃').1
    simpa only [packetOf_targetCentralTitsMap] using
      congrArg packetOfCentralTitsMap h
  · intro h
    apply packetOfCentralTitsMap_injective
    simpa only [packetOf_targetCentralTitsMap] using
      (BrauerPacket.ofTriple_eq_iff_diagonal
        module_isExponentTwo q₁ q₂ q₃ q₁' q₂' q₃').2 h

/-! ## The actual central-boundary map -/

namespace BoundaryRealization

variable (C : BoundaryRealization.{u, v} A)

/-- The unique central Tits datum carried by an actual boundary realization.
It is reconstructed from the vector and positive half-spin entries of the
realization's balanced packet. -/
def centralDatum (X : C.Object) :
    D4CenterCharacter →ₗ[ZMod 2] A :=
  centralTitsMap (C.packet X).underlying (C.packet X).cliffordPlus

/-- Re-evaluating the central datum of an actual realization recovers its
labelled packet. -/
@[simp] theorem packetOfCentralDatum (X : C.Object) :
    packetOfCentralTitsMap (C.centralDatum X) = C.packet X := by
  exact packetOfCentralTitsMap_centralTitsMap_of_isBalanced
    (C.packet X) (C.packet_isBalanced X)

/-- Equality of central data is equivalent to equality of their labelled
packets. -/
theorem centralDatum_eq_iff_packet_eq
    (X : C.Object) (t : D4CenterCharacter →ₗ[ZMod 2] A) :
    C.centralDatum X = t ↔
      C.packet X = packetOfCentralTitsMap t := by
  constructor
  · intro h
    rw [← C.packetOfCentralDatum X, h]
  · intro h
    apply packetOfCentralTitsMap_injective
    rw [C.packetOfCentralDatum X, h]

/-- A central Tits datum is effective exactly when it lies in the image of the
actual central-boundary map. -/
theorem isEffective_packetOfCentralTitsMap_iff_mem_range
    (t : D4CenterCharacter →ₗ[ZMod 2] A) :
    C.IsEffective (packetOfCentralTitsMap t) ↔
      t ∈ Set.range C.centralDatum := by
  constructor
  · rintro ⟨X, hX⟩
    exact ⟨X, (C.centralDatum_eq_iff_packet_eq X t).2 hX⟩
  · rintro ⟨X, hX⟩
    exact ⟨X, (C.centralDatum_eq_iff_packet_eq X t).1 hX⟩

end BoundaryRealization

/-- Full central-boundary surjectivity is literal surjectivity of the map from
actual realizations to central Tits data. -/
theorem centralBoundarySurjective_iff_centralDatum_surjective
    (C : BoundaryRealization.{u, v} A) :
    CentralBoundarySurjective C ↔
      Function.Surjective C.centralDatum := by
  constructor
  · intro h t
    exact (C.isEffective_packetOfCentralTitsMap_iff_mem_range t).1 (h t)
  · intro h t
    exact (C.isEffective_packetOfCentralTitsMap_iff_mem_range t).2 (h t)

/-! ## The index-eight image problem -/

/-- The exact boundary-image problem on the hard index-eight central locus. -/
def IndexEightCentralBoundaryImageGoal
    (I : BrauerIndexModel A)
    (C : BoundaryRealization.{u, v} A)
    (IsQuaternionClass : A → Prop) : Prop :=
  ∀ t : D4CenterCharacter →ₗ[ZMod 2] A,
    IsIndexEightQuaternionTargetCentralDatum I IsQuaternionClass t →
      t ∈ Set.range C.centralDatum

/-- Effectivity and membership in the actual boundary image are equivalent on
the index-eight target locus. -/
theorem indexEightCentralTargetEffectivityGoal_iff_boundaryImage
    (I : BrauerIndexModel A)
    (C : BoundaryRealization.{u, v} A)
    (IsQuaternionClass : A → Prop) :
    IndexEightCentralTargetEffectivityGoal I C IsQuaternionClass ↔
      IndexEightCentralBoundaryImageGoal I C IsQuaternionClass := by
  constructor
  · intro h t ht
    exact (C.isEffective_packetOfCentralTitsMap_iff_mem_range t).1 (h t ht)
  · intro h t ht
    exact (C.isEffective_packetOfCentralTitsMap_iff_mem_range t).2 (h t ht)

/-- The same image problem written directly on quaternion triples, using the
explicit two-coordinate central datum above. -/
def E7IndexEightCentralLiftGoal
    (I : BrauerIndexModel A)
    (C : BoundaryRealization.{u, v} A)
    (IsQuaternionClass : A → Prop) : Prop :=
  ∀ q₁ q₂ q₃ : A,
    IsQuaternionClass q₁ →
      IsQuaternionClass q₂ →
      IsQuaternionClass q₃ →
      I.index (q₁ + q₂ + q₃) = 8 →
      targetCentralTitsMap q₁ q₂ q₃ ∈ Set.range C.centralDatum

/-- The hard E7 realization theorem is exactly lifting every explicit target
central datum through the boundary map from actual realizations. -/
theorem e7IndexEightRealizationGoal_iff_centralLift
    (I : BrauerIndexModel A)
    (C : BoundaryRealization.{u, v} A)
    (IsQuaternionClass : A → Prop) :
    E7IndexEightRealizationGoal I C IsQuaternionClass ↔
      E7IndexEightCentralLiftGoal I C IsQuaternionClass := by
  constructor
  · intro h q₁ q₂ q₃ hq₁ hq₂ hq₃ hIndex
    apply (C.isEffective_packetOfCentralTitsMap_iff_mem_range
      (targetCentralTitsMap q₁ q₂ q₃)).1
    simpa only [packetOf_targetCentralTitsMap] using
      h q₁ q₂ q₃ hq₁ hq₂ hq₃ hIndex
  · intro h q₁ q₂ q₃ hq₁ hq₂ hq₃ hIndex
    have hLift := h q₁ q₂ q₃ hq₁ hq₂ hq₃ hIndex
    have hEffective :=
      (C.isEffective_packetOfCentralTitsMap_iff_mem_range
        (targetCentralTitsMap q₁ q₂ q₃)).2 hLift
    simpa only [packetOf_targetCentralTitsMap] using hEffective

/-! ## The following nonabelian obstruction -/

/-- A formal exactness package for the nonabelian obstruction following the
central connecting map.  Its instantiation must come from genuine Galois or
fpqc cohomology; in particular, `exact_boundary` may not be filled by simply
restating `BoundaryRealization.IsEffective` and then counted as a realization
theorem. -/
structure D4CentralObstructionTheory
    (C : BoundaryRealization.{u, v} A) where
  Obstruction : Type w
  IsNeutral : Obstruction → Prop
  obstruction : (D4CenterCharacter →ₗ[ZMod 2] A) → Obstruction
  exact_boundary : ∀ t,
    t ∈ Set.range C.centralDatum ↔ IsNeutral (obstruction t)

/-- Neutrality of the nonabelian obstruction on precisely the hard central
target locus. -/
def IndexEightCentralObstructionNeutralityGoal
    (I : BrauerIndexModel A)
    (C : BoundaryRealization.{u, v} A)
    (O : D4CentralObstructionTheory.{u, v, w} C)
    (IsQuaternionClass : A → Prop) : Prop :=
  ∀ t : D4CenterCharacter →ₗ[ZMod 2] A,
    IsIndexEightQuaternionTargetCentralDatum I IsQuaternionClass t →
      O.IsNeutral (O.obstruction t)

/-- The same obstruction-neutrality goal written on the explicit quaternion
triple central datum. -/
def E7IndexEightTargetObstructionNeutralityGoal
    (I : BrauerIndexModel A)
    (C : BoundaryRealization.{u, v} A)
    (O : D4CentralObstructionTheory.{u, v, w} C)
    (IsQuaternionClass : A → Prop) : Prop :=
  ∀ q₁ q₂ q₃ : A,
    IsQuaternionClass q₁ →
      IsQuaternionClass q₂ →
      IsQuaternionClass q₃ →
      I.index (q₁ + q₂ + q₃) = 8 →
      O.IsNeutral (O.obstruction (targetCentralTitsMap q₁ q₂ q₃))

/-- The missing central effectivity theorem is exactly neutrality of the
following nonabelian obstruction on the index-eight target locus. -/
theorem indexEightCentralTargetEffectivityGoal_iff_obstructionNeutrality
    (I : BrauerIndexModel A)
    (C : BoundaryRealization.{u, v} A)
    (O : D4CentralObstructionTheory.{u, v, w} C)
    (IsQuaternionClass : A → Prop) :
    IndexEightCentralTargetEffectivityGoal I C IsQuaternionClass ↔
      IndexEightCentralObstructionNeutralityGoal I C O IsQuaternionClass := by
  constructor
  · intro h t ht
    exact (O.exact_boundary t).1
      ((C.isEffective_packetOfCentralTitsMap_iff_mem_range t).1 (h t ht))
  · intro h t ht
    exact (C.isEffective_packetOfCentralTitsMap_iff_mem_range t).2
      ((O.exact_boundary t).2 (h t ht))

/-- Quaternion-triple realization on the hard stratum is equivalent to
neutrality of its explicit target obstruction. -/
theorem e7IndexEightRealizationGoal_iff_targetObstructionNeutrality
    (I : BrauerIndexModel A)
    (C : BoundaryRealization.{u, v} A)
    (O : D4CentralObstructionTheory.{u, v, w} C)
    (IsQuaternionClass : A → Prop) :
    E7IndexEightRealizationGoal I C IsQuaternionClass ↔
      E7IndexEightTargetObstructionNeutralityGoal
        I C O IsQuaternionClass := by
  rw [e7IndexEightRealizationGoal_iff_centralLift]
  constructor
  · intro h q₁ q₂ q₃ hq₁ hq₂ hq₃ hIndex
    exact (O.exact_boundary (targetCentralTitsMap q₁ q₂ q₃)).1
      (h q₁ q₂ q₃ hq₁ hq₂ hq₃ hIndex)
  · intro h q₁ q₂ q₃ hq₁ hq₂ hq₃ hIndex
    exact (O.exact_boundary (targetCentralTitsMap q₁ q₂ q₃)).2
      (h q₁ q₂ q₃ hq₁ hq₂ hq₃ hIndex)

/-- The full abstract E7 target splits into the already treated complement
and neutrality of the explicit nonabelian obstruction on the index-eight
stratum. -/
theorem e7RealizationGoal_iff_away_and_targetObstructionNeutrality
    (I : BrauerIndexModel A)
    (C : BoundaryRealization.{u, v} A)
    (O : D4CentralObstructionTheory.{u, v, w} C)
    (IsQuaternionClass : A → Prop) :
    E7RealizationGoal C IsQuaternionClass ↔
      E7AwayFromIndexEightRealizationGoal I C IsQuaternionClass ∧
        E7IndexEightTargetObstructionNeutralityGoal
          I C O IsQuaternionClass := by
  rw [e7RealizationGoal_iff_indexEight_partition]
  rw [e7IndexEightRealizationGoal_iff_targetObstructionNeutrality]

/-- Neutrality of every obstruction class is a sufficient, generally
strictly stronger, input for the hard E7 stratum. -/
theorem e7IndexEightRealizationGoal_of_all_obstructions_neutral
    (I : BrauerIndexModel A)
    (C : BoundaryRealization.{u, v} A)
    (O : D4CentralObstructionTheory.{u, v, w} C)
    (IsQuaternionClass : A → Prop)
    (hNeutral : ∀ o : O.Obstruction, O.IsNeutral o) :
    E7IndexEightRealizationGoal I C IsQuaternionClass := by
  rw [e7IndexEightRealizationGoal_iff_targetObstructionNeutrality
    I C O IsQuaternionClass]
  intro q₁ q₂ q₃ _ _ _ _
  exact hNeutral (O.obstruction (targetCentralTitsMap q₁ q₂ q₃))

end RiemannResearch.E7.QuaternionTrialityPacket
