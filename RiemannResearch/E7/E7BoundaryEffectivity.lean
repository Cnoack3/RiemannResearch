/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.D4CenterTitsPacket

/-!
# The exact effectivity boundary in the remaining type-E7 case

The three Brauer classes in the E7 bridge form a balanced labelled `D₄`
central Tits datum.  The linear classification of such data is not the missing
step: the missing step is effectivity by an actual degree-eight algebra with
quadratic pair.

This file separates four logically different statements.

1. `E7RealizationGoal` is the exact prescribed-packet realization problem for
   triples of quaternion classes.
2. `CentralTargetEffectivityGoal` is the same problem expressed on the
   character group of `Z(Spin₈)`; the two formulations are proved equivalent.
3. `BalancedBoundarySurjective` is a stronger, unrestricted boundary
   surjectivity statement.
4. A four-quaternion completion and a rank-four hermitian-isotropy theorem are
   two sufficient mechanisms for effectivity.  Neither mechanism is assumed.

Thus the module records the precise dependency boundary without introducing
an axiom asserting the missing E7 theorem.
-/

namespace RiemannResearch.E7.QuaternionTrialityPacket

universe u v w

variable {A : Type u} [AddCommGroup A]

/-- A class of actual degree-eight realizations together with its labelled
trialitarian Brauer packet.  The balance field records the trivial-discriminant
central-character relation. -/
structure BoundaryRealization (A : Type u) [AddCommGroup A] where
  Object : Type v
  packet : Object → BrauerPacket A
  packet_isBalanced : ∀ X, BrauerPacket.IsBalanced (packet X)

namespace BoundaryRealization

variable (C : BoundaryRealization A)

/-- A labelled Brauer packet is effective when it is represented by an actual
object in the chosen realization context. -/
def IsEffective (P : BrauerPacket A) : Prop :=
  ∃ X : C.Object, C.packet X = P

/-- Effectivity forces the central-character balance relation. -/
theorem isEffective_isBalanced {P : BrauerPacket A}
    (hP : C.IsEffective P) : BrauerPacket.IsBalanced P := by
  rcases hP with ⟨X, rfl⟩
  exact C.packet_isBalanced X

end BoundaryRealization

/-- A packet belongs to the E7 target locus when it comes from three classes
satisfying the designated quaternion-class predicate. -/
def IsQuaternionTargetPacket
    (IsQuaternionClass : A → Prop) (P : BrauerPacket A) : Prop :=
  ∃ q₁ q₂ q₃ : A,
    IsQuaternionClass q₁ ∧ IsQuaternionClass q₂ ∧ IsQuaternionClass q₃ ∧
      P = BrauerPacket.ofTriple q₁ q₂ q₃

/-- Exact packet form of Gille's remaining E7 realization problem. -/
def E7RealizationGoal
    (C : BoundaryRealization A) (IsQuaternionClass : A → Prop) : Prop :=
  ∀ q₁ q₂ q₃ : A,
    IsQuaternionClass q₁ → IsQuaternionClass q₂ → IsQuaternionClass q₃ →
      C.IsEffective (BrauerPacket.ofTriple q₁ q₂ q₃)

/-- The quantified triple formulation is exactly effectivity on the target
packet locus. -/
theorem e7RealizationGoal_iff_targetPackets
    (C : BoundaryRealization A) (IsQuaternionClass : A → Prop) :
    E7RealizationGoal C IsQuaternionClass ↔
      ∀ P : BrauerPacket A,
        IsQuaternionTargetPacket IsQuaternionClass P → C.IsEffective P := by
  constructor
  · intro h P hP
    rcases hP with ⟨q₁, q₂, q₃, hq₁, hq₂, hq₃, hEq⟩
    rcases h q₁ q₂ q₃ hq₁ hq₂ hq₃ with ⟨X, hX⟩
    exact ⟨X, hX.trans hEq.symm⟩
  · intro h q₁ q₂ q₃ hq₁ hq₂ hq₃
    exact h (BrauerPacket.ofTriple q₁ q₂ q₃)
      ⟨q₁, q₂, q₃, hq₁, hq₂, hq₃, rfl⟩

section CentralBoundary

variable [Module (ZMod 2) A]

/-- The target locus transported to a linear central Tits datum on
`Z(Spin₈)^*`. -/
def IsQuaternionTargetCentralDatum
    (IsQuaternionClass : A → Prop)
    (t : D4CenterCharacter →ₗ[ZMod 2] A) : Prop :=
  IsQuaternionTargetPacket IsQuaternionClass (packetOfCentralTitsMap t)

/-- Exact central-boundary formulation of the remaining E7 target. -/
def CentralTargetEffectivityGoal
    (C : BoundaryRealization A) (IsQuaternionClass : A → Prop) : Prop :=
  ∀ t : D4CenterCharacter →ₗ[ZMod 2] A,
    IsQuaternionTargetCentralDatum IsQuaternionClass t →
      C.IsEffective (packetOfCentralTitsMap t)

/-- The quaternion-triple realization problem and the central-boundary target
problem are equivalent.  This uses only the verified classification of
balanced `D₄` central Tits packets. -/
theorem e7RealizationGoal_iff_centralTargetEffectivity
    (C : BoundaryRealization A) (IsQuaternionClass : A → Prop) :
    E7RealizationGoal C IsQuaternionClass ↔
      CentralTargetEffectivityGoal C IsQuaternionClass := by
  constructor
  · intro h t ht
    rcases ht with ⟨q₁, q₂, q₃, hq₁, hq₂, hq₃, hEq⟩
    rcases h q₁ q₂ q₃ hq₁ hq₂ hq₃ with ⟨X, hX⟩
    exact ⟨X, hX.trans hEq.symm⟩
  · intro h q₁ q₂ q₃ hq₁ hq₂ hq₃
    let P : BrauerPacket A := BrauerPacket.ofTriple q₁ q₂ q₃
    let t : D4CenterCharacter →ₗ[ZMod 2] A :=
      centralTitsMap P.underlying P.cliffordPlus
    have hP : BrauerPacket.IsBalanced P := by
      exact BrauerPacket.isBalanced_ofTriple module_isExponentTwo q₁ q₂ q₃
    have ht : packetOfCentralTitsMap t = P := by
      exact packetOfCentralTitsMap_centralTitsMap_of_isBalanced P hP
    have hTarget : IsQuaternionTargetCentralDatum IsQuaternionClass t := by
      exact ⟨q₁, q₂, q₃, hq₁, hq₂, hq₃, ht⟩
    rcases h t hTarget with ⟨X, hX⟩
    exact ⟨X, hX.trans ht⟩

/-- Surjectivity of the full balanced boundary, a statement stronger than the
E7 target because it drops the quaternion-triple restriction. -/
def BalancedBoundarySurjective (C : BoundaryRealization A) : Prop :=
  ∀ P : BrauerPacket A,
    BrauerPacket.IsBalanced P → C.IsEffective P

/-- The same unrestricted surjectivity statement on central Tits data. -/
def CentralBoundarySurjective (C : BoundaryRealization A) : Prop :=
  ∀ t : D4CenterCharacter →ₗ[ZMod 2] A,
    C.IsEffective (packetOfCentralTitsMap t)

/-- Full balanced-packet surjectivity is equivalent to full central-boundary
surjectivity. -/
theorem balancedBoundarySurjective_iff_centralBoundarySurjective
    (C : BoundaryRealization A) :
    BalancedBoundarySurjective C ↔ CentralBoundarySurjective C := by
  constructor
  · intro h t
    exact h (packetOfCentralTitsMap t) (packetOfCentralTitsMap_isBalanced t)
  · intro h P hP
    let t : D4CenterCharacter →ₗ[ZMod 2] A :=
      centralTitsMap P.underlying P.cliffordPlus
    have ht : packetOfCentralTitsMap t = P :=
      packetOfCentralTitsMap_centralTitsMap_of_isBalanced P hP
    rcases h t with ⟨X, hX⟩
    exact ⟨X, hX.trans ht⟩

/-- The unrestricted boundary theorem implies the E7 target theorem. -/
theorem e7RealizationGoal_of_balancedBoundarySurjective
    (C : BoundaryRealization A) (IsQuaternionClass : A → Prop)
    (h : BalancedBoundarySurjective C) :
    E7RealizationGoal C IsQuaternionClass := by
  intro q₁ q₂ q₃ _ _ _
  exact h (BrauerPacket.ofTriple q₁ q₂ q₃)
    (BrauerPacket.isBalanced_ofTriple module_isExponentTwo q₁ q₂ q₃)

end CentralBoundary

/-- A constructor realizing the published four-quaternion orthogonal-sum
mechanism.  Supplying this structure requires the actual algebra-with-
quadratic-pair construction and its Clifford calculation. -/
structure FourQuaternionConstructor
    (C : BoundaryRealization A) (IsQuaternionClass : A → Prop) where
  realize : ∀ P : FourClassPacket A,
    IsQuaternionClass P.p₁ → IsQuaternionClass P.p₂ →
    IsQuaternionClass P.p₃ → IsQuaternionClass P.p₄ →
    P.total = 0 → C.Object
  packet_realize : ∀ (P : FourClassPacket A)
      (hp₁ : IsQuaternionClass P.p₁) (hp₂ : IsQuaternionClass P.p₂)
      (hp₃ : IsQuaternionClass P.p₃) (hp₄ : IsQuaternionClass P.p₄)
      (hTotal : P.total = 0),
    C.packet (realize P hp₁ hp₂ hp₃ hp₄ hTotal) = P.brauerPacket

/-- A four-quaternion presentation gives an effective target packet once the
orthogonal-sum constructor has been supplied. -/
theorem BoundaryRealization.isEffective_of_fourQuaternionPresentation
    (C : BoundaryRealization A) (IsQuaternionClass : A → Prop)
    (F : FourQuaternionConstructor C IsQuaternionClass)
    (q₁ q₂ q₃ : A)
    (h : HasFourQuaternionPresentation IsQuaternionClass q₁ q₂ q₃) :
    C.IsEffective (BrauerPacket.ofTriple q₁ q₂ q₃) := by
  rcases h with ⟨P, hQ, hTotal, hPacket⟩
  refine ⟨F.realize P hQ.1 hQ.2.1 hQ.2.2.1 hQ.2.2.2 hTotal, ?_⟩
  exact (F.packet_realize P hQ.1 hQ.2.1 hQ.2.2.1 hQ.2.2.2 hTotal).trans
    hPacket

/-- Uniform quaternion completion is a sufficient, but deliberately not
asserted, route to the E7 realization goal. -/
theorem e7RealizationGoal_of_fourQuaternionCompletions
    (h₂ : IsExponentTwo A)
    (C : BoundaryRealization A) (IsQuaternionClass : A → Prop)
    (F : FourQuaternionConstructor C IsQuaternionClass)
    (hCompletion : ∀ q₁ q₂ q₃ : A,
      IsQuaternionClass q₁ → IsQuaternionClass q₂ →
      IsQuaternionClass q₃ →
      HasQuaternionCompletion IsQuaternionClass q₁ q₂ q₃) :
    E7RealizationGoal C IsQuaternionClass := by
  intro q₁ q₂ q₃ hq₁ hq₂ hq₃
  apply C.isEffective_of_fourQuaternionPresentation IsQuaternionClass F
  exact (hasFourQuaternionPresentation_iff_completion
    h₂ IsQuaternionClass q₁ q₂ q₃).2
      (hCompletion q₁ q₂ q₃ hq₁ hq₂ hq₃)

/-- Abstract form of Gille's intrinsic rank-four hermitian route.  The datum
and isotropy predicate are kept abstract here; an implementation must encode
`D = Q₂ ⊗ Q₃`, the two rank-two summands, and the prescribed Clifford
invariants. -/
structure HermitianEffectivityReduction
    (C : BoundaryRealization A) where
  HermitianDatum : Type w
  datum : A → A → A → HermitianDatum
  IsIsotropic : HermitianDatum → Prop
  realize : ∀ q₁ q₂ q₃ : A,
    IsIsotropic (datum q₁ q₂ q₃) → C.Object
  packet_realize : ∀ (q₁ q₂ q₃ : A)
      (hIso : IsIsotropic (datum q₁ q₂ q₃)),
    C.packet (realize q₁ q₂ q₃ hIso) =
      BrauerPacket.ofTriple q₁ q₂ q₃

/-- The exact isotropy statement required from a hermitian reduction on the
quaternion-triple locus. -/
def HermitianIsotropyGoal
    (R : HermitianEffectivityReduction (A := A) C)
    (IsQuaternionClass : A → Prop) : Prop :=
  ∀ q₁ q₂ q₃ : A,
    IsQuaternionClass q₁ → IsQuaternionClass q₂ → IsQuaternionClass q₃ →
      R.IsIsotropic (R.datum q₁ q₂ q₃)

/-- The rank-four hermitian isotropy theorem implies the exact E7 realization
goal once the construction from an isotropic vector to a quadratic pair is
provided. -/
theorem e7RealizationGoal_of_hermitianIsotropy
    (C : BoundaryRealization A) (IsQuaternionClass : A → Prop)
    (R : HermitianEffectivityReduction (A := A) C)
    (hIso : HermitianIsotropyGoal R IsQuaternionClass) :
    E7RealizationGoal C IsQuaternionClass := by
  intro q₁ q₂ q₃ hq₁ hq₂ hq₃
  let h := hIso q₁ q₂ q₃ hq₁ hq₂ hq₃
  exact ⟨R.realize q₁ q₂ q₃ h, R.packet_realize q₁ q₂ q₃ h⟩

/-- Triality operations on actual realizations. -/
structure TrialityClosed (C : BoundaryRealization A) where
  rotateObject : C.Object → C.Object
  reflectObject : C.Object → C.Object
  packet_rotate : ∀ X,
    C.packet (rotateObject X) = BrauerPacket.rotate (C.packet X)
  packet_reflect : ∀ X,
    C.packet (reflectObject X) = BrauerPacket.reflect (C.packet X)

/-- Effectivity is preserved by cyclic triality relabelling. -/
theorem BoundaryRealization.isEffective_rotate
    (C : BoundaryRealization A) (T : TrialityClosed C)
    {P : BrauerPacket A} (hP : C.IsEffective P) :
    C.IsEffective (BrauerPacket.rotate P) := by
  rcases hP with ⟨X, hX⟩
  exact ⟨T.rotateObject X, (T.packet_rotate X).trans (congrArg BrauerPacket.rotate hX)⟩

/-- Effectivity is preserved by the half-spin reflection. -/
theorem BoundaryRealization.isEffective_reflect
    (C : BoundaryRealization A) (T : TrialityClosed C)
    {P : BrauerPacket A} (hP : C.IsEffective P) :
    C.IsEffective (BrauerPacket.reflect P) := by
  rcases hP with ⟨X, hX⟩
  exact ⟨T.reflectObject X,
    (T.packet_reflect X).trans (congrArg BrauerPacket.reflect hX)⟩

end RiemannResearch.E7.QuaternionTrialityPacket
