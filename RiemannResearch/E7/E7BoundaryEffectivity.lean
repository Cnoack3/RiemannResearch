import RiemannResearch.E7.D4CenterTitsPacket

namespace RiemannResearch.E7.QuaternionTrialityPacket

universe u v w
variable {A : Type u} [AddCommGroup A]

structure BoundaryRealization (A : Type u) [AddCommGroup A] where
  Object : Type v
  packet : Object → BrauerPacket A
  packet_isBalanced : ∀ X, BrauerPacket.IsBalanced (packet X)

namespace BoundaryRealization
variable (C : BoundaryRealization A)
def IsEffective (P : BrauerPacket A) : Prop := ∃ X : C.Object, C.packet X = P

theorem isEffective_isBalanced {P : BrauerPacket A}
    (hP : C.IsEffective P) : BrauerPacket.IsBalanced P := by
  rcases hP with ⟨X, rfl⟩
  exact C.packet_isBalanced X
end BoundaryRealization

def IsQuaternionTargetPacket (Q : A → Prop) (P : BrauerPacket A) : Prop :=
  ∃ q₁ q₂ q₃ : A, Q q₁ ∧ Q q₂ ∧ Q q₃ ∧ P = BrauerPacket.ofTriple q₁ q₂ q₃

def E7RealizationGoal (C : BoundaryRealization A) (Q : A → Prop) : Prop :=
  ∀ q₁ q₂ q₃ : A, Q q₁ → Q q₂ → Q q₃ →
    C.IsEffective (BrauerPacket.ofTriple q₁ q₂ q₃)

theorem e7RealizationGoal_iff_targetPackets
    (C : BoundaryRealization A) (Q : A → Prop) :
    E7RealizationGoal C Q ↔
      ∀ P : BrauerPacket A, IsQuaternionTargetPacket Q P → C.IsEffective P := by
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

def IsQuaternionTargetCentralDatum (Q : A → Prop)
    (t : D4CenterCharacter →ₗ[ZMod 2] A) : Prop :=
  IsQuaternionTargetPacket Q (packetOfCentralTitsMap t)

def CentralTargetEffectivityGoal (C : BoundaryRealization A) (Q : A → Prop) : Prop :=
  ∀ t : D4CenterCharacter →ₗ[ZMod 2] A,
    IsQuaternionTargetCentralDatum Q t → C.IsEffective (packetOfCentralTitsMap t)

theorem e7RealizationGoal_iff_centralTargetEffectivity
    (C : BoundaryRealization A) (Q : A → Prop) :
    E7RealizationGoal C Q ↔ CentralTargetEffectivityGoal C Q := by
  constructor
  · intro h t ht
    rcases ht with ⟨q₁, q₂, q₃, hq₁, hq₂, hq₃, hEq⟩
    rcases h q₁ q₂ q₃ hq₁ hq₂ hq₃ with ⟨X, hX⟩
    exact ⟨X, hX.trans hEq.symm⟩
  · intro h q₁ q₂ q₃ hq₁ hq₂ hq₃
    let P : BrauerPacket A := BrauerPacket.ofTriple q₁ q₂ q₃
    let t : D4CenterCharacter →ₗ[ZMod 2] A :=
      centralTitsMap P.underlying P.cliffordPlus
    have hP : BrauerPacket.IsBalanced P :=
      BrauerPacket.isBalanced_ofTriple module_isExponentTwo q₁ q₂ q₃
    have ht : packetOfCentralTitsMap t = P :=
      packetOfCentralTitsMap_centralTitsMap_of_isBalanced P hP
    have hTarget : IsQuaternionTargetCentralDatum Q t :=
      ⟨q₁, q₂, q₃, hq₁, hq₂, hq₃, ht⟩
    rcases h t hTarget with ⟨X, hX⟩
    exact ⟨X, hX.trans ht⟩

def BalancedBoundarySurjective (C : BoundaryRealization A) : Prop :=
  ∀ P : BrauerPacket A, BrauerPacket.IsBalanced P → C.IsEffective P

def CentralBoundarySurjective (C : BoundaryRealization A) : Prop :=
  ∀ t : D4CenterCharacter →ₗ[ZMod 2] A, C.IsEffective (packetOfCentralTitsMap t)

theorem balancedBoundarySurjective_iff_centralBoundarySurjective
    (C : BoundaryRealization A) :
    BalancedBoundarySurjective C ↔ CentralBoundarySurjective C := by
  constructor
  · intro h t
    exact h (packetOfCentralTitsMap t) (packetOfCentralTitsMap_isBalanced t)
  · intro h P hP
    let t := centralTitsMap P.underlying P.cliffordPlus
    have ht : packetOfCentralTitsMap t = P :=
      packetOfCentralTitsMap_centralTitsMap_of_isBalanced P hP
    rcases h t with ⟨X, hX⟩
    exact ⟨X, hX.trans ht⟩

theorem e7RealizationGoal_of_balancedBoundarySurjective
    (C : BoundaryRealization A) (Q : A → Prop)
    (h : BalancedBoundarySurjective C) : E7RealizationGoal C Q := by
  intro q₁ q₂ q₃ _ _ _
  exact h (BrauerPacket.ofTriple q₁ q₂ q₃)
    (BrauerPacket.isBalanced_ofTriple module_isExponentTwo q₁ q₂ q₃)
end CentralBoundary

structure FourQuaternionConstructor
    (C : BoundaryRealization A) (Q : A → Prop) where
  realize : ∀ P : FourClassPacket A,
    Q P.p₁ → Q P.p₂ → Q P.p₃ → Q P.p₄ → P.total = 0 → C.Object
  packet_realize : ∀ (P : FourClassPacket A)
      (hp₁ : Q P.p₁) (hp₂ : Q P.p₂) (hp₃ : Q P.p₃) (hp₄ : Q P.p₄)
      (hTotal : P.total = 0),
    C.packet (realize P hp₁ hp₂ hp₃ hp₄ hTotal) = P.brauerPacket

theorem BoundaryRealization.isEffective_of_fourQuaternionPresentation
    (C : BoundaryRealization A) (Q : A → Prop)
    (F : FourQuaternionConstructor C Q) (q₁ q₂ q₃ : A)
    (h : HasFourQuaternionPresentation Q q₁ q₂ q₃) :
    C.IsEffective (BrauerPacket.ofTriple q₁ q₂ q₃) := by
  rcases h with ⟨P, hQ, hTotal, hPacket⟩
  refine ⟨F.realize P hQ.1 hQ.2.1 hQ.2.2.1 hQ.2.2.2 hTotal, ?_⟩
  exact (F.packet_realize P hQ.1 hQ.2.1 hQ.2.2.1 hQ.2.2.2 hTotal).trans hPacket

theorem e7RealizationGoal_of_fourQuaternionCompletions
    (h₂ : IsExponentTwo A) (C : BoundaryRealization A) (Q : A → Prop)
    (F : FourQuaternionConstructor C Q)
    (hCompletion : ∀ q₁ q₂ q₃ : A,
      Q q₁ → Q q₂ → Q q₃ → HasQuaternionCompletion Q q₁ q₂ q₃) :
    E7RealizationGoal C Q := by
  intro q₁ q₂ q₃ hq₁ hq₂ hq₃
  apply C.isEffective_of_fourQuaternionPresentation Q F
  exact (hasFourQuaternionPresentation_iff_completion h₂ Q q₁ q₂ q₃).2
    (hCompletion q₁ q₂ q₃ hq₁ hq₂ hq₃)

structure HermitianEffectivityReduction (C : BoundaryRealization A) where
  HermitianDatum : Type w
  datum : A → A → A → HermitianDatum
  IsIsotropic : HermitianDatum → Prop
  realize : ∀ q₁ q₂ q₃ : A, IsIsotropic (datum q₁ q₂ q₃) → C.Object
  packet_realize : ∀ (q₁ q₂ q₃ : A) (hIso : IsIsotropic (datum q₁ q₂ q₃)),
    C.packet (realize q₁ q₂ q₃ hIso) = BrauerPacket.ofTriple q₁ q₂ q₃

def HermitianIsotropyGoal (R : HermitianEffectivityReduction (A := A) C)
    (Q : A → Prop) : Prop :=
  ∀ q₁ q₂ q₃ : A, Q q₁ → Q q₂ → Q q₃ → R.IsIsotropic (R.datum q₁ q₂ q₃)

theorem e7RealizationGoal_of_hermitianIsotropy
    (C : BoundaryRealization A) (Q : A → Prop)
    (R : HermitianEffectivityReduction (A := A) C)
    (hIso : HermitianIsotropyGoal R Q) : E7RealizationGoal C Q := by
  intro q₁ q₂ q₃ hq₁ hq₂ hq₃
  let h := hIso q₁ q₂ q₃ hq₁ hq₂ hq₃
  exact ⟨R.realize q₁ q₂ q₃ h, R.packet_realize q₁ q₂ q₃ h⟩

structure TrialityClosed (C : BoundaryRealization A) where
  rotateObject : C.Object → C.Object
  reflectObject : C.Object → C.Object
  packet_rotate : ∀ X, C.packet (rotateObject X) = BrauerPacket.rotate (C.packet X)
  packet_reflect : ∀ X, C.packet (reflectObject X) = BrauerPacket.reflect (C.packet X)

theorem BoundaryRealization.isEffective_rotate
    (C : BoundaryRealization A) (T : TrialityClosed C)
    {P : BrauerPacket A} (hP : C.IsEffective P) :
    C.IsEffective (BrauerPacket.rotate P) := by
  rcases hP with ⟨X, hX⟩
  exact ⟨T.rotateObject X,
    (T.packet_rotate X).trans (congrArg BrauerPacket.rotate hX)⟩

theorem BoundaryRealization.isEffective_reflect
    (C : BoundaryRealization A) (T : TrialityClosed C)
    {P : BrauerPacket A} (hP : C.IsEffective P) :
    C.IsEffective (BrauerPacket.reflect P) := by
  rcases hP with ⟨X, hX⟩
  exact ⟨T.reflectObject X,
    (T.packet_reflect X).trans (congrArg BrauerPacket.reflect hX)⟩

end RiemannResearch.E7.QuaternionTrialityPacket
