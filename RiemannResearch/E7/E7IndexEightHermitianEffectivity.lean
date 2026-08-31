/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.E7IndexEightBoundary

/-!
# The hermitian reduction restricted to the hard index-eight E7 stratum

`E7BoundaryEffectivity` records Gille's rank-four hermitian route for all
quaternion triples. The remaining type-E7 case only requires that route when
the total quaternion class has Schur index eight. This file isolates precisely
that restricted input and proves that it supplies the already formalized
index-eight packet and central-boundary effectivity goals.

No isotropy theorem is assumed here. An implementation of
`IndexEightHermitianIsotropyGoal` must still encode the actual biquaternion
algebra `D = Q₂ ⊗ Q₃`, Gille's prescribed rank-four hermitian quadratic pair,
and a genuine isotropic vector.
-/

namespace RiemannResearch.E7.QuaternionTrialityPacket

universe u v w

variable {A : Type u} [AddCommGroup A]
variable {C : BoundaryRealization.{u, v} A}

/-- The exact hermitian-isotropy theorem needed in the hard E7 stratum.

Unlike `HermitianIsotropyGoal`, this asks for isotropy only for quaternion
triples whose total Brauer class has Schur index eight. -/
def IndexEightHermitianIsotropyGoal
    (I : BrauerIndexModel A)
    (R : HermitianEffectivityReduction.{u, w, v} (A := A) C)
    (IsQuaternionClass : A → Prop) : Prop :=
  ∀ q₁ q₂ q₃ : A,
    IsQuaternionClass q₁ →
      IsQuaternionClass q₂ →
      IsQuaternionClass q₃ →
      I.index (q₁ + q₂ + q₃) = 8 →
      R.IsIsotropic (R.datum q₁ q₂ q₃)

/-- Isotropy of Gille's prescribed hermitian datum on the index-eight locus
produces an actual realization of every hard E7 packet. -/
theorem e7IndexEightRealizationGoal_of_hermitianIsotropy
    (I : BrauerIndexModel A)
    (R : HermitianEffectivityReduction.{u, w, v} (A := A) C)
    (IsQuaternionClass : A → Prop)
    (hIso : IndexEightHermitianIsotropyGoal I R IsQuaternionClass) :
    E7IndexEightRealizationGoal I C IsQuaternionClass := by
  intro q₁ q₂ q₃ hq₁ hq₂ hq₃ hIndex
  have h : R.IsIsotropic (R.datum q₁ q₂ q₃) :=
    hIso q₁ q₂ q₃ hq₁ hq₂ hq₃ hIndex
  exact ⟨R.realize q₁ q₂ q₃ h, R.packet_realize q₁ q₂ q₃ h⟩

/-- Once all non-index-eight packets are known to be effective, the restricted
hermitian theorem closes the full abstract E7 realization goal. -/
theorem e7RealizationGoal_of_away_and_indexEightHermitianIsotropy
    (I : BrauerIndexModel A)
    (R : HermitianEffectivityReduction.{u, w, v} (A := A) C)
    (IsQuaternionClass : A → Prop)
    (hAway : E7AwayFromIndexEightRealizationGoal I C IsQuaternionClass)
    (hIso : IndexEightHermitianIsotropyGoal I R IsQuaternionClass) :
    E7RealizationGoal C IsQuaternionClass := by
  exact (e7RealizationGoal_iff_indexEight_partition
    I C IsQuaternionClass).2
      ⟨hAway,
        e7IndexEightRealizationGoal_of_hermitianIsotropy
          I R IsQuaternionClass hIso⟩

section CentralBoundary

variable [Module (ZMod 2) A]

/-- The same restricted hermitian theorem discharges the index-eight central
Tits-boundary formulation. -/
theorem indexEightCentralTargetEffectivityGoal_of_hermitianIsotropy
    (I : BrauerIndexModel A)
    (R : HermitianEffectivityReduction.{u, w, v} (A := A) C)
    (IsQuaternionClass : A → Prop)
    (hIso : IndexEightHermitianIsotropyGoal I R IsQuaternionClass) :
    IndexEightCentralTargetEffectivityGoal I C IsQuaternionClass := by
  exact (e7IndexEightRealizationGoal_iff_centralTargetEffectivity
    I C IsQuaternionClass).1
      (e7IndexEightRealizationGoal_of_hermitianIsotropy
        I R IsQuaternionClass hIso)

end CentralBoundary

end RiemannResearch.E7.QuaternionTrialityPacket
