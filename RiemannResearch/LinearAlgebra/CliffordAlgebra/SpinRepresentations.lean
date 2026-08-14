/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.LinearAlgebra.CliffordAlgebra.EvenFunctoriality
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RepresentationTheory.Basic

/-!
# Pointwise representations of Mathlib spin groups

This file constructs the canonical vector representation of Mathlib's
pointwise spin group and restricts any supplied even-Clifford-algebra action
to spin points.

The vector representation is fully constructed. For the two half-spin
representations, the exact remaining algebraic input is a supplied splitting

`Cl⁰(Q) ≃ End(S⁺) × End(S⁻)`.

The file derives the two half-spin actions, their joint faithfulness, and
their restriction to spin points from that single bridge. It does not
construct the splitting, a Spin group scheme, or a compatible outer S3
action.
-/

namespace RiemannResearch.LinearAlgebra.CliffordEven

open CliffordAlgebra

universe uK uM uS uP uN

section Vector

variable {K : Type uK} [Field K] [Invertible (2 : K)]
variable {M : Type uM} [AddCommGroup M] [Module K M]

/-- Over a field of characteristic different from two, the canonical map into
the Clifford algebra is injective. -/
theorem iota_injective (Q : QuadraticForm K M) :
    Function.Injective (CliffordAlgebra.ι Q) := by
  intro x y h
  apply Module.eval_apply_injective K
  apply LinearMap.ext
  intro d
  have hc := congrArg (CliffordAlgebra.contractLeft d) h
  simp only [CliffordAlgebra.contractLeft_ι] at hc
  exact FaithfulSMul.algebraMap_injective K (CliffordAlgebra Q) hc

/-- Spin points, mapped to conjugating units of the Clifford algebra. -/
def spinConjugationHom (Q : QuadraticForm K M) :
    SpinPoint Q →* ConjAct (CliffordAlgebra Q)ˣ :=
  ConjAct.toConjAct.toMonoidHom.comp spinGroup.toUnits

/-- The conjugation representation of spin points on the full Clifford
algebra. -/
def spinCliffordRepresentation (Q : QuadraticForm K M) :
    Representation K (SpinPoint Q) (CliffordAlgebra Q) :=
  (DistribMulAction.toModuleEnd K (CliffordAlgebra Q)).comp
    (spinConjugationHom Q)

/-- The conjugation representation restricted to the range of the Clifford
generator map. -/
def spinVectorRangeRepresentation (Q : QuadraticForm K M) :
    Representation K (SpinPoint Q) (CliffordAlgebra.ι Q).range :=
  (spinCliffordRepresentation Q).subrepresentation
    (CliffordAlgebra.ι Q).range (by
      intro g x hx
      rcases hx with ⟨y, rfl⟩
      change
        ConjAct.toConjAct (spinGroup.toUnits g) •
          CliffordAlgebra.ι Q y ∈
            (CliffordAlgebra.ι Q).range
      apply spinGroup.conjAct_smul_ι_mem_range_ι
      simpa only [spinGroup.val_toUnits_apply] using g.property)

/-- The canonical pointwise vector representation, transported back from the
range of the Clifford generator map to the original quadratic module. -/
noncomputable def spinVectorRepresentation (Q : QuadraticForm K M) :
    Representation K (SpinPoint Q) M :=
  (((LinearEquiv.ofInjective (CliffordAlgebra.ι Q)
      (iota_injective Q)).symm.conjRingEquiv).toMonoidHom).comp
    (spinVectorRangeRepresentation Q)

/-- The vector representation is characterized by Clifford conjugation. -/
@[simp]
theorem iota_spinVectorRepresentation
    (Q : QuadraticForm K M) (g : SpinPoint Q) (x : M) :
    CliffordAlgebra.ι Q (spinVectorRepresentation Q g x) =
      ConjAct.toConjAct (spinGroup.toUnits g) •
        CliffordAlgebra.ι Q x := by
  simp [spinVectorRepresentation, spinVectorRangeRepresentation,
    spinCliffordRepresentation, spinConjugationHom]

/-- The vector action formula written as multiplication in the Clifford
algebra. -/
theorem iota_spinVectorRepresentation_mul
    (Q : QuadraticForm K M) (g : SpinPoint Q) (x : M) :
    CliffordAlgebra.ι Q (spinVectorRepresentation Q g x) =
      (g : CliffordAlgebra Q) * CliffordAlgebra.ι Q x *
        (spinGroup.toUnits g).inv := by
  rw [iota_spinVectorRepresentation]
  rfl

/-- Spin conjugation preserves the quadratic form on the vector module. -/
theorem spinVectorRepresentation_preserves_form
    (Q : QuadraticForm K M) (g : SpinPoint Q) (x : M) :
    Q (spinVectorRepresentation Q g x) = Q x := by
  apply FaithfulSMul.algebraMap_injective K (CliffordAlgebra Q)
  rw [← CliffordAlgebra.ι_sq_scalar, ← CliffordAlgebra.ι_sq_scalar]
  rw [iota_spinVectorRepresentation_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (spinGroup.toUnits g).inv
    (g : CliffordAlgebra Q)
    (CliffordAlgebra.ι Q x * (spinGroup.toUnits g).inv)]
  rw [show (spinGroup.toUnits g).inv * (g : CliffordAlgebra Q) = 1 by
    simpa only [spinGroup.val_toUnits_apply] using
      (spinGroup.toUnits g).inv_val]
  simp only [one_mul]
  rw [← mul_assoc (CliffordAlgebra.ι Q x)
    (CliffordAlgebra.ι Q x) (spinGroup.toUnits g).inv]
  rw [CliffordAlgebra.ι_sq_scalar]
  rw [← mul_assoc]
  rw [← Algebra.commutes]
  simp only [mul_assoc]
  rw [show (g : CliffordAlgebra Q) * (spinGroup.toUnits g).inv = 1 by
    simpa only [spinGroup.val_toUnits_apply] using
      (spinGroup.toUnits g).val_inv]
  simp

end Vector

section EvenAction

variable {K : Type uK} [CommRing K]
variable {M : Type uM} [AddCommGroup M] [Module K M]
variable {S : Type uS} [AddCommGroup S] [Module K S]

/-- Restrict a supplied representation of the even Clifford algebra to its
subgroup of spin points. -/
def spinRepresentationOfEvenAction (Q : QuadraticForm K M)
    (ρ : CliffordAlgebra.even Q →ₐ[K] Module.End K S) :
    Representation K (SpinPoint Q) S :=
  ρ.toMonoidHom.comp
    ((Units.coeHom (CliffordAlgebra.even Q)).comp
      (spinPointToEvenUnits Q))

/-- Evaluation of a restricted even-Clifford action at a spin point. -/
@[simp]
theorem spinRepresentationOfEvenAction_apply
    (Q : QuadraticForm K M)
    (ρ : CliffordAlgebra.even Q →ₐ[K] Module.End K S)
    (g : SpinPoint Q) :
    spinRepresentationOfEvenAction Q ρ g =
      ρ (((spinPointToEvenUnits Q g :
        (CliffordAlgebra.even Q)ˣ) : CliffordAlgebra.even Q)) :=
  rfl

end EvenAction

section HalfSpinInterface

variable {K : Type uK} [Field K]
variable {M : Type uM} [AddCommGroup M] [Module K M]
variable {SPlus : Type uP} [AddCommGroup SPlus] [Module K SPlus]
  [FiniteDimensional K SPlus]
variable {SMinus : Type uN} [AddCommGroup SMinus] [Module K SMinus]
  [FiniteDimensional K SMinus]

/-- Supplied split half-spin decomposition data. The algebra equivalence is
bridge data, not constructed here. -/
structure HalfSpinDecomposition (Q : QuadraticForm K M)
    (SPlus : Type uP) [AddCommGroup SPlus] [Module K SPlus]
    [FiniteDimensional K SPlus]
    (SMinus : Type uN) [AddCommGroup SMinus] [Module K SMinus]
    [FiniteDimensional K SMinus] where
  evenEquiv :
    CliffordAlgebra.even Q ≃ₐ[K]
      Module.End K SPlus × Module.End K SMinus
  plus_finrank : Module.finrank K SPlus = 8
  minus_finrank : Module.finrank K SMinus = 8

namespace HalfSpinDecomposition

/-- Projection of the supplied split even-Clifford decomposition onto the
positive half-spin factor. -/
def plusAction (Q : QuadraticForm K M)
    (D : HalfSpinDecomposition Q SPlus SMinus) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K SPlus :=
  (AlgHom.fst K (Module.End K SPlus) (Module.End K SMinus)).comp
    D.evenEquiv.toAlgHom

/-- Projection of the supplied split even-Clifford decomposition onto the
negative half-spin factor. -/
def minusAction (Q : QuadraticForm K M)
    (D : HalfSpinDecomposition Q SPlus SMinus) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K SMinus :=
  (AlgHom.snd K (Module.End K SPlus) (Module.End K SMinus)).comp
    D.evenEquiv.toAlgHom

/-- The two half-spin actions jointly detect every even Clifford element. -/
theorem jointlyFaithful (Q : QuadraticForm K M)
    (D : HalfSpinDecomposition Q SPlus SMinus) :
    Function.Injective fun x : CliffordAlgebra.even Q =>
      (D.plusAction Q x, D.minusAction Q x) := by
  intro x y h
  apply D.evenEquiv.injective
  simpa [plusAction, minusAction] using h

/-- The supplied positive half-spin action restricted to spin points. -/
def plusSpinRepresentation (Q : QuadraticForm K M)
    (D : HalfSpinDecomposition Q SPlus SMinus) :
    Representation K (SpinPoint Q) SPlus :=
  spinRepresentationOfEvenAction Q (D.plusAction Q)

/-- The supplied negative half-spin action restricted to spin points. -/
def minusSpinRepresentation (Q : QuadraticForm K M)
    (D : HalfSpinDecomposition Q SPlus SMinus) :
    Representation K (SpinPoint Q) SMinus :=
  spinRepresentationOfEvenAction Q (D.minusAction Q)

/-- Evaluation of the positive half-spin representation. -/
@[simp]
theorem plusSpinRepresentation_apply
    (Q : QuadraticForm K M)
    (D : HalfSpinDecomposition Q SPlus SMinus)
    (g : SpinPoint Q) :
    D.plusSpinRepresentation Q g =
      (D.evenEquiv
        ((spinPointToEvenUnits Q g :
          (CliffordAlgebra.even Q)ˣ) : CliffordAlgebra.even Q)).1 :=
  rfl

/-- Evaluation of the negative half-spin representation. -/
@[simp]
theorem minusSpinRepresentation_apply
    (Q : QuadraticForm K M)
    (D : HalfSpinDecomposition Q SPlus SMinus)
    (g : SpinPoint Q) :
    D.minusSpinRepresentation Q g =
      (D.evenEquiv
        ((spinPointToEvenUnits Q g :
          (CliffordAlgebra.even Q)ˣ) : CliffordAlgebra.even Q)).2 :=
  rfl

end HalfSpinDecomposition

end HalfSpinInterface

end RiemannResearch.LinearAlgebra.CliffordEven
