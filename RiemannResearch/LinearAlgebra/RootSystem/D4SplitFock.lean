/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Pi
import RiemannResearch.LinearAlgebra.CliffordAlgebra.ExteriorSpinors
import RiemannResearch.LinearAlgebra.CliffordAlgebra.SpinRepresentations
import RiemannResearch.LinearAlgebra.RootSystem.D4SplitQuadratic

/-!
# Exterior Fock representations for split D4

This file specializes the constructive exterior Fock action to the split
eight-dimensional quadratic space `H⁴`. It produces two actual pointwise Spin
representations, on the even and odd exterior-parity pieces of `Λ(K⁴)`.

The two parity pieces are proved to have finrank eight, so they give actual
split half-spin Fock modules and pointwise Spin representations. Their two
actions are also packaged as the canonical block homomorphism

`Cl⁰(H⁴) → End(Λeven K⁴) × End(Λodd K⁴)`.

Both sides are proved to have dimension 128. Consequently full faithfulness of
the exterior Fock action implies that the block map is an algebra equivalence;
this file exposes the exact reduction. `D4SplitFockFaithfulness` closes the
PBW/matrix-unit boundary constructively and supplies the unconditional split
half-spin decomposition.

This lower module constructs no outer triality action or group scheme.
`D4SplitTrialityCompatibility` supplies the separate related-triples
compatibility layer; split Spin(8) representability remains open.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

open CliffordAlgebra

universe u

variable (K : Type u) [Field K]

/-- The full exterior Fock space `Λ(K⁴)` for split D4. -/
abbrev SplitFockSpace :=
  CliffordEven.ExteriorFockSpace (K := K) (U := Fin 4 → K)

/-- The even exterior-parity Fock space for split D4. -/
abbrev SplitFockEven :=
  CliffordEven.ExteriorFockEven (K := K) (U := Fin 4 → K)

/-- The odd exterior-parity Fock space for split D4. -/
abbrev SplitFockOdd :=
  CliffordEven.ExteriorFockOdd (K := K) (U := Fin 4 → K)

/-- The positive split half-spin Fock module. -/
abbrev SplitHalfSpinPlus := SplitFockEven K

/-- The negative split half-spin Fock module. -/
abbrev SplitHalfSpinMinus := SplitFockOdd K

/-- The constructive Clifford action of the split D4 form on its full Fock
space. -/
def splitFockCliffordAction :
    CliffordAlgebra (splitD4Form K) →ₐ[K]
      Module.End K (SplitFockSpace K) :=
  CliffordEven.exteriorCliffordAction

/-- The constructive even-Clifford action on even exterior parity. -/
def splitFockEvenAction :
    CliffordAlgebra.even (splitD4Form K) →ₐ[K]
      Module.End K (SplitFockEven K) :=
  CliffordEven.exteriorFockEvenAction

/-- The constructive even-Clifford action on odd exterior parity. -/
def splitFockOddAction :
    CliffordAlgebra.even (splitD4Form K) →ₐ[K]
      Module.End K (SplitFockOdd K) :=
  CliffordEven.exteriorFockOddAction

/-- The pointwise Spin representation on even exterior parity. -/
def splitEvenFockSpinRepresentation :
    Representation K (CliffordEven.SpinPoint (splitD4Form K))
      (SplitFockEven K) :=
  CliffordEven.spinRepresentationOfEvenAction
    (splitD4Form K) (splitFockEvenAction K)

/-- The pointwise Spin representation on odd exterior parity. -/
def splitOddFockSpinRepresentation :
    Representation K (CliffordEven.SpinPoint (splitD4Form K))
      (SplitFockOdd K) :=
  CliffordEven.spinRepresentationOfEvenAction
    (splitD4Form K) (splitFockOddAction K)

@[simp]
theorem splitEvenFockSpinRepresentation_apply
    (g : CliffordEven.SpinPoint (splitD4Form K)) :
    splitEvenFockSpinRepresentation K g =
      splitFockEvenAction K
        (((CliffordEven.spinPointToEvenUnits (splitD4Form K) g :
          (CliffordAlgebra.even (splitD4Form K))ˣ) :
            CliffordAlgebra.even (splitD4Form K))) :=
  rfl

@[simp]
theorem splitOddFockSpinRepresentation_apply
    (g : CliffordEven.SpinPoint (splitD4Form K)) :
    splitOddFockSpinRepresentation K g =
      splitFockOddAction K
        (((CliffordEven.spinPointToEvenUnits (splitD4Form K) g :
          (CliffordAlgebra.even (splitD4Form K))ˣ) :
            CliffordAlgebra.even (splitD4Form K))) :=
  rfl


/-- A norm-one hyperbolic vector whose Fock action exchanges parity. -/
def splitFockParityUnit : SplitD4Space K :=
  (LinearMap.proj 0,
    LinearMap.single K (fun _ : Fin 4 => K) 0 1)

@[simp]
theorem dualProd_splitFockParityUnit :
    QuadraticForm.dualProd K (Fin 4 → K)
      (splitFockParityUnit K) = 1 := by
  simp [splitFockParityUnit, QuadraticForm.dualProd_apply]

/-- The Fock action of the chosen hyperbolic unit is an involution. -/
theorem splitFockGenerator_parityUnit_sq :
    CliffordEven.exteriorFockGenerator
          (K := K) (U := Fin 4 → K) (splitFockParityUnit K) *
        CliffordEven.exteriorFockGenerator
          (K := K) (U := Fin 4 → K) (splitFockParityUnit K) = 1 := by
  rw [CliffordEven.exteriorFockGenerator_sq,
    dualProd_splitFockParityUnit]
  exact map_one (algebraMap K
    (Module.End K (SplitFockSpace K)))

/-- The chosen hyperbolic unit identifies the even and odd Fock pieces. -/
noncomputable def splitFockParityEquiv :
    SplitFockEven K ≃ₗ[K] SplitFockOdd K :=
  LinearEquiv.ofLinear
    ((CliffordEven.exteriorFockGenerator
      (K := K) (U := Fin 4 → K) (splitFockParityUnit K)).restrict
        (fun _x hx =>
          CliffordEven.exteriorFockGenerator_mem_odd_of_mem_even
            (splitFockParityUnit K) hx))
    ((CliffordEven.exteriorFockGenerator
      (K := K) (U := Fin 4 → K) (splitFockParityUnit K)).restrict
        (fun _x hx =>
          CliffordEven.exteriorFockGenerator_mem_even_of_mem_odd
            (splitFockParityUnit K) hx))
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have h := LinearMap.congr_fun
        (splitFockGenerator_parityUnit_sq K) x
      simpa [Module.End.mul_apply] using h)
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have h := LinearMap.congr_fun
        (splitFockGenerator_parityUnit_sq K) x
      simpa [Module.End.mul_apply] using h)

/-- The full rank-four exterior Fock space has dimension sixteen. -/
theorem splitFockSpace_finrank :
    Module.finrank K (SplitFockSpace K) = 16 := by
  rw [Module.finrank_eq_card_basis
    (Pi.basisFun K (Fin 4)).ExteriorAlgebra]
  simp

noncomputable local instance splitFockFinite :
    Module.Finite K (SplitFockSpace K) :=
  Module.Finite.of_basis
    (Pi.basisFun K (Fin 4)).ExteriorAlgebra

/-- Both parity halves of the rank-four Fock space have dimension eight. -/
theorem splitFockParity_finranks :
    Module.finrank K (SplitFockEven K) = 8 ∧
      Module.finrank K (SplitFockOdd K) = 8 := by
  have heq := (splitFockParityEquiv K).finrank_eq
  change Module.finrank K (SplitFockEven K) =
    Module.finrank K (SplitFockOdd K) at heq
  have hsum := (Submodule.prodEquivOfIsCompl
    (CliffordAlgebra.evenOdd
      (0 : QuadraticForm K (Fin 4 → K)) 0)
    (CliffordAlgebra.evenOdd
      (0 : QuadraticForm K (Fin 4 → K)) 1)
    (CliffordAlgebra.evenOdd_isCompl
      (0 : QuadraticForm K (Fin 4 → K)))).finrank_eq
  rw [Module.finrank_prod, splitFockSpace_finrank] at hsum
  change Module.finrank K (SplitFockEven K) +
    Module.finrank K (SplitFockOdd K) = 16 at hsum
  omega

theorem splitHalfSpinPlus_finrank :
    Module.finrank K (SplitHalfSpinPlus K) = 8 :=
  (splitFockParity_finranks K).1

theorem splitHalfSpinMinus_finrank :
    Module.finrank K (SplitHalfSpinMinus K) = 8 :=
  (splitFockParity_finranks K).2

/-- The two constructed half-spin actions, packaged as one block
homomorphism. Proving this map bijective is the remaining even-Clifford
splitting obligation. -/
def splitHalfSpinBlockAction :
    CliffordAlgebra.even (splitD4Form K) →ₐ[K]
      Module.End K (SplitHalfSpinPlus K) ×
        Module.End K (SplitHalfSpinMinus K) :=
  (splitFockEvenAction K).prod (splitFockOddAction K)

/-- The positive split half-spin pointwise representation. -/
abbrev splitHalfSpinPlusRepresentation :=
  splitEvenFockSpinRepresentation K

/-- The negative split half-spin pointwise representation. -/
abbrev splitHalfSpinMinusRepresentation :=
  splitOddFockSpinRepresentation K

/-- The product of the two half-spin endomorphism algebras has dimension
128. -/
theorem splitHalfSpinBlockTarget_finrank :
    Module.finrank K
      (Module.End K (SplitHalfSpinPlus K) ×
        Module.End K (SplitHalfSpinMinus K)) = 128 := by
  rw [Module.finrank_eq_card_basis
    ((Module.finBasis K (SplitHalfSpinPlus K)).end.prod
      (Module.finBasis K (SplitHalfSpinMinus K)).end)]
  simp [splitHalfSpinPlus_finrank, splitHalfSpinMinus_finrank]

noncomputable local instance splitHalfSpinBlockTargetFinite :
    Module.Finite K
      (Module.End K (SplitHalfSpinPlus K) ×
        Module.End K (SplitHalfSpinMinus K)) :=
  Module.Finite.of_basis
    ((Module.finBasis K (SplitHalfSpinPlus K)).end.prod
      (Module.finBasis K (SplitHalfSpinMinus K)).end)

/-- Faithfulness of the full exterior Fock action implies joint faithfulness
of its two parity restrictions. -/
theorem splitHalfSpinBlockAction_injective_of_exteriorCliffordAction_injective
    (hfull : Function.Injective (splitFockCliffordAction K)) :
    Function.Injective (splitHalfSpinBlockAction K) := by
  intro a b hab
  apply Subtype.ext
  apply hfull
  apply LinearMap.ext_on_codisjoint
    (CliffordAlgebra.evenOdd_isCompl
      (0 : QuadraticForm K (Fin 4 → K))).codisjoint
  · intro z hz
    have he := DFunLike.congr_fun
      (congrArg Prod.fst hab) (⟨z, hz⟩ : SplitFockEven K)
    exact congrArg Subtype.val he
  · intro z hz
    have ho := DFunLike.congr_fun
      (congrArg Prod.snd hab) (⟨z, hz⟩ : SplitFockOdd K)
    exact congrArg Subtype.val ho

/-- A basis of the split eight-dimensional quadratic space. -/
noncomputable def splitD4Basis :
    Module.Basis (Fin 8) K (SplitD4Space K) :=
  ((Pi.basisFun K (Fin 4)).dualBasis.prod
    (Pi.basisFun K (Fin 4))).reindex finSumFinEquiv

/-- The exterior algebra of the split D4 quadratic space has dimension
256. -/
theorem splitD4Exterior_finrank :
    Module.finrank K
      (ExteriorAlgebra K (SplitD4Space K)) = 256 := by
  rw [Module.finrank_eq_card_basis
    (splitD4Basis K).ExteriorAlgebra]
  simp

/-- Multiplication respects the mod-two Clifford grading. -/
theorem splitClifford_mul_mem_evenOdd {i j : ZMod 2}
    {x y : CliffordAlgebra (splitD4Form K)}
    (hx : x ∈ CliffordAlgebra.evenOdd (splitD4Form K) i)
    (hy : y ∈ CliffordAlgebra.evenOdd (splitD4Form K) j) :
    x * y ∈ CliffordAlgebra.evenOdd
      (splitD4Form K) (i + j) :=
  CliffordAlgebra.evenOdd_mul_le (splitD4Form K) i j
    (Submodule.mul_mem_mul hx hy)

/-- Left multiplication by the chosen norm-one hyperbolic vector is an
involution on the full split Clifford algebra. -/
theorem splitCliffordParityUnit_mulLeft_sq :
    LinearMap.mulLeft K
        (CliffordAlgebra.ι (splitD4Form K)
          (splitFockParityUnit K)) *
      LinearMap.mulLeft K
        (CliffordAlgebra.ι (splitD4Form K)
          (splitFockParityUnit K)) = 1 := by
  apply LinearMap.ext
  intro x
  simp only [Module.End.mul_apply, LinearMap.mulLeft_apply]
  rw [← mul_assoc, CliffordAlgebra.ι_sq_scalar]
  have hq : splitD4Form K (splitFockParityUnit K) = 1 :=
    dualProd_splitFockParityUnit K
  rw [hq]
  simp

/-- The norm-one hyperbolic vector also exchanges parity in the source
Clifford algebra. -/
noncomputable def splitCliffordParityEquiv :
    ↥(CliffordAlgebra.evenOdd (splitD4Form K) 0) ≃ₗ[K]
      ↥(CliffordAlgebra.evenOdd (splitD4Form K) 1) :=
  LinearEquiv.ofLinear
    ((LinearMap.mulLeft K
      (CliffordAlgebra.ι (splitD4Form K)
        (splitFockParityUnit K))).restrict
      (fun _x hx => by
        have h := splitClifford_mul_mem_evenOdd K
          (CliffordAlgebra.ι_mem_evenOdd_one
            (splitD4Form K) (splitFockParityUnit K)) hx
        rw [add_zero] at h
        exact h))
    ((LinearMap.mulLeft K
      (CliffordAlgebra.ι (splitD4Form K)
        (splitFockParityUnit K))).restrict
      (fun _x hx => by
        have h := splitClifford_mul_mem_evenOdd K
          (CliffordAlgebra.ι_mem_evenOdd_one
            (splitD4Form K) (splitFockParityUnit K)) hx
        rw [show (1 : ZMod 2) + 1 = 0 by decide] at h
        exact h))
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have h := LinearMap.congr_fun
        (splitCliffordParityUnit_mulLeft_sq K) x
      change
        CliffordAlgebra.ι (splitD4Form K) (splitFockParityUnit K) *
            (CliffordAlgebra.ι (splitD4Form K)
              (splitFockParityUnit K) *
              (x : CliffordAlgebra (splitD4Form K))) =
          (x : CliffordAlgebra (splitD4Form K))
      exact h)
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have h := LinearMap.congr_fun
        (splitCliffordParityUnit_mulLeft_sq K) x
      change
        CliffordAlgebra.ι (splitD4Form K) (splitFockParityUnit K) *
            (CliffordAlgebra.ι (splitD4Form K)
              (splitFockParityUnit K) *
              (x : CliffordAlgebra (splitD4Form K))) =
          (x : CliffordAlgebra (splitD4Form K))
      exact h)

variable [Invertible (2 : K)]

noncomputable local instance splitD4ExteriorFinite :
    Module.Finite K
      (ExteriorAlgebra K (SplitD4Space K)) :=
  Module.Finite.of_basis (splitD4Basis K).ExteriorAlgebra

noncomputable local instance splitD4CliffordFinite :
    Module.Finite K
      (CliffordAlgebra (splitD4Form K)) :=
  Module.Finite.equiv
    (CliffordAlgebra.equivExterior (splitD4Form K)).symm

/-- The split D4 Clifford algebra has dimension 256. -/
theorem splitD4Clifford_finrank :
    Module.finrank K
      (CliffordAlgebra (splitD4Form K)) = 256 := by
  rw [(CliffordAlgebra.equivExterior
    (splitD4Form K)).finrank_eq]
  exact splitD4Exterior_finrank K

/-- The two parity pieces of the split D4 Clifford algebra each have
dimension 128. -/
theorem splitD4CliffordParity_finranks :
    Module.finrank K
        ↥(CliffordAlgebra.evenOdd (splitD4Form K) 0) = 128 ∧
      Module.finrank K
        ↥(CliffordAlgebra.evenOdd (splitD4Form K) 1) = 128 := by
  have heq := (splitCliffordParityEquiv K).finrank_eq
  have hsum := (Submodule.prodEquivOfIsCompl
    (CliffordAlgebra.evenOdd (splitD4Form K) 0)
    (CliffordAlgebra.evenOdd (splitD4Form K) 1)
    (CliffordAlgebra.evenOdd_isCompl
      (splitD4Form K))).finrank_eq
  rw [Module.finrank_prod, splitD4Clifford_finrank] at hsum
  omega

/-- The even split D4 Clifford algebra has dimension 128. -/
theorem splitD4EvenClifford_finrank :
    Module.finrank K
      (CliffordAlgebra.even (splitD4Form K)) = 128 := by
  change Module.finrank K
    ↥(CliffordAlgebra.even (splitD4Form K)).toSubmodule = 128
  rw [CliffordAlgebra.even_toSubmodule]
  exact (splitD4CliffordParity_finranks K).1

/-- Full Fock faithfulness makes the parity-block action bijective: the
remaining step after injectivity is finite-dimensional linear algebra. -/
theorem splitHalfSpinBlockAction_bijective_of_exteriorCliffordAction_injective
    (hfull : Function.Injective (splitFockCliffordAction K)) :
    Function.Bijective (splitHalfSpinBlockAction K) := by
  have hinj : Function.Injective (splitHalfSpinBlockAction K) :=
    splitHalfSpinBlockAction_injective_of_exteriorCliffordAction_injective
      K hfull
  let _ := Module.Free.of_divisionRing K
    (CliffordAlgebra.even (splitD4Form K))
  let _ := Module.Free.of_divisionRing K
    (Module.End K (SplitHalfSpinPlus K) ×
      Module.End K (SplitHalfSpinMinus K))
  refine ⟨hinj, ?_⟩
  let e :
      (Module.End K (SplitHalfSpinPlus K) ×
        Module.End K (SplitHalfSpinMinus K)) ≃ₗ[K]
      CliffordAlgebra.even (splitD4Form K) :=
    Classical.choice
      (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (by
        rw [splitHalfSpinBlockTarget_finrank,
          splitD4EvenClifford_finrank]))
  have hg_inj : Function.Injective
      (e.toLinearMap.comp (splitHalfSpinBlockAction K).toLinearMap) :=
    e.injective.comp hinj
  have hg_surj : Function.Surjective
      (e.toLinearMap.comp (splitHalfSpinBlockAction K).toLinearMap) :=
    LinearMap.injective_iff_surjective.mp hg_inj
  intro y
  rcases hg_surj (e y) with ⟨x, hx⟩
  refine ⟨x, e.injective ?_⟩
  exact hx

/-- Under the single full-Fock faithfulness hypothesis, the two constructed
half-spin actions give the expected even-Clifford algebra equivalence. -/
noncomputable def splitHalfSpinBlockEquiv_of_exteriorCliffordAction_injective
    (hfull : Function.Injective (splitFockCliffordAction K)) :
    CliffordAlgebra.even (splitD4Form K) ≃ₐ[K]
      Module.End K (SplitHalfSpinPlus K) ×
        Module.End K (SplitHalfSpinMinus K) :=
  AlgEquiv.ofBijective (splitHalfSpinBlockAction K)
    (splitHalfSpinBlockAction_bijective_of_exteriorCliffordAction_injective
      K hfull)

/-- The concrete split-D4 half-spin decomposition, conditional only on full
faithfulness of the constructed exterior Fock action. -/
noncomputable def splitHalfSpinDecomposition_of_exteriorCliffordAction_injective
    (hfull : Function.Injective (splitFockCliffordAction K)) :
    CliffordEven.HalfSpinDecomposition (splitD4Form K)
      (SplitHalfSpinPlus K) (SplitHalfSpinMinus K) where
  evenEquiv :=
    splitHalfSpinBlockEquiv_of_exteriorCliffordAction_injective K hfull
  plus_finrank := splitHalfSpinPlus_finrank K
  minus_finrank := splitHalfSpinMinus_finrank K

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality
