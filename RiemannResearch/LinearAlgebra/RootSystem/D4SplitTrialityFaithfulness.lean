/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.LinearAlgebra.RootSystem.D4SplitTrialityCompatibility
import RiemannResearch.LinearAlgebra.RootSystem.D4SplitFockFaithfulness

/-!
# Faithfulness of the split D4 triality representation tuple

The two concrete half-spin Fock actions jointly recover an even Clifford
element.  Since split spin points embed in the units of that even algebra, the
three-component triality representation tuple is faithful in any common
system of linear coordinates.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

open RiemannResearch.LinearAlgebra

universe uK uV

noncomputable section

variable (K : Type uK) [Field K] [Invertible (2 : K)]
variable (V : Type uV) [AddCommGroup V] [Module K V]

/-- The vector and two half-spin representations of a split spin point,
written in arbitrary common coordinates, determine the spin point. -/
theorem splitTrialityLinearTupleHom_injective
    (chart : ∀ l, (SplitTrialityModule K l) ≃ₗ[K] V) :
    Function.Injective (splitTrialityLinearTupleHom K V chart) := by
  intro g h hgh
  have hcomp (l : TrialityLabel) :
      splitTrialityLinearTupleHom K V chart g l =
        splitTrialityLinearTupleHom K V chart h l :=
    congrFun hgh l
  have hrep (l : TrialityLabel) :
      splitTrialityRepresentation K l g =
        splitTrialityRepresentation K l h := by
    apply LinearMap.ext
    intro x
    have hc := LinearEquiv.congr_fun (hcomp l) (chart l x)
    exact (chart l).injective (by
      simpa [splitTrialityLinearTupleHom, chartedRepresentation,
        representationLinearEquiv] using hc)
  have hp := hrep .halfSpinPlus
  have hm := hrep .halfSpinMinus
  change
    splitFockEvenAction K
        (((CliffordEven.spinPointToEvenUnits (splitD4Form K) g :
          (CliffordAlgebra.even (splitD4Form K))ˣ) :
            CliffordAlgebra.even (splitD4Form K))) =
      splitFockEvenAction K
        (((CliffordEven.spinPointToEvenUnits (splitD4Form K) h :
          (CliffordAlgebra.even (splitD4Form K))ˣ) :
            CliffordAlgebra.even (splitD4Form K))) at hp
  change
    splitFockOddAction K
        (((CliffordEven.spinPointToEvenUnits (splitD4Form K) g :
          (CliffordAlgebra.even (splitD4Form K))ˣ) :
            CliffordAlgebra.even (splitD4Form K))) =
      splitFockOddAction K
        (((CliffordEven.spinPointToEvenUnits (splitD4Form K) h :
          (CliffordAlgebra.even (splitD4Form K))ˣ) :
            CliffordAlgebra.even (splitD4Form K))) at hm
  have hblock :
      splitHalfSpinBlockAction K
          (((CliffordEven.spinPointToEvenUnits (splitD4Form K) g :
            (CliffordAlgebra.even (splitD4Form K))ˣ) :
              CliffordAlgebra.even (splitD4Form K))) =
        splitHalfSpinBlockAction K
          (((CliffordEven.spinPointToEvenUnits (splitD4Form K) h :
            (CliffordAlgebra.even (splitD4Form K))ˣ) :
              CliffordAlgebra.even (splitD4Form K))) :=
    Prod.ext hp hm
  have heven :=
    (splitHalfSpinBlockAction_injective_of_exteriorCliffordAction_injective
      K (splitFockCliffordAction_injective (K := K))) hblock
  apply CliffordEven.spinPointToEvenUnits_injective (splitD4Form K)
  apply Units.ext
  exact heven

end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality
