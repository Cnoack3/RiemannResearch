/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.AlgebraicGroupFiniteStage
import RiemannResearch.GaloisCohomology.FiniteGaloisGlobalFpqcH1

/-!
# Continuous cocycles at finite fpqc stages

This module sends an action-compatible finite quotient factorization of a
continuous absolute-Galois cocycle to its canonical finite-Galois fixed-cover
Čech class and then to global fpqc Čech `H¹`.  The formulas make the
finite-stage comparison completely explicit.

Independence of the chosen finite stage is a separate naturality statement:
it requires comparison of the finite-Galois Čech constructions under
enlarging fixed fields.
-/

namespace RiemannResearch.GaloisCohomology

open CategoryTheory
open RiemannResearch.AlgebraicGeometry
open ContinuousNonabelianCocycle
open ContinuousNonabelianCocycle.ActionCompatibleFiniteQuotientFactorization

universe u

noncomputable section

variable (K A : Type u) [Field K] [PerfectField K]
variable [CommRing A] [HopfAlgebra K A]
variable
  {a : ContinuousNonabelianCocycle
    (Field.absoluteGaloisGroup K) (AlgebraicGroupGeometricPoints K A)}

local instance (H : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    FiniteDimensional K (AbsoluteGaloisOpenNormalSubgroup.fixedField K H) :=
  AbsoluteGaloisOpenNormalSubgroup.fixedField_finiteDimensional K H

local instance (H : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    IsGalois K (AbsoluteGaloisOpenNormalSubgroup.fixedField K H) :=
  AbsoluteGaloisOpenNormalSubgroup.fixedField_isGalois K H

/-- The fixed-cover Čech cocycle representing one transported finite-stage
continuous cocycle. -/
def finiteStageFixedCoverCocycle
    (D : ActionCompatibleFiniteQuotientFactorization a) :
    PresheafOfGroups.OneCocycle
      (finiteGaloisAffineGroupPresheaf K A)
      (fun _ : PUnit.{1} =>
        finiteGaloisCoverObject K
          (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup)) :=
  (finiteGaloisFixedCoverCocycleEquiv K
      (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup) A).symm
    ((galoisCechCocycleEquiv
      ((AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup) ≃ₐ[K]
        (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup))
      (AffineGaloisPoint K
        (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup) A)).symm
      (AlgebraicGeometry.GaloisH1.finiteStageDescendedCocycle K A D))

/-- At cocycle level, the canonical finite-Galois fpqc comparison sends the
explicit fixed-cover representative to the coordinate form of the
transported finite-stage cocycle. -/
@[simp] theorem finiteStageFixedCoverCocycle_cocycleEquiv
    (D : ActionCompatibleFiniteQuotientFactorization a) :
    (finiteGaloisFpqcGaloisCechComparison K
      (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup) A).cocycleEquiv
        (finiteStageFixedCoverCocycle K A D) =
      (galoisCechCocycleEquiv
        ((AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup) ≃ₐ[K]
          (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup))
        (AffineGaloisPoint K
          (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup) A)).symm
        (AlgebraicGeometry.GaloisH1.finiteStageDescendedCocycle K A D) := by
  change
    finiteGaloisFixedCoverCocycleEquiv K
        (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup) A
        (finiteStageFixedCoverCocycle K A D) = _
  unfold finiteStageFixedCoverCocycle
  rw [Equiv.apply_symm_apply]

/-- The canonical fixed-cover comparison sends the explicit finite-stage
Čech representative to the transported nonabelian cocycle class. -/
theorem finiteStageFixedCoverCocycle_comparison
    (D : ActionCompatibleFiniteQuotientFactorization a) :
    finiteGaloisCanonicalH1EquivNonabelian K
        (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup) A
        (finiteStageFixedCoverCocycle K A D).class =
      NonabelianH1.classOf
        (AlgebraicGeometry.GaloisH1.finiteStageDescendedCocycle K A D) := by
  change
    NonabelianH1.classOf
      (galoisCechCocycleEquiv _ _
        ((finiteGaloisFpqcGaloisCechComparison K
          (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup) A).cocycleEquiv
          (finiteStageFixedCoverCocycle K A D))) = _
  rw [finiteStageFixedCoverCocycle_cocycleEquiv,
    Equiv.apply_symm_apply]

/-- The global fpqc class represented by one action-compatible finite stage. -/
def finiteStageGlobalFpqcH1
    (D : ActionCompatibleFiniteQuotientFactorization a) :
    FpqcH1.{u, 0} (CommRingCat.of K) (CommRingCat.of A) :=
  FpqcH1.classOf (CommRingCat.of K) (CommRingCat.of A)
    (finiteGaloisFpqcCover K
      (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup))
    (finiteStageFixedCoverCocycle K A D).class

/-- The explicit finite-stage global class agrees with the canonical
finite-Galois-to-global map applied to the transported cocycle class. -/
theorem finiteStageGlobalFpqcH1_eq_finiteGaloisToGlobal
    (D : ActionCompatibleFiniteQuotientFactorization a) :
    finiteStageGlobalFpqcH1 K A D =
      finiteGaloisToGlobalFpqcH1 K
        (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup) A
        (NonabelianH1.classOf
          (AlgebraicGeometry.GaloisH1.finiteStageDescendedCocycle K A D)) := by
  unfold finiteStageGlobalFpqcH1 finiteGaloisToGlobalFpqcH1
  congr 1

end

end RiemannResearch.GaloisCohomology
