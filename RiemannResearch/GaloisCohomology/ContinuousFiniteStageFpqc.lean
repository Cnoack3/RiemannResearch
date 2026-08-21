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

local instance (H : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    (H : Subgroup (Field.absoluteGaloisGroup K)).Normal :=
  H.isNormal'

local instance (H : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    MulDistribMulAction
      (Field.absoluteGaloisGroup K ⧸
        (H : Subgroup (Field.absoluteGaloisGroup K)))
      (FixedPoints.subgroup H (AlgebraicGroupGeometricPoints K A)) :=
  MulDistribMulAction.instQuotientSubgroupSubtypeMemSubgroup

/-- The explicit fixed-cover representative attached directly to one open
normal subgroup and descent proofs for a continuous cocycle. -/
def finiteStageFixedCoverCocycleAtSubgroup
    (a : ContinuousNonabelianCocycle
      (Field.absoluteGaloisGroup K) (AlgebraicGroupGeometricPoints K A))
    (H : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (htriv : ∀ h : H, a h.1 = 1)
    (hfix : ∀ h : H, ∀ σ : Field.absoluteGaloisGroup K,
      h.1 • a σ = a σ) :
    PresheafOfGroups.OneCocycle (finiteGaloisAffineGroupPresheaf K A)
      (fun _ : PUnit.{1} =>
        finiteGaloisCoverObject K
          (AbsoluteGaloisOpenNormalSubgroup.fixedField K H)) :=
  (finiteGaloisFixedCoverCocycleEquiv K
      (AbsoluteGaloisOpenNormalSubgroup.fixedField K H) A).symm
    ((galoisCechCocycleEquiv
      ((AbsoluteGaloisOpenNormalSubgroup.fixedField K H) ≃ₐ[K]
        (AbsoluteGaloisOpenNormalSubgroup.fixedField K H))
      (AffineGaloisPoint K
        (AbsoluteGaloisOpenNormalSubgroup.fixedField K H) A)).symm
      (AlgebraicGeometry.GaloisH1.finiteStageDescendedCocycleAtSubgroup
        K A a H htriv hfix))

/-- The fixed-cover comparison sends the explicit-subgroup representative to
the corresponding transported nonabelian cocycle class. -/
theorem finiteStageFixedCoverCocycleAtSubgroup_comparison
    (a : ContinuousNonabelianCocycle
      (Field.absoluteGaloisGroup K) (AlgebraicGroupGeometricPoints K A))
    (H : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (htriv : ∀ h : H, a h.1 = 1)
    (hfix : ∀ h : H, ∀ σ : Field.absoluteGaloisGroup K,
      h.1 • a σ = a σ) :
    finiteGaloisCanonicalH1EquivNonabelian K
        (AbsoluteGaloisOpenNormalSubgroup.fixedField K H) A
        (finiteStageFixedCoverCocycleAtSubgroup
          K A a H htriv hfix).class =
      NonabelianH1.classOf
        (AlgebraicGeometry.GaloisH1.finiteStageDescendedCocycleAtSubgroup
          K A a H htriv hfix) := by
  change NonabelianH1.classOf
    (galoisCechCocycleEquiv _ _
      ((finiteGaloisFpqcGaloisCechComparison K
        (AbsoluteGaloisOpenNormalSubgroup.fixedField K H) A).cocycleEquiv
        (finiteStageFixedCoverCocycleAtSubgroup
          K A a H htriv hfix))) = _
  change NonabelianH1.classOf
    (galoisCechCocycleEquiv _ _
      ((finiteGaloisFixedCoverCocycleEquiv K
        (AbsoluteGaloisOpenNormalSubgroup.fixedField K H) A)
        (finiteStageFixedCoverCocycleAtSubgroup
          K A a H htriv hfix))) = _
  unfold finiteStageFixedCoverCocycleAtSubgroup
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The explicit-subgroup fixed-cover representative specializes to the one
stored by an action-compatible factorization. -/
theorem finiteStageFixedCoverCocycleAtSubgroup_eq
    (D : ActionCompatibleFiniteQuotientFactorization a) :
    finiteStageFixedCoverCocycleAtSubgroup K A a D.subgroup
        D.trivial_on D.fixes_range =
      finiteStageFixedCoverCocycle K A D := by
  unfold finiteStageFixedCoverCocycleAtSubgroup
    finiteStageFixedCoverCocycle
  rw [AlgebraicGeometry.GaloisH1.finiteStageDescendedCocycleAtSubgroup_eq]

/-- The global fpqc class attached directly to an explicit open normal
subgroup and descent proofs. -/
def finiteStageGlobalFpqcH1AtSubgroup
    (a : ContinuousNonabelianCocycle
      (Field.absoluteGaloisGroup K) (AlgebraicGroupGeometricPoints K A))
    (H : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (htriv : ∀ h : H, a h.1 = 1)
    (hfix : ∀ h : H, ∀ σ : Field.absoluteGaloisGroup K,
      h.1 • a σ = a σ) :
    FpqcH1.{u, 0} (CommRingCat.of K) (CommRingCat.of A) :=
  FpqcH1.classOf (CommRingCat.of K) (CommRingCat.of A)
    (finiteGaloisFpqcCover K
      (AbsoluteGaloisOpenNormalSubgroup.fixedField K H))
    (finiteStageFixedCoverCocycleAtSubgroup K A a H htriv hfix).class

/-- The explicit-subgroup global class specializes to the class stored by a
factorization. -/
theorem finiteStageGlobalFpqcH1AtSubgroup_eq
    (D : ActionCompatibleFiniteQuotientFactorization a) :
    finiteStageGlobalFpqcH1AtSubgroup K A a D.subgroup
        D.trivial_on D.fixes_range =
      finiteStageGlobalFpqcH1 K A D := by
  unfold finiteStageGlobalFpqcH1AtSubgroup finiteStageGlobalFpqcH1
  rw [finiteStageFixedCoverCocycleAtSubgroup_eq]

/-- A gauge fixed by the explicit subgroup descends the gauge equivalence to
the transported finite-Galois cocycles. -/
theorem finiteStageDescendedCocycleAtSubgroup_cohomologous_of_gauge
    {a b : ContinuousNonabelianCocycle
      (Field.absoluteGaloisGroup K) (AlgebraicGroupGeometricPoints K A)}
    (H : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (htrivA : ∀ h : H, a h.1 = 1)
    (hfixA : ∀ h : H, ∀ σ : Field.absoluteGaloisGroup K,
      h.1 • a σ = a σ)
    (htrivB : ∀ h : H, b h.1 = 1)
    (hfixB : ∀ h : H, ∀ σ : Field.absoluteGaloisGroup K,
      h.1 • b σ = b σ)
    (g : AlgebraicGroupGeometricPoints K A)
    (hab : b.1 = a.1.gauge g)
    (hg : ∀ h : H, h.1 • g = g) :
    (AlgebraicGeometry.GaloisH1.finiteStageDescendedCocycleAtSubgroup
      K A a H htrivA hfixA).Cohomologous
    (AlgebraicGeometry.GaloisH1.finiteStageDescendedCocycleAtSubgroup
      K A b H htrivB hfixB) := by
  let gH : FixedPoints.subgroup H (AlgebraicGroupGeometricPoints K A) :=
    ⟨g, (FixedPoints.mem_subgroup H _ g).2 hg⟩
  let cA := descendedCocycleAtSubgroup a H htrivA hfixA
  let cB := descendedCocycleAtSubgroup b H htrivB hfixB
  have hraw : cB = cA.gauge gH := by
    apply NonabelianCocycle.ext
    intro q
    refine Quotient.inductionOn' q ?_
    intro σ
    apply Subtype.ext
    change b σ = g⁻¹ * a σ * σ • g
    exact congrArg
      (fun w : NonabelianCocycle (Field.absoluteGaloisGroup K)
        (AlgebraicGroupGeometricPoints K A) => w σ) hab
  refine
    ⟨AlgebraicGeometry.GaloisH1.finiteStageCoefficientEquivAtSubgroup
      K A H gH, ?_⟩
  apply NonabelianCocycle.ext
  intro τ
  let eQ :=
    AbsoluteGaloisOpenNormalSubgroup.quotientEquivGaloisGroup K H
  let eG :=
    AlgebraicGeometry.GaloisH1.finiteStageCoefficientEquivAtSubgroup K A H
  let q := eQ.symm τ
  change eG (cB q) = (eG gH)⁻¹ * eG (cA q) * τ • eG gH
  rw [hraw]
  change eG (gH⁻¹ * cA q * q • gH) =
    (eG gH)⁻¹ * eG (cA q) * τ • eG gH
  rw [map_mul, map_mul, map_inv,
    AlgebraicGeometry.GaloisH1.finiteStageCoefficientEquivAtSubgroup_smul,
    show eQ q = τ by exact eQ.apply_symm_apply τ]

/-- Gauge-equivalent explicit-subgroup representatives determine the same
fixed-cover Čech class. -/
theorem finiteStageFixedCoverCocycleAtSubgroup_class_eq_of_gauge
    {a b : ContinuousNonabelianCocycle
      (Field.absoluteGaloisGroup K) (AlgebraicGroupGeometricPoints K A)}
    (H : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (htrivA : ∀ h : H, a h.1 = 1)
    (hfixA : ∀ h : H, ∀ σ : Field.absoluteGaloisGroup K,
      h.1 • a σ = a σ)
    (htrivB : ∀ h : H, b h.1 = 1)
    (hfixB : ∀ h : H, ∀ σ : Field.absoluteGaloisGroup K,
      h.1 • b σ = b σ)
    (g : AlgebraicGroupGeometricPoints K A)
    (hab : b.1 = a.1.gauge g)
    (hg : ∀ h : H, h.1 • g = g) :
    (finiteStageFixedCoverCocycleAtSubgroup
      K A a H htrivA hfixA).class =
      (finiteStageFixedCoverCocycleAtSubgroup
        K A b H htrivB hfixB).class := by
  apply
    (finiteGaloisCanonicalH1EquivNonabelian K
      (AbsoluteGaloisOpenNormalSubgroup.fixedField K H) A).injective
  rw [finiteStageFixedCoverCocycleAtSubgroup_comparison,
    finiteStageFixedCoverCocycleAtSubgroup_comparison]
  exact (NonabelianH1.classOf_eq_classOf_iff _ _).2
    (finiteStageDescendedCocycleAtSubgroup_cohomologous_of_gauge
      K A H htrivA hfixA htrivB hfixB g hab hg)

/-- Gauge-equivalent representatives descended over one explicit subgroup
determine the same global fpqc class. -/
theorem finiteStageGlobalFpqcH1AtSubgroup_eq_of_gauge
    {a b : ContinuousNonabelianCocycle
      (Field.absoluteGaloisGroup K) (AlgebraicGroupGeometricPoints K A)}
    (H : OpenNormalSubgroup (Field.absoluteGaloisGroup K))
    (htrivA : ∀ h : H, a h.1 = 1)
    (hfixA : ∀ h : H, ∀ σ : Field.absoluteGaloisGroup K,
      h.1 • a σ = a σ)
    (htrivB : ∀ h : H, b h.1 = 1)
    (hfixB : ∀ h : H, ∀ σ : Field.absoluteGaloisGroup K,
      h.1 • b σ = b σ)
    (g : AlgebraicGroupGeometricPoints K A)
    (hab : b.1 = a.1.gauge g)
    (hg : ∀ h : H, h.1 • g = g) :
    finiteStageGlobalFpqcH1AtSubgroup K A a H htrivA hfixA =
      finiteStageGlobalFpqcH1AtSubgroup K A b H htrivB hfixB := by
  unfold finiteStageGlobalFpqcH1AtSubgroup
  rw [finiteStageFixedCoverCocycleAtSubgroup_class_eq_of_gauge
    K A H htrivA hfixA htrivB hfixB g hab hg]

end

end RiemannResearch.GaloisCohomology
