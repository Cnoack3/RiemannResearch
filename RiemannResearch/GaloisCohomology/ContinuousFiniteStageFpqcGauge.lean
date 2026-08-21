/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.ContinuousFiniteStageFpqcNaturality

/-!
# Gauge invariance of continuous finite-stage fpqc classes

This module proves that the global fpqc class constructed from a continuous
absolute-Galois cocycle is invariant under gauge equivalence, not only under
changing the chosen finite quotient. It therefore descends to a pointed map
from continuous nonabelian Galois `H¹` to global fpqc Čech `H¹`.

Source for the continuous nonabelian cohomology construction and its
finite-stage interpretation: J.-P. Serre, *Galois Cohomology*, Chapter I, §5.
-/

namespace RiemannResearch.GaloisCohomology

open RiemannResearch.AlgebraicGeometry
open ContinuousNonabelianCocycle
open ContinuousNonabelianCocycle.ActionCompatibleFiniteQuotientFactorization

universe u

noncomputable section

variable (K A : Type u) [Field K] [PerfectField K]
variable [CommRing A] [HopfAlgebra K A]

local instance (H : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    FiniteDimensional K
      (AbsoluteGaloisOpenNormalSubgroup.fixedField K H) :=
  AbsoluteGaloisOpenNormalSubgroup.fixedField_finiteDimensional K H

local instance (H : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    IsGalois K (AbsoluteGaloisOpenNormalSubgroup.fixedField K H) :=
  AbsoluteGaloisOpenNormalSubgroup.fixedField_isGalois K H

variable [Algebra.FiniteType K A]
variable {a b : ContinuousNonabelianCocycle
  (Field.absoluteGaloisGroup K) (AlgebraicGroupGeometricPoints K A)}

/-- Gauge-equivalent continuous cocycles determine the same global fpqc class,
even when their initial finite factorizations are unrelated.

The proof refines both kernels to an open normal subgroup that also fixes the
chosen gauge element, then uses the explicit-subgroup gauge comparison. -/
theorem finiteStageGlobalFpqcH1_eq_of_cohomologous
    (hab : a.Cohomologous b)
    (D : ActionCompatibleFiniteQuotientFactorization a)
    (E : ActionCompatibleFiniteQuotientFactorization b) :
    finiteStageGlobalFpqcH1 K A D =
      finiteStageGlobalFpqcH1 K A E := by
  obtain ⟨g, hbg⟩ := hab
  let U : Set (Field.absoluteGaloisGroup K) :=
    ((D.subgroup : Set (Field.absoluteGaloisGroup K)) ∩
      (E.subgroup : Set (Field.absoluteGaloisGroup K))) ∩
      (MulAction.stabilizer (Field.absoluteGaloisGroup K) g :
        Set (Field.absoluteGaloisGroup K))
  have hUOpen : IsOpen U := by
    exact
      (D.subgroup.toOpenSubgroup.isOpen.inter
        E.subgroup.toOpenSubgroup.isOpen).inter
        (stabilizer_isOpen (Field.absoluteGaloisGroup K) g)
  have hOneU : (1 : Field.absoluteGaloisGroup K) ∈ U := by
    simp [U]
  obtain ⟨H, hHU⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUOpen hOneU
  have hHD : H ≤ D.subgroup := by
    intro σ hσ
    exact (hHU hσ).1.1
  have hHE : H ≤ E.subgroup := by
    intro σ hσ
    exact (hHU hσ).1.2
  have hg : ∀ h : H, h.1 • g = g := by
    intro h
    exact MulAction.mem_stabilizer_iff.mp (hHU h.2).2
  let DH := D.pullbackToSubgroup H hHD
  let EH := E.pullbackToSubgroup H hHE
  calc
    finiteStageGlobalFpqcH1 K A D =
        finiteStageGlobalFpqcH1 K A DH :=
      Refinement.finiteStageGlobalFpqcH1_eq_of_refinement K A ⟨hHD⟩
    _ = finiteStageGlobalFpqcH1AtSubgroup K A a H
        DH.trivial_on DH.fixes_range := by
      symm
      exact finiteStageGlobalFpqcH1AtSubgroup_eq K A DH
    _ = finiteStageGlobalFpqcH1AtSubgroup K A b H
        EH.trivial_on EH.fixes_range :=
      finiteStageGlobalFpqcH1AtSubgroup_eq_of_gauge K A H
        DH.trivial_on DH.fixes_range EH.trivial_on EH.fixes_range
        g hbg hg
    _ = finiteStageGlobalFpqcH1 K A EH :=
      finiteStageGlobalFpqcH1AtSubgroup_eq K A EH
    _ = finiteStageGlobalFpqcH1 K A E :=
      (Refinement.finiteStageGlobalFpqcH1_eq_of_refinement K A ⟨hHE⟩).symm

/-- A canonical choice of action-compatible finite factorization, used only to
define the quotient map. Independence theorems remove all dependence on this
choice from its observable behavior. -/
noncomputable def chosenActionCompatibleFiniteQuotientFactorization
    (a : ContinuousNonabelianCocycle
      (Field.absoluteGaloisGroup K) (AlgebraicGroupGeometricPoints K A)) :
    ActionCompatibleFiniteQuotientFactorization a :=
  Classical.choice (exists_actionCompatibleFiniteQuotientFactorization a)

/-- The finite-stage construction descends to continuous nonabelian Galois
`H¹`. -/
noncomputable def continuousGaloisToGlobalFpqcH1 :
    ContinuousNonabelianH1 (Field.absoluteGaloisGroup K)
        (AlgebraicGroupGeometricPoints K A) →
      FpqcH1.{u, 0} (CommRingCat.of K) (CommRingCat.of A) :=
  Quotient.lift
    (fun a => finiteStageGlobalFpqcH1 K A
      (chosenActionCompatibleFiniteQuotientFactorization K A a))
    (by
      intro a b hab
      exact finiteStageGlobalFpqcH1_eq_of_cohomologous K A hab
        (chosenActionCompatibleFiniteQuotientFactorization K A a)
        (chosenActionCompatibleFiniteQuotientFactorization K A b))

/-- Evaluation of the continuous comparison map on a cocycle class. -/
@[simp] theorem continuousGaloisToGlobalFpqcH1_classOf
    (a : ContinuousNonabelianCocycle
      (Field.absoluteGaloisGroup K) (AlgebraicGroupGeometricPoints K A)) :
    continuousGaloisToGlobalFpqcH1 K A
        (ContinuousNonabelianH1.classOf a) =
      finiteStageGlobalFpqcH1 K A
        (chosenActionCompatibleFiniteQuotientFactorization K A a) := rfl

/-- Evaluation may use any action-compatible finite factorization. -/
theorem continuousGaloisToGlobalFpqcH1_classOf_eq
    (a : ContinuousNonabelianCocycle
      (Field.absoluteGaloisGroup K) (AlgebraicGroupGeometricPoints K A))
    (D : ActionCompatibleFiniteQuotientFactorization a) :
    continuousGaloisToGlobalFpqcH1 K A
        (ContinuousNonabelianH1.classOf a) =
      finiteStageGlobalFpqcH1 K A D := by
  rw [continuousGaloisToGlobalFpqcH1_classOf]
  exact finiteStageGlobalFpqcH1_independent K A _ _

omit [Algebra.FiniteType K A] in
/-- Every finite stage of the trivial continuous cocycle has neutral global
fpqc class. -/
theorem finiteStageGlobalFpqcH1_trivial
    (D : ActionCompatibleFiniteQuotientFactorization
      (ContinuousNonabelianCocycle.trivial :
        ContinuousNonabelianCocycle (Field.absoluteGaloisGroup K)
          (AlgebraicGroupGeometricPoints K A))) :
    finiteStageGlobalFpqcH1 K A D =
      FpqcH1.neutral (CommRingCat.of K) (CommRingCat.of A) := by
  have hc :
      AlgebraicGeometry.GaloisH1.finiteStageDescendedCocycle K A D =
        (NonabelianCocycle.trivial :
          NonabelianCocycle
            ((AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup) ≃ₐ[K]
              (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup))
            (AffineGaloisPoint K
              (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup) A)) := by
    apply NonabelianCocycle.ext
    intro τ
    let q :=
      (AbsoluteGaloisOpenNormalSubgroup.quotientEquivGaloisGroup
        K D.subgroup).symm τ
    change AlgebraicGeometry.GaloisH1.finiteStageCoefficientEquiv K A D
      (D.descendedCocycle q) = 1
    refine Quotient.inductionOn' q ?_
    intro σ
    have hx : D.descendedCocycle (QuotientGroup.mk σ) = 1 := by
      apply Subtype.ext
      change ((D.descendedCocycle (QuotientGroup.mk σ) :
        D.FixedCoefficientGroup) : AlgebraicGroupGeometricPoints K A) = 1
      exact D.coe_descendedCocycle_mk σ
    rw [hx]
    exact map_one
      (AlgebraicGeometry.GaloisH1.finiteStageCoefficientEquiv K A D)
  rw [finiteStageGlobalFpqcH1_eq_finiteGaloisToGlobal, hc]
  exact finiteGaloisToGlobalFpqcH1_neutral K
    (AbsoluteGaloisOpenNormalSubgroup.fixedField K D.subgroup) A

/-- The continuous comparison map preserves the distinguished neutral
class. -/
@[simp] theorem continuousGaloisToGlobalFpqcH1_neutral :
    continuousGaloisToGlobalFpqcH1 K A
        (ContinuousNonabelianH1.neutral :
          ContinuousNonabelianH1 (Field.absoluteGaloisGroup K)
            (AlgebraicGroupGeometricPoints K A)) =
      FpqcH1.neutral (CommRingCat.of K) (CommRingCat.of A) := by
  change continuousGaloisToGlobalFpqcH1 K A
      (ContinuousNonabelianH1.classOf
        (ContinuousNonabelianCocycle.trivial :
          ContinuousNonabelianCocycle (Field.absoluteGaloisGroup K)
            (AlgebraicGroupGeometricPoints K A))) = _
  rw [continuousGaloisToGlobalFpqcH1_classOf]
  exact finiteStageGlobalFpqcH1_trivial K A _

end

end RiemannResearch.GaloisCohomology
