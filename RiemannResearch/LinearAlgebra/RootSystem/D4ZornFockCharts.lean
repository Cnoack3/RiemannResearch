/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.LinearAlgebra.RootSystem.D4SplitFockFaithfulness
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornSpinComparison

/-!
# Explicit split-vector and exterior-Fock charts for Zorn triality

This module supplies concrete eight-coordinate charts on all three members of
the split D4 representation family.  The vector chart is an explicit
isometry from the hyperbolic space U* × U to the Zorn norm.  The two
half-spin charts use the exterior basis indexed by the eight even,
respectively odd, subsets of Fin 4.

The exterior-Fock realization follows the comparison used in
Alsaody--Gille, *Isotopes of Octonion Algebras, G2-Torsors and Triality*,
Proposition 3.10 and Theorem 3.12:
<https://arxiv.org/abs/1704.05229>.  The exact signed subset ordering below
is the coordinate convention used by the present Zorn formulas.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

open CliffordAlgebra
open RiemannResearch.LinearAlgebra
open RiemannResearch.LinearAlgebra.CliffordEven

universe u

noncomputable section

variable (K : Type u) [Field K]

/-! ## The vector chart -/

/-- The ith standard coordinate vector of K⁴. -/
def splitZornCoordinateVector (i : Fin 4) : Fin 4 → K :=
  Pi.single i 1

/-- Forward coordinates from the split hyperbolic vector module to the Zorn
octonion module. -/
def splitVectorToZornLinear :
    SplitD4Space K →ₗ[K] Zorn.Octonion K where
  toFun p := ![
    p.2 0, p.2 1, p.2 2, p.2 3,
    -p.1 (splitZornCoordinateVector K 1),
    -p.1 (splitZornCoordinateVector K 2),
    -p.1 (splitZornCoordinateVector K 3),
    p.1 (splitZornCoordinateVector K 0)]
  map_add' p q := by
    ext i
    fin_cases i <;> simp <;> abel
  map_smul' a p := by
    ext i
    fin_cases i <;> simp

/-- Inverse coordinates from a Zorn octonion to the split hyperbolic vector
module. -/
def zornToSplitVectorLinear :
    Zorn.Octonion K →ₗ[K] SplitD4Space K where
  toFun x :=
    ( { toFun := fun v =>
          x 7 * v 0 - x 4 * v 1 - x 5 * v 2 - x 6 * v 3
        map_add' := by
          intros
          simp
          ring
        map_smul' := by
          intros
          simp
          ring },
      ![x 0, x 1, x 2, x 3] )
  map_add' x y := by
    apply Prod.ext
    · apply LinearMap.ext
      intro v
      simp
      ring
    · ext i
      fin_cases i <;> simp
  map_smul' a x := by
    apply Prod.ext
    · apply LinearMap.ext
      intro v
      simp
      ring
    · ext i
      fin_cases i <;> simp

theorem zornToSplitVectorLinear_comp_splitVectorToZornLinear :
    (zornToSplitVectorLinear K).comp (splitVectorToZornLinear K) =
      LinearMap.id := by
  apply LinearMap.ext
  intro p
  apply Prod.ext
  · apply (Pi.basisFun K (Fin 4)).ext
    intro i
    fin_cases i <;>
      simp [zornToSplitVectorLinear, splitVectorToZornLinear,
        splitZornCoordinateVector]
  · ext i
    fin_cases i <;>
      simp [zornToSplitVectorLinear, splitVectorToZornLinear]

theorem splitVectorToZornLinear_comp_zornToSplitVectorLinear :
    (splitVectorToZornLinear K).comp (zornToSplitVectorLinear K) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  ext i
  fin_cases i <;>
    simp [zornToSplitVectorLinear, splitVectorToZornLinear,
      splitZornCoordinateVector]

/-- The explicit vector-representation chart in Zorn coordinates. -/
def splitVectorZornEquiv :
    SplitD4Space K ≃ₗ[K] Zorn.Octonion K :=
  LinearEquiv.ofLinear
    (splitVectorToZornLinear K)
    (zornToSplitVectorLinear K)
    (splitVectorToZornLinear_comp_zornToSplitVectorLinear K)
    (zornToSplitVectorLinear_comp_splitVectorToZornLinear K)

@[simp] theorem splitVectorZornEquiv_apply (p : SplitD4Space K) :
    splitVectorZornEquiv K p = splitVectorToZornLinear K p :=
  rfl

/-- The vector chart identifies the split hyperbolic quadratic form with the
Zorn norm, coefficient by coefficient. -/
theorem splitVectorZornEquiv_normForm (p : SplitD4Space K) :
    Zorn.normForm K (splitVectorZornEquiv K p) =
      splitD4Form K p := by
  have hleft := LinearMap.congr_fun
    (zornToSplitVectorLinear_comp_splitVectorToZornLinear K) p
  have hp0 := congrArg
    (fun q : SplitD4Space K => q.1 p.2) hleft
  dsimp [zornToSplitVectorLinear, splitVectorToZornLinear] at hp0
  have hp :
      p.1 (splitZornCoordinateVector K 0) * p.2 0 +
          p.1 (splitZornCoordinateVector K 1) * p.2 1 +
          p.1 (splitZornCoordinateVector K 2) * p.2 2 +
          p.1 (splitZornCoordinateVector K 3) * p.2 3 =
        p.1 p.2 := by
    simpa [sub_neg_eq_add] using hp0
  simp only [splitVectorZornEquiv_apply, Zorn.normForm_apply,
    Zorn.norm, splitD4Form, QuadraticForm.dualProd_apply]
  change
    p.2 0 * p.1 (splitZornCoordinateVector K 0) -
          p.2 1 * (-p.1 (splitZornCoordinateVector K 1)) -
          p.2 2 * (-p.1 (splitZornCoordinateVector K 2)) -
          p.2 3 * (-p.1 (splitZornCoordinateVector K 3)) =
        p.1 p.2
  rw [← hp]
  ring

/-! ## Parity bases of the exterior-Fock modules -/

/-- An exterior monomial of degree n has parity n modulo two in the zero-form
Clifford grading. -/
theorem splitFockExteriorMulti_mem_parity :
    ∀ (n : ℕ) (v : Fin n → (Fin 4 → K)),
      ExteriorAlgebra.ιMulti K n v ∈
        evenOdd (0 : QuadraticForm K (Fin 4 → K)) (n : ZMod 2) := by
  intro n
  induction n with
  | zero =>
      intro v
      rw [ExteriorAlgebra.ιMulti_zero_apply]
      exact Submodule.one_le.mp (one_le_evenOdd_zero _)
  | succ n ih =>
      intro v
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      have hhead :
          ExteriorAlgebra.ι K (v 0) ∈
            evenOdd (0 : QuadraticForm K (Fin 4 → K)) 1 :=
        ι_mem_evenOdd_one _ _
      have htail := ih (Matrix.vecTail v)
      have hmul := Submodule.mul_le.mp
        (evenOdd_mul_le
          (0 : QuadraticForm K (Fin 4 → K)) 1 (n : ZMod 2))
        _ hhead _ htail
      simpa [Nat.cast_succ, add_comm] using hmul

/-- Parity of a standard exterior-basis monomial. -/
theorem splitFockExteriorBasis_mem_parity
    (s : Finset (Fin 4)) :
    (Pi.basisFun K (Fin 4)).ExteriorAlgebra s ∈
      evenOdd (0 : QuadraticForm K (Fin 4 → K))
        (s.card : ZMod 2) := by
  rw [ExteriorAlgebra.basis_apply_ofCard
    (Pi.basisFun K (Fin 4)) rfl]
  exact splitFockExteriorMulti_mem_parity K s.card _

/-- Ordering of the eight even subsets.  Complementary subsets occupy
coordinates (0,7), (1,4), (2,5), and (3,6). -/
def splitFockEvenSubset : Fin 8 → Finset (Fin 4) := ![
  ∅, {0, 1}, {0, 2}, {0, 3},
  {2, 3}, {1, 3}, {1, 2}, Finset.univ]

theorem splitFockEvenSubset_injective :
    Function.Injective splitFockEvenSubset := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

@[simp] theorem splitFockEvenSubset_card_mod_two (i : Fin 8) :
    ((splitFockEvenSubset i).card : ZMod 2) = 0 := by
  fin_cases i <;> decide

/-- Ordered unsigned exterior monomials in the positive half-spin module. -/
def splitFockEvenBasisVector (i : Fin 8) :
    SplitFockEven K :=
  ⟨(Pi.basisFun K (Fin 4)).ExteriorAlgebra (splitFockEvenSubset i),
    by
      have h := splitFockExteriorBasis_mem_parity K
        (splitFockEvenSubset i)
      simpa using h⟩

theorem splitFockEvenBasisVector_linearIndependent :
    LinearIndependent K (splitFockEvenBasisVector K) := by
  apply LinearIndependent.of_comp
    (evenOdd (0 : QuadraticForm K (Fin 4 → K)) 0).subtype
  change LinearIndependent K
    (fun i =>
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra
        (splitFockEvenSubset i))
  exact
    ((Pi.basisFun K (Fin 4)).ExteriorAlgebra.linearIndependent.comp
      splitFockEvenSubset splitFockEvenSubset_injective)

/-- Ordering of the odd subsets is inverse to the desired Zorn coordinate
assignment: 123, 1, 2, 3, 023, 013, 012, 0. -/
def splitFockOddSubset : Fin 8 → Finset (Fin 4) := ![
  {1, 2, 3}, {1}, {2}, {3},
  {0, 2, 3}, {0, 1, 3}, {0, 1, 2}, {0}]

theorem splitFockOddSubset_injective :
    Function.Injective splitFockOddSubset := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

@[simp] theorem splitFockOddSubset_card_mod_two (i : Fin 8) :
    ((splitFockOddSubset i).card : ZMod 2) = 1 := by
  fin_cases i <;> decide

/-- Ordered unsigned exterior monomials in the negative half-spin module. -/
def splitFockOddBasisVector (i : Fin 8) :
    SplitFockOdd K :=
  ⟨(Pi.basisFun K (Fin 4)).ExteriorAlgebra (splitFockOddSubset i),
    by
      have h := splitFockExteriorBasis_mem_parity K
        (splitFockOddSubset i)
      simpa using h⟩

theorem splitFockOddBasisVector_linearIndependent :
    LinearIndependent K (splitFockOddBasisVector K) := by
  apply LinearIndependent.of_comp
    (evenOdd (0 : QuadraticForm K (Fin 4 → K)) 1).subtype
  change LinearIndependent K
    (fun i =>
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra
        (splitFockOddSubset i))
  exact
    ((Pi.basisFun K (Fin 4)).ExteriorAlgebra.linearIndependent.comp
      splitFockOddSubset splitFockOddSubset_injective)

local instance splitZornFullFockFinite :
    Module.Finite K (SplitFockSpace K) :=
  Module.Finite.of_basis
    (Pi.basisFun K (Fin 4)).ExteriorAlgebra

local instance splitZornEvenFockFinite :
    Module.Finite K (SplitFockEven K) :=
  Module.Finite.of_injective
    (evenOdd (0 : QuadraticForm K (Fin 4 → K)) 0).subtype
    (evenOdd
      (0 : QuadraticForm K (Fin 4 → K)) 0).injective_subtype

local instance splitZornOddFockFinite :
    Module.Finite K (SplitFockOdd K) :=
  Module.Finite.of_injective
    (evenOdd (0 : QuadraticForm K (Fin 4 → K)) 1).subtype
    (evenOdd
      (0 : QuadraticForm K (Fin 4 → K)) 1).injective_subtype

/-- The explicit exterior-monomial basis of positive half-spin. -/
def splitFockEvenBasis :
    Module.Basis (Fin 8) K (SplitFockEven K) :=
  Module.Basis.mk
    (splitFockEvenBasisVector_linearIndependent K) (by
      have hrank :=
        finrank_span_eq_card
          (splitFockEvenBasisVector_linearIndependent K)
      rw [Fintype.card_fin] at hrank
      have hfin :
          Module.finrank K
              ↥(Submodule.span K
                (Set.range (splitFockEvenBasisVector K))) =
            Module.finrank K (SplitFockEven K) := by
        rw [hrank, splitHalfSpinPlus_finrank K]
      rw [Submodule.eq_top_of_finrank_eq hfin])

/-- The explicit exterior-monomial basis of negative half-spin. -/
def splitFockOddBasis :
    Module.Basis (Fin 8) K (SplitFockOdd K) :=
  Module.Basis.mk
    (splitFockOddBasisVector_linearIndependent K) (by
      have hrank :=
        finrank_span_eq_card
          (splitFockOddBasisVector_linearIndependent K)
      rw [Fintype.card_fin] at hrank
      have hfin :
          Module.finrank K
              ↥(Submodule.span K
                (Set.range (splitFockOddBasisVector K))) =
            Module.finrank K (SplitFockOdd K) := by
        rw [hrank, splitHalfSpinMinus_finrank K]
      rw [Submodule.eq_top_of_finrank_eq hfin])

/-- Sign correction for the positive half-spin coordinate 13 ↦ -e5. -/
def splitFockEvenZornSignEquiv :
    Zorn.Octonion K ≃ₗ[K] Zorn.Octonion K where
  toFun x := ![x 0, x 1, x 2, x 3, x 4, -x 5, x 6, x 7]
  invFun x := ![x 0, x 1, x 2, x 3, x 4, -x 5, x 6, x 7]
  left_inv x := by
    ext i
    fin_cases i <;> simp
  right_inv x := by
    ext i
    fin_cases i <;> simp
  map_add' x y := by
    ext i
    fin_cases i <;> simp [add_comm]
  map_smul' a x := by
    ext i
    fin_cases i <;> simp

/-- Sign correction for odd coordinates 1, 2, 3, 4, and 6. -/
def splitFockOddZornSignEquiv :
    Zorn.Octonion K ≃ₗ[K] Zorn.Octonion K where
  toFun x := ![x 0, -x 1, -x 2, -x 3, -x 4, x 5, -x 6, x 7]
  invFun x := ![x 0, -x 1, -x 2, -x 3, -x 4, x 5, -x 6, x 7]
  left_inv x := by
    ext i
    fin_cases i <;> simp
  right_inv x := by
    ext i
    fin_cases i <;> simp
  map_add' x y := by
    ext i
    fin_cases i <;> simp [add_comm]
  map_smul' a x := by
    ext i
    fin_cases i <;> simp

/-- Positive half-spin in the signed eight Zorn coordinates. -/
def splitFockEvenZornEquiv :
    SplitFockEven K ≃ₗ[K] Zorn.Octonion K :=
  (splitFockEvenBasis K).equivFun.trans
    (splitFockEvenZornSignEquiv K)

/-- Negative half-spin in the signed eight Zorn coordinates. -/
def splitFockOddZornEquiv :
    SplitFockOdd K ≃ₗ[K] Zorn.Octonion K :=
  (splitFockOddBasis K).equivFun.trans
    (splitFockOddZornSignEquiv K)

@[simp] theorem splitFockEvenZornEquiv_basisVector (i : Fin 8) :
    splitFockEvenZornEquiv K (splitFockEvenBasisVector K i) =
      splitFockEvenZornSignEquiv K (Pi.single i 1) := by
  simp only [splitFockEvenZornEquiv, LinearEquiv.trans_apply]
  apply congrArg (splitFockEvenZornSignEquiv K)
  change
    (splitFockEvenBasis K).equivFun
        (splitFockEvenBasisVector K i) =
      Pi.single i 1
  rw [show splitFockEvenBasisVector K i =
      splitFockEvenBasis K i by
    simp [splitFockEvenBasis]]
  ext j
  by_cases hij : i = j
  · subst j
    simp [Module.Basis.equivFun_self, Pi.single]
  · simp [Module.Basis.equivFun_self, Pi.single, hij, Ne.symm hij]

@[simp] theorem splitFockOddZornEquiv_basisVector (i : Fin 8) :
    splitFockOddZornEquiv K (splitFockOddBasisVector K i) =
      splitFockOddZornSignEquiv K (Pi.single i 1) := by
  simp only [splitFockOddZornEquiv, LinearEquiv.trans_apply]
  apply congrArg (splitFockOddZornSignEquiv K)
  change
    (splitFockOddBasis K).equivFun
        (splitFockOddBasisVector K i) =
      Pi.single i 1
  rw [show splitFockOddBasisVector K i =
      splitFockOddBasis K i by
    simp [splitFockOddBasis]]
  ext j
  by_cases hij : i = j
  · subst j
    simp [Module.Basis.equivFun_self, Pi.single]
  · simp [Module.Basis.equivFun_self, Pi.single, hij, Ne.symm hij]

variable [Invertible (2 : K)]

/-- One explicit simultaneous Zorn chart on the vector and two Fock
half-spin representation modules. -/
def splitZornFockChart : SplitZornChart K
  | .vector => splitVectorZornEquiv K
  | .halfSpinPlus => splitFockEvenZornEquiv K
  | .halfSpinMinus => splitFockOddZornEquiv K

/-- The vector component of the charted split triality tuple preserves the
Zorn norm. -/
theorem splitZornFockChart_vector_preservesNorm
    (g : CliffordEven.SpinPoint (splitD4Form K))
    (x : Zorn.Octonion K) :
    Zorn.normForm K
        (splitTrialityLinearTupleHom K (Zorn.Octonion K)
          (splitZornFockChart K) g .vector x) =
      Zorn.normForm K x := by
  simp only [splitTrialityLinearTupleHom, chartedRepresentation,
    representationLinearEquiv, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearEquiv.trans_apply]
  change
    Zorn.normForm K
        (splitVectorZornEquiv K
          (CliffordEven.spinVectorRepresentation (splitD4Form K) g
            ((splitVectorZornEquiv K).symm x))) =
      Zorn.normForm K x
  rw [splitVectorZornEquiv_normForm,
    CliffordEven.spinVectorRepresentation_preserves_form]
  rw [← splitVectorZornEquiv_normForm K
    ((splitVectorZornEquiv K).symm x)]
  simp

end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality
