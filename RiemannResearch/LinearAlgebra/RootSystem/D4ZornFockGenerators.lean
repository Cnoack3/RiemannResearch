/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.LinearAlgebra.RootSystem.D4ZornFockCharts

/-!
# Generator-level Fock/Zorn triality comparison

This module packages the parity-changing exterior-Fock generator and reduces
the two expected Zorn block identities to their exact finite tables on the
explicit vector and half-spin bases. Each remaining table has 8 by 8 entries;
no dimension argument or unspecified comparison map is used.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

open CliffordAlgebra
open RiemannResearch.LinearAlgebra
open RiemannResearch.LinearAlgebra.CliffordEven

universe u

noncomputable section

variable (K : Type u) [Field K]

namespace Zorn

/-- Left para-octonion multiplication as a linear map in the second input. -/
def paraMulLeftLinear (x : Octonion K) : Octonion K →ₗ[K] Octonion K where
  toFun y := paraMul K x y
  map_add' y z := by
    ext i
    fin_cases i <;> simp [paraMul, mul, conjugate] <;> ring
  map_smul' a y := by
    ext i
    fin_cases i <;> simp [paraMul, mul, conjugate] <;> ring

/-- Right para-octonion multiplication as a linear map in the first input. -/
def paraMulRightLinear (y : Octonion K) : Octonion K →ₗ[K] Octonion K where
  toFun x := paraMul K x y
  map_add' x z := by
    ext i
    fin_cases i <;> simp [paraMul, mul, conjugate] <;> ring
  map_smul' a x := by
    ext i
    fin_cases i <;> simp [paraMul, mul, conjugate] <;> ring

end Zorn

/-- The vector basis transported from the eight standard Zorn coordinates. -/
def splitVectorZornBasis : Module.Basis (Fin 8) K (SplitD4Space K) :=
  (Pi.basisFun K (Fin 8)).map (splitVectorZornEquiv K).symm

/-- The same vector basis in creation/annihilation coordinates. -/
def splitVectorZornBasisSource : Fin 8 → SplitD4Space K := ![
  (0, (Pi.basisFun K (Fin 4)) 0),
  (0, (Pi.basisFun K (Fin 4)) 1),
  (0, (Pi.basisFun K (Fin 4)) 2),
  (0, (Pi.basisFun K (Fin 4)) 3),
  (-(Pi.basisFun K (Fin 4)).dualBasis 1, 0),
  (-(Pi.basisFun K (Fin 4)).dualBasis 2, 0),
  (-(Pi.basisFun K (Fin 4)).dualBasis 3, 0),
  ((Pi.basisFun K (Fin 4)).dualBasis 0, 0)]

@[simp] theorem splitVectorZornBasis_eq_source (i : Fin 8) :
    splitVectorZornBasis K i = splitVectorZornBasisSource K i := by
  fin_cases i <;> apply Prod.ext
  all_goals first | apply LinearMap.ext; intro v | ext j; fin_cases j
  all_goals
    simp [splitVectorZornBasis, splitVectorZornBasisSource,
      splitVectorZornEquiv, zornToSplitVectorLinear,
      splitVectorToZornLinear, splitZornCoordinateVector]

@[simp] theorem splitVectorZornEquiv_basis (i : Fin 8) :
    splitVectorZornEquiv K (splitVectorZornBasis K i) =
      Pi.single i 1 := by
  simp [splitVectorZornBasis]

/-- The Fock Clifford generator restricted from even to odd exterior parity. -/
def splitFockGeneratorEvenToOdd (x : SplitD4Space K) :
    SplitFockEven K →ₗ[K] SplitFockOdd K :=
  (exteriorFockGenerator (K := K) (U := Fin 4 → K) x).restrict
    (fun _z hz => exteriorFockGenerator_mem_odd_of_mem_even x hz)

/-- The Fock Clifford generator restricted from odd to even exterior parity. -/
def splitFockGeneratorOddToEven (x : SplitD4Space K) :
    SplitFockOdd K →ₗ[K] SplitFockEven K :=
  (exteriorFockGenerator (K := K) (U := Fin 4 → K) x).restrict
    (fun _z hz => exteriorFockGenerator_mem_even_of_mem_odd x hz)

/-- Creation on an exterior basis monomial when the new index is absent. -/
theorem splitFock_creation_basis_eq_of_not_mem
    (i : Fin 4) (s : Finset (Fin 4)) (hi : i ∉ s) :
    ExteriorAlgebra.ι K ((Pi.basisFun K (Fin 4)) i) *
        (Pi.basisFun K (Fin 4)).ExteriorAlgebra s =
      splitFockEraseSign i (insert i s) •
        (Pi.basisFun K (Fin 4)).ExteriorAlgebra (insert i s) := by
  have h := splitFock_basis_singleton_mul_erase
    (K := K) i (insert i s) (Finset.mem_insert_self i s)
  rw [splitFock_basis_singleton] at h
  simpa [hi] using h

/-- The even-to-odd block at a fixed positive half-spinor is linear in the
split vector input. -/
def splitFockEvenGeneratorAt (s : SplitFockEven K) :
    SplitD4Space K →ₗ[K] Zorn.Octonion K where
  toFun x :=
    splitFockOddZornEquiv K (splitFockGeneratorEvenToOdd K x s)
  map_add' x y := by
    rw [← map_add]
    congr 1
    apply Subtype.ext
    exact LinearMap.congr_fun
      ((exteriorFockGenerator
        (K := K) (U := Fin 4 → K)).map_add x y) s.1
  map_smul' a x := by
    rw [← map_smul]
    congr 1
    apply Subtype.ext
    exact LinearMap.congr_fun
      ((exteriorFockGenerator
        (K := K) (U := Fin 4 → K)).map_smul a x) s.1

/-- The odd-to-even block at a fixed negative half-spinor is linear in the
split vector input. -/
def splitFockOddGeneratorAt (s : SplitFockOdd K) :
    SplitD4Space K →ₗ[K] Zorn.Octonion K where
  toFun x :=
    splitFockEvenZornEquiv K (splitFockGeneratorOddToEven K x s)
  map_add' x y := by
    rw [← map_add]
    congr 1
    apply Subtype.ext
    exact LinearMap.congr_fun
      ((exteriorFockGenerator
        (K := K) (U := Fin 4 → K)).map_add x y) s.1
  map_smul' a x := by
    rw [← map_smul]
    congr 1
    apply Subtype.ext
    exact LinearMap.congr_fun
      ((exteriorFockGenerator
        (K := K) (U := Fin 4 → K)).map_smul a x) s.1

/-- The full even-to-odd generator identity is equivalent to its exact
64-entry table on the explicit vector and positive-half-spin bases. -/
theorem splitFockGeneratorEvenToOdd_chart_iff_basis :
    (∀ (x : SplitD4Space K) (s : SplitFockEven K),
      splitFockOddZornEquiv K (splitFockGeneratorEvenToOdd K x s) =
        Zorn.paraMul K (splitVectorZornEquiv K x)
          (splitFockEvenZornEquiv K s)) ↔
    (∀ (i j : Fin 8),
      splitFockOddZornEquiv K
          (splitFockGeneratorEvenToOdd K
            (splitVectorZornBasis K i) (splitFockEvenBasis K j)) =
        Zorn.paraMul K
          (splitVectorZornEquiv K (splitVectorZornBasis K i))
          (splitFockEvenZornEquiv K (splitFockEvenBasis K j))) := by
  constructor
  · intro h i j
    exact h _ _
  · intro h x s
    let lhs : SplitFockEven K →ₗ[K] Zorn.Octonion K :=
      (splitFockOddZornEquiv K).toLinearMap.comp
        (splitFockGeneratorEvenToOdd K x)
    let rhs : SplitFockEven K →ₗ[K] Zorn.Octonion K :=
      (Zorn.paraMulLeftLinear K (splitVectorZornEquiv K x)).comp
        (splitFockEvenZornEquiv K).toLinearMap
    change lhs s = rhs s
    apply LinearMap.congr_fun ?_ s
    apply (splitFockEvenBasis K).ext
    intro j
    change (splitFockEvenGeneratorAt K (splitFockEvenBasis K j)) x =
      ((Zorn.paraMulRightLinear K
        (splitFockEvenZornEquiv K (splitFockEvenBasis K j))).comp
          (splitVectorZornEquiv K).toLinearMap) x
    apply LinearMap.congr_fun ?_ x
    apply (splitVectorZornBasis K).ext
    intro i
    exact h i j

/-- The full odd-to-even generator identity is equivalent to its exact
64-entry table on the explicit vector and negative-half-spin bases. -/
theorem splitFockGeneratorOddToEven_chart_iff_basis :
    (∀ (x : SplitD4Space K) (s : SplitFockOdd K),
      splitFockEvenZornEquiv K (splitFockGeneratorOddToEven K x s) =
        Zorn.paraMul K (splitFockOddZornEquiv K s)
          (splitVectorZornEquiv K x)) ↔
    (∀ (i j : Fin 8),
      splitFockEvenZornEquiv K
          (splitFockGeneratorOddToEven K
            (splitVectorZornBasis K i) (splitFockOddBasis K j)) =
        Zorn.paraMul K
          (splitFockOddZornEquiv K (splitFockOddBasis K j))
          (splitVectorZornEquiv K (splitVectorZornBasis K i))) := by
  constructor
  · intro h i j
    exact h _ _
  · intro h x s
    let lhs : SplitFockOdd K →ₗ[K] Zorn.Octonion K :=
      (splitFockEvenZornEquiv K).toLinearMap.comp
        (splitFockGeneratorOddToEven K x)
    let rhs : SplitFockOdd K →ₗ[K] Zorn.Octonion K :=
      (Zorn.paraMulRightLinear K (splitVectorZornEquiv K x)).comp
        (splitFockOddZornEquiv K).toLinearMap
    change lhs s = rhs s
    apply LinearMap.congr_fun ?_ s
    apply (splitFockOddBasis K).ext
    intro j
    change (splitFockOddGeneratorAt K (splitFockOddBasis K j)) x =
      ((Zorn.paraMulLeftLinear K
        (splitFockOddZornEquiv K (splitFockOddBasis K j))).comp
          (splitVectorZornEquiv K).toLinearMap) x
    apply LinearMap.congr_fun ?_ x
    apply (splitVectorZornBasis K).ext
    intro i
    exact h i j

end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality
