/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E8.BinaryIcosahedralAtlas
import RiemannResearch.E8.GroupSchemeFoundation
import RiemannResearch.LinearAlgebra.RootSystem.D4PairOverlattice

/-!
# D4-by-D4 lattice gluing inside the E8 atlas

This file identifies the integral lattice in the binary-icosahedral E8 atlas
with a based E8 lattice and computes the index-four D4-by-D4 glue quotient.
The glue is the shared discriminant graph attached to one D4 triality
symmetry, so the E8 calculation consumes the common D4 hierarchy.

This is an exact lattice statement. It does not construct a D4-by-D4 subgroup
scheme of an E8 group scheme, half-spin representations, or fpqc/Galois
descent.
-/

open Matrix

namespace RiemannResearch.E8.D4PairLatticeGluing

open BinaryIcosahedralAtlas
open RiemannResearch.LinearAlgebra.RootSystem.D4Triality

abbrev PairRootCoordinates := RootCoordinates × RootCoordinates

def atlasE8Basis : Mat8 := ![
  ![1,0,0,0,0,0,0,0],
  ![0,0,0,1,-1,0,-1,-1],
  ![-2,0,0,-1,0,1,0,-1],
  ![1,-1,0,0,0,-1,1,1],
  ![0,1,0,0,0,0,0,0],
  ![0,0,0,0,1,0,0,0],
  ![0,0,0,1,-1,1,-1,0],
  ![0,0,1,-1,1,0,0,1]]

def atlasE8BasisInv : Mat8 := ![
  ![1,0,0,0,0,0,0,0],
  ![0,0,0,0,1,0,0,0],
  ![1,2,2,3,3,2,1,1],
  ![0,1,1,2,2,2,1,0],
  ![0,0,0,0,0,1,0,0],
  ![1,0,1,1,1,1,1,0],
  ![1,1,2,3,3,2,1,0],
  ![-1,-1,-1,-1,-1,-1,0,0]]

set_option maxHeartbeats 0 in
-- Exhaustive multiplication of the two explicit integral 8-by-8 matrices
-- needs an unrestricted heartbeat budget.
theorem atlasE8Basis_mul_inverse :
    atlasE8Basis * atlasE8BasisInv = 1 := by
  decide

set_option maxHeartbeats 0 in
-- Exhaustive multiplication of the two explicit integral 8-by-8 matrices
-- needs an unrestricted heartbeat budget.
theorem atlasE8Basis_inverse_mul :
    atlasE8BasisInv * atlasE8Basis = 1 := by
  decide

set_option maxHeartbeats 0 in
-- The finite 8-by-8 Gram certificate needs an unrestricted heartbeat budget;
-- it proves that the atlas ambient form is integrally based-isometric to E8.
theorem atlasE8Basis_gram :
    atlasE8Basis * Q * atlasE8Basis.transpose =
      CartanMatrix.E₈ := by
  decide

def atlasPairWeightMatrix : Mat8 := ![
  ![1,0,0,0,0,1,0,-1],
  ![-1,-1,-1,0,0,0,0,1],
  ![0,1,1,-1,-1,-1,-1,0],
  ![0,1,1,1,0,0,1,0],
  ![-1,-1,0,1,1,-1,-1,0],
  ![0,1,1,0,0,0,1,-1],
  ![0,0,-1,0,0,1,0,1],
  ![1,-1,0,-1,0,0,-1,0]]

theorem atlasPairWeightMatrix_eq_pairing :
    atlasPairWeightMatrix =
      fun i j => ∑ k : I8,
        Q j k * roots (centralFirstReindex i) k := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

def atlasWeightMapFin8 : Vec8 →+ Vec8 where
  toFun := atlasPairWeightMatrix.mulVec
  map_zero' := Matrix.mulVec_zero atlasPairWeightMatrix
  map_add' := Matrix.mulVec_add atlasPairWeightMatrix

def firstBlock (x : Vec8) : WeightCoordinates :=
  fun i => x ⟨i.1, by omega⟩

def secondBlock (x : Vec8) : WeightCoordinates :=
  fun i => x ⟨i.1 + 4, by omega⟩

def atlasPairWeightMap : Vec8 →+ PairWeightCoordinates where
  toFun x :=
    (firstBlock (atlasWeightMapFin8 x),
      secondBlock (atlasWeightMapFin8 x))
  map_zero' := by
    ext i <;> simp [firstBlock, secondBlock]
  map_add' x y := by
    ext i <;> simp [firstBlock, secondBlock]

@[simp]
theorem atlasPairWeightMap_apply (x : Vec8) :
    atlasPairWeightMap x =
      (![x 0 + x 5 - x 7,
          -x 0 - x 1 - x 2 + x 7,
          x 1 + x 2 - x 3 - x 4 - x 5 - x 6,
          x 1 + x 2 + x 3 + x 6],
        ![-x 0 - x 1 + x 3 + x 4 - x 5 - x 6,
          x 1 + x 2 + x 6 - x 7,
          -x 2 + x 5 + x 7,
          x 0 - x 1 - x 3 - x 6]) := by
  ext i <;>
    fin_cases i <;>
    simp [atlasPairWeightMap, atlasWeightMapFin8, firstBlock, secondBlock,
      atlasPairWeightMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;>
    ring

def pairRootsCentralFirst : PairRootCoordinates →+ Vec8 where
  toFun x := ![
    x.1 1, x.1 0, x.1 2, x.1 3,
    x.2 1, x.2 0, x.2 2, x.2 3]
  map_zero' := by
    ext i
    fin_cases i <;> simp
  map_add' x y := by
    ext i
    fin_cases i <;> simp

def atlasRootsMatrix : Mat8 := fun i j => roots i j

def atlasRootLinear : Vec8 →+ Vec8 where
  toFun := atlasRootsMatrix.transpose.mulVec
  map_zero' := Matrix.mulVec_zero atlasRootsMatrix.transpose
  map_add' := Matrix.mulVec_add atlasRootsMatrix.transpose

def atlasRootCombination : PairRootCoordinates →+ Vec8 :=
  atlasRootLinear.comp pairRootsCentralFirst

def atlasRootSublattice : AddSubgroup Vec8 :=
  atlasRootCombination.range

theorem atlasPairWeightMap_rootCombination
    (x : PairRootCoordinates) :
    atlasPairWeightMap (atlasRootCombination x) =
      (cartanMap x.1, cartanMap x.2) := by
  ext i <;>
    fin_cases i <;>
    simp [atlasPairWeightMap, atlasWeightMapFin8, firstBlock, secondBlock,
      atlasPairWeightMatrix, atlasRootCombination, atlasRootLinear,
      atlasRootsMatrix, pairRootsCentralFirst, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, cartanMap_apply, roots, a0, a1, a2, a3,
      b0, b1, b2, b3] <;>
    ring

def atlasPairDiscriminantMap : Vec8 →+ PairDiscriminantGroup :=
  pairDiscriminantMap.comp atlasPairWeightMap

def atlasParity : Vec8 →+ DiscriminantModel where
  toFun x :=
    (((x 0 + x 1 + x 2 + x 3 + x 4 + x 6 + x 7 : ℤ) : ZMod 2),
      ((x 0 + x 1 + x 2 + x 3 + x 5 + x 6 + x 7 : ℤ) : ZMod 2))
  map_zero' := by simp
  map_add' x y := by
    ext <;> simp <;> ring

theorem atlasParity_surjective :
    Function.Surjective atlasParity := by
  rintro ⟨a, b⟩
  refine ⟨![0, 0, 0, 0, a.cast, b.cast, 0, 0], ?_⟩
  ext <;> simp [atlasParity]

theorem atlasPairDiscriminantMap_model (x : Vec8) :
    (discriminantEquivParity (atlasPairDiscriminantMap x).1,
      discriminantEquivParity (atlasPairDiscriminantMap x).2) =
    (atlasParity x,
      ((atlasParity x).1,
        (atlasParity x).1 + (atlasParity x).2)) := by
  have hfirst :
      discriminantEquivParity (atlasPairDiscriminantMap x).1 =
        parityMap (atlasPairWeightMap x).1 := by
    change discriminantEquivParity
      (QuotientAddGroup.mk' rootSublattice
        (atlasPairWeightMap x).1) = _
    exact discriminantEquivParity_mk _
  have hsecond :
      discriminantEquivParity (atlasPairDiscriminantMap x).2 =
        parityMap (atlasPairWeightMap x).2 := by
    change discriminantEquivParity
      (QuotientAddGroup.mk' rootSublattice
        (atlasPairWeightMap x).2) = _
    exact discriminantEquivParity_mk _
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hneg : ∀ z : ZMod 2, -z = z := by decide
  rw [hfirst, hsecond, atlasPairWeightMap_apply]
  ext <;>
    simp [parityMap, atlasParity] <;>
    ring_nf <;>
    simp [htwo, sub_eq_add_neg, hneg]

def atlasGlueSymmetry : DiagramSymmetry :=
  Equiv.swap .vector .halfSpinPlus

theorem modelAction_atlasGlueSymmetry :
    ∀ p : DiscriminantModel,
      modelAction atlasGlueSymmetry p =
        (p.1, p.1 + p.2) := by
  decide

noncomputable abbrev atlasGlueSubgroup :
    AddSubgroup PairDiscriminantGroup :=
  discriminantGraph atlasGlueSymmetry

@[simp]
theorem mem_atlasGlueSubgroup_iff (p : PairDiscriminantGroup) :
    p ∈ atlasGlueSubgroup ↔
      p.2 = discriminantAction atlasGlueSymmetry p.1 :=
  mem_discriminantGraph_iff atlasGlueSymmetry p

theorem atlasPairDiscriminantMap_mem_glueSubgroup (x : Vec8) :
    atlasPairDiscriminantMap x ∈ atlasGlueSubgroup := by
  rw [mem_atlasGlueSubgroup_iff]
  apply discriminantEquivParity.injective
  change discriminantEquivParity (atlasPairDiscriminantMap x).2 =
    discriminantEquivParity
      (discriminantActionPerm atlasGlueSymmetry
        (atlasPairDiscriminantMap x).1)
  rw [discriminantEquivParity_discriminantActionPerm_apply,
    modelAction_atlasGlueSymmetry]
  have h := atlasPairDiscriminantMap_model x
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  change discriminantEquivParity (atlasPairDiscriminantMap x).1 =
    atlasParity x at h₁
  change discriminantEquivParity (atlasPairDiscriminantMap x).2 =
    ((atlasParity x).1,
      (atlasParity x).1 + (atlasParity x).2) at h₂
  rw [h₁]
  exact h₂

/-- Every atlas vector maps into the common integral D4-by-D4 gluing
overlattice. -/
theorem atlasPairWeightMap_mem_pairGluingOverlattice (x : Vec8) :
    atlasPairWeightMap x ∈
      pairGluingOverlattice atlasGlueSymmetry := by
  change pairDiscriminantMap (atlasPairWeightMap x) ∈
    discriminantGraph atlasGlueSymmetry
  exact atlasPairDiscriminantMap_mem_glueSubgroup x

noncomputable def atlasGlueMap :
    Vec8 →+ atlasGlueSubgroup where
  toFun x :=
    ⟨atlasPairDiscriminantMap x,
      atlasPairDiscriminantMap_mem_glueSubgroup x⟩
  map_zero' := by
    apply Subtype.ext
    exact atlasPairDiscriminantMap.map_zero
  map_add' x y := by
    apply Subtype.ext
    exact atlasPairDiscriminantMap.map_add x y

theorem atlasGlueMap_surjective :
    Function.Surjective atlasGlueMap := by
  rintro ⟨⟨a, b⟩, hab⟩
  have hab' :
      b = discriminantAction atlasGlueSymmetry a :=
    (mem_atlasGlueSubgroup_iff (a, b)).mp hab
  obtain ⟨x, hx⟩ :=
    atlasParity_surjective (discriminantEquivParity a)
  have hmodel := atlasPairDiscriminantMap_model x
  have hfirstModel := congrArg Prod.fst hmodel
  have hfirst : (atlasPairDiscriminantMap x).1 = a := by
    apply discriminantEquivParity.injective
    simpa [hx] using hfirstModel
  refine ⟨x, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact hfirst
  · have himg := atlasPairDiscriminantMap_mem_glueSubgroup x
    rw [mem_atlasGlueSubgroup_iff] at himg
    change (atlasPairDiscriminantMap x).2 = b
    rw [himg, hab', hfirst]

theorem atlasRootSublattice_eq_atlasParity_ker :
    atlasRootSublattice = atlasParity.ker := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    have htwo : (2 : ZMod 2) = 0 := by decide
    have hfour : (4 : ZMod 2) = 0 := by decide
    ext <;>
      simp [atlasParity, atlasRootCombination, atlasRootLinear,
        atlasRootsMatrix, pairRootsCentralFirst, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, roots, a0, a1, a2, a3, b0, b1, b2, b3] <;>
      ring_nf <;>
      simp [htwo, hfour]
  · intro x hx
    change atlasParity x = 0 at hx
    have hfst := congrArg Prod.fst hx
    have hsnd := congrArg Prod.snd hx
    change
      ((x 0 + x 1 + x 2 + x 3 + x 4 + x 6 + x 7 : ℤ) :
        ZMod 2) = 0 at hfst
    change
      ((x 0 + x 1 + x 2 + x 3 + x 5 + x 6 + x 7 : ℤ) :
        ZMod 2) = 0 at hsnd
    have hd₁ : (2 : ℤ) ∣
        x 0 + x 1 + x 2 + x 3 + x 4 + x 6 + x 7 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd
        (x 0 + x 1 + x 2 + x 3 + x 4 + x 6 + x 7) 2).mp hfst
    have hd₂ : (2 : ℤ) ∣
        x 0 + x 1 + x 2 + x 3 + x 5 + x 6 + x 7 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd
        (x 0 + x 1 + x 2 + x 3 + x 5 + x 6 + x 7) 2).mp hsnd
    rcases hd₁ with ⟨k, hk⟩
    rcases hd₂ with ⟨l, hl⟩
    refine ⟨
      (![l - k,
          -x 0 - x 4 + x 7,
          l - x 0 - x 3 - x 4 - x 5 - x 6,
          k - x 0 - x 4],
        ![l - x 0 - x 1 + x 4 - x 5 - x 6 - x 7,
          x 2 + x 4 - x 7,
          k + l - x 0 - x 1 - x 2 - x 3 - x 6 - x 7,
          k - x 1 - x 3 - x 6 - x 7]), ?_⟩
    ext i
    fin_cases i <;>
      simp [atlasRootCombination, atlasRootLinear, atlasRootsMatrix,
        pairRootsCentralFirst, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, roots, a0, a1, a2, a3,
        b0, b1, b2, b3] <;>
      omega

theorem atlasGlueMap_ker_eq_atlasParity_ker :
    atlasGlueMap.ker = atlasParity.ker := by
  ext x
  change atlasGlueMap x = 0 ↔ atlasParity x = 0
  constructor
  · intro hx
    have hpair : atlasPairDiscriminantMap x = 0 :=
      congrArg Subtype.val hx
    have hmodel :=
      congrArg Prod.fst (atlasPairDiscriminantMap_model x)
    rw [hpair] at hmodel
    simpa using hmodel.symm
  · intro hx
    apply Subtype.ext
    change atlasPairDiscriminantMap x = 0
    apply Prod.ext
    · apply discriminantEquivParity.injective
      have hmodel :=
        congrArg Prod.fst (atlasPairDiscriminantMap_model x)
      rw [hx] at hmodel
      simpa using hmodel
    · have hmodel :=
        congrArg Prod.snd (atlasPairDiscriminantMap_model x)
      rw [hx] at hmodel
      have heq :
          discriminantEquivParity (atlasPairDiscriminantMap x).2 =
            discriminantEquivParity (0 : DiscriminantGroup) := by
        exact hmodel.trans discriminantEquivParity.map_zero.symm
      exact discriminantEquivParity.injective heq

theorem atlasRootSublattice_eq_atlasGlueMap_ker :
    atlasRootSublattice = atlasGlueMap.ker :=
  atlasRootSublattice_eq_atlasParity_ker.trans
    atlasGlueMap_ker_eq_atlasParity_ker.symm

noncomputable def atlasD4PairQuotientEquivGlue :
    Vec8 ⧸ atlasRootSublattice ≃+ atlasGlueSubgroup :=
  (QuotientAddGroup.quotientAddEquivOfEq
      atlasRootSublattice_eq_atlasGlueMap_ker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      atlasGlueMap atlasGlueMap_surjective)

theorem natCard_atlasD4PairQuotient :
    Nat.card (Vec8 ⧸ atlasRootSublattice) = 4 := by
  rw [Nat.card_congr atlasD4PairQuotientEquivGlue.toEquiv]
  exact natCard_discriminantGraph atlasGlueSymmetry

end RiemannResearch.E8.D4PairLatticeGluing
