/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.LinearAlgebra.RootSystem.D4ZornFockCharts
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornBaseChange

/-!
# Generator-level Fock/Zorn triality comparison

This module packages the parity-changing exterior-Fock generator, proves the
two exact 8-by-8 integral tables on the explicit vector and half-spin bases,
and derives both Zorn block identities over every field by base change and
bilinearity. No dimension argument or unspecified comparison map is used.
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
/-! ## Ordered exterior monomials for the finite generator tables -/

/-- The element in position \`i\` of the increasingly sorted list underlying a
finite subset. Keeping the cardinality proof explicit lets the kernel reduce
all sixteen monomials below without evaluating a noncomputable permutation
sign. -/
private def splitFockSortedIndex (s : Finset (Fin 4)) {n : ℕ}
    (h : s.card = n) (i : Fin n) : Fin 4 :=
  (s.sort (fun a b => a ≤ b)).get
    ⟨i.1, by simp [h, i.2]⟩

private theorem splitFock_sort_eq_of_eq_toFinset
    (s : Finset (Fin 4)) (l : List (Fin 4))
    (h : s = l.toFinset) (hn : l.Nodup)
    (ho : List.Pairwise (fun a b : Fin 4 => a ≤ b) l) :
    s.sort (fun a b => a ≤ b) = l := by
  rw [h]
  exact
    (List.toFinset_sort (r := fun a b : Fin 4 => a ≤ b) hn).2 ho

private theorem splitFock_basis_eq_ιMulti_sorted
    {s : Finset (Fin 4)} {n : ℕ} (h : s.card = n) :
    (Pi.basisFun K (Fin 4)).ExteriorAlgebra s =
      ExteriorAlgebra.ιMulti K n
        (fun i =>
          (Pi.basisFun K (Fin 4)) (splitFockSortedIndex s h i)) := by
  rw [ExteriorAlgebra.basis_apply_ofCard
    (Pi.basisFun K (Fin 4)) h]
  simp only [ExteriorAlgebra.ιMulti_family,
    Set.powersetCard.ofFinEmbEquiv]
  apply congrArg (ExteriorAlgebra.ιMulti K n)
  funext i
  apply congrArg (fun j => (Pi.basisFun K (Fin 4)) j)
  exact Finset.orderEmbOfFin_apply _ _ _

private def splitFockIota (i : Fin 4) :
    ExteriorAlgebra K (Fin 4 → K) :=
  ExteriorAlgebra.ι K ((Pi.basisFun K (Fin 4)) i)

/-- The eight ordered even exterior monomials in chart order. -/
private def splitFockEvenProduct :
    Fin 8 → ExteriorAlgebra K (Fin 4 → K) := ![
  1,
  splitFockIota K 0 * splitFockIota K 1,
  splitFockIota K 0 * splitFockIota K 2,
  splitFockIota K 0 * splitFockIota K 3,
  splitFockIota K 2 * splitFockIota K 3,
  splitFockIota K 1 * splitFockIota K 3,
  splitFockIota K 1 * splitFockIota K 2,
  splitFockIota K 0 *
    (splitFockIota K 1 *
      (splitFockIota K 2 * splitFockIota K 3))]

/-- The eight ordered odd exterior monomials in chart order. -/
private def splitFockOddProduct :
    Fin 8 → ExteriorAlgebra K (Fin 4 → K) := ![
  splitFockIota K 1 *
    (splitFockIota K 2 * splitFockIota K 3),
  splitFockIota K 1,
  splitFockIota K 2,
  splitFockIota K 3,
  splitFockIota K 0 *
    (splitFockIota K 2 * splitFockIota K 3),
  splitFockIota K 0 *
    (splitFockIota K 1 * splitFockIota K 3),
  splitFockIota K 0 *
    (splitFockIota K 1 * splitFockIota K 2),
  splitFockIota K 0]

private theorem splitFockEvenBasisVector_val (i : Fin 8) :
    (splitFockEvenBasisVector K i :
        ExteriorAlgebra K (Fin 4 → K)) =
      splitFockEvenProduct K i := by
  fin_cases i
  · change
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra ∅ = 1
    rw [splitFock_basis_eq_ιMulti_sorted K
      (n := 0) (by decide)]
    have hs :
        (∅ : Finset (Fin 4)).sort (fun a b => a ≤ b) = [] := by
      exact splitFock_sort_eq_of_eq_toFinset _ _
        (by decide) (by decide) (by decide)
    simp [splitFockSortedIndex, hs]
  · change
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra {0, 1} =
        splitFockIota K 0 * splitFockIota K 1
    rw [splitFock_basis_eq_ιMulti_sorted K
      (n := 2) (by decide)]
    have hs :
        ({0, 1} : Finset (Fin 4)).sort
            (fun a b => a ≤ b) = [0, 1] := by
      exact splitFock_sort_eq_of_eq_toFinset _ _
        (by decide) (by decide) (by decide)
    simp [splitFockSortedIndex, hs, splitFockIota,
      ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]
  · change
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra {0, 2} =
        splitFockIota K 0 * splitFockIota K 2
    rw [splitFock_basis_eq_ιMulti_sorted K
      (n := 2) (by decide)]
    have hs :
        ({0, 2} : Finset (Fin 4)).sort
            (fun a b => a ≤ b) = [0, 2] := by
      exact splitFock_sort_eq_of_eq_toFinset _ _
        (by decide) (by decide) (by decide)
    simp [splitFockSortedIndex, hs, splitFockIota,
      ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]
  · change
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra {0, 3} =
        splitFockIota K 0 * splitFockIota K 3
    rw [splitFock_basis_eq_ιMulti_sorted K
      (n := 2) (by decide)]
    have hs :
        ({0, 3} : Finset (Fin 4)).sort
            (fun a b => a ≤ b) = [0, 3] := by
      exact splitFock_sort_eq_of_eq_toFinset _ _
        (by decide) (by decide) (by decide)
    simp [splitFockSortedIndex, hs, splitFockIota,
      ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]
  · change
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra {2, 3} =
        splitFockIota K 2 * splitFockIota K 3
    rw [splitFock_basis_eq_ιMulti_sorted K
      (n := 2) (by decide)]
    have hs :
        ({2, 3} : Finset (Fin 4)).sort
            (fun a b => a ≤ b) = [2, 3] := by
      exact splitFock_sort_eq_of_eq_toFinset _ _
        (by decide) (by decide) (by decide)
    simp [splitFockSortedIndex, hs, splitFockIota,
      ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]
  · change
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra {1, 3} =
        splitFockIota K 1 * splitFockIota K 3
    rw [splitFock_basis_eq_ιMulti_sorted K
      (n := 2) (by decide)]
    have hs :
        ({1, 3} : Finset (Fin 4)).sort
            (fun a b => a ≤ b) = [1, 3] := by
      exact splitFock_sort_eq_of_eq_toFinset _ _
        (by decide) (by decide) (by decide)
    simp [splitFockSortedIndex, hs, splitFockIota,
      ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]
  · change
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra {1, 2} =
        splitFockIota K 1 * splitFockIota K 2
    rw [splitFock_basis_eq_ιMulti_sorted K
      (n := 2) (by decide)]
    have hs :
        ({1, 2} : Finset (Fin 4)).sort
            (fun a b => a ≤ b) = [1, 2] := by
      exact splitFock_sort_eq_of_eq_toFinset _ _
        (by decide) (by decide) (by decide)
    simp [splitFockSortedIndex, hs, splitFockIota,
      ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]
  · change
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra Finset.univ =
        splitFockIota K 0 *
          (splitFockIota K 1 *
            (splitFockIota K 2 * splitFockIota K 3))
    rw [splitFock_basis_eq_ιMulti_sorted K
      (n := 4) (by decide)]
    have hs :
        (Finset.univ : Finset (Fin 4)).sort
            (fun a b => a ≤ b) = [0, 1, 2, 3] := by
      exact splitFock_sort_eq_of_eq_toFinset _ _
        (by decide) (by decide) (by decide)
    simp [splitFockSortedIndex, hs, splitFockIota,
      ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]

private theorem splitFockOddBasisVector_val (i : Fin 8) :
    (splitFockOddBasisVector K i :
        ExteriorAlgebra K (Fin 4 → K)) =
      splitFockOddProduct K i := by
  fin_cases i
  · change
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra {1, 2, 3} =
        splitFockIota K 1 *
          (splitFockIota K 2 * splitFockIota K 3)
    rw [splitFock_basis_eq_ιMulti_sorted K
      (n := 3) (by decide)]
    have hs :
        ({1, 2, 3} : Finset (Fin 4)).sort
            (fun a b => a ≤ b) = [1, 2, 3] := by
      exact splitFock_sort_eq_of_eq_toFinset _ _
        (by decide) (by decide) (by decide)
    simp [splitFockSortedIndex, hs, splitFockIota,
      ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]
  · change
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra {1} =
        splitFockIota K 1
    rw [splitFock_basis_eq_ιMulti_sorted K
      (n := 1) (by decide)]
    have hs :
        ({1} : Finset (Fin 4)).sort
            (fun a b => a ≤ b) = [1] := by
      exact splitFock_sort_eq_of_eq_toFinset _ _
        (by decide) (by decide) (by decide)
    simp [splitFockSortedIndex, hs, splitFockIota,
      ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]
  · change
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra {2} =
        splitFockIota K 2
    rw [splitFock_basis_eq_ιMulti_sorted K
      (n := 1) (by decide)]
    have hs :
        ({2} : Finset (Fin 4)).sort
            (fun a b => a ≤ b) = [2] := by
      exact splitFock_sort_eq_of_eq_toFinset _ _
        (by decide) (by decide) (by decide)
    simp [splitFockSortedIndex, hs, splitFockIota,
      ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]
  · change
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra {3} =
        splitFockIota K 3
    rw [splitFock_basis_eq_ιMulti_sorted K
      (n := 1) (by decide)]
    have hs :
        ({3} : Finset (Fin 4)).sort
            (fun a b => a ≤ b) = [3] := by
      exact splitFock_sort_eq_of_eq_toFinset _ _
        (by decide) (by decide) (by decide)
    simp [splitFockSortedIndex, hs, splitFockIota,
      ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]
  · change
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra {0, 2, 3} =
        splitFockIota K 0 *
          (splitFockIota K 2 * splitFockIota K 3)
    rw [splitFock_basis_eq_ιMulti_sorted K
      (n := 3) (by decide)]
    have hs :
        ({0, 2, 3} : Finset (Fin 4)).sort
            (fun a b => a ≤ b) = [0, 2, 3] := by
      exact splitFock_sort_eq_of_eq_toFinset _ _
        (by decide) (by decide) (by decide)
    simp [splitFockSortedIndex, hs, splitFockIota,
      ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]
  · change
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra {0, 1, 3} =
        splitFockIota K 0 *
          (splitFockIota K 1 * splitFockIota K 3)
    rw [splitFock_basis_eq_ιMulti_sorted K
      (n := 3) (by decide)]
    have hs :
        ({0, 1, 3} : Finset (Fin 4)).sort
            (fun a b => a ≤ b) = [0, 1, 3] := by
      exact splitFock_sort_eq_of_eq_toFinset _ _
        (by decide) (by decide) (by decide)
    simp [splitFockSortedIndex, hs, splitFockIota,
      ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]
  · change
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra {0, 1, 2} =
        splitFockIota K 0 *
          (splitFockIota K 1 * splitFockIota K 2)
    rw [splitFock_basis_eq_ιMulti_sorted K
      (n := 3) (by decide)]
    have hs :
        ({0, 1, 2} : Finset (Fin 4)).sort
            (fun a b => a ≤ b) = [0, 1, 2] := by
      exact splitFock_sort_eq_of_eq_toFinset _ _
        (by decide) (by decide) (by decide)
    simp [splitFockSortedIndex, hs, splitFockIota,
      ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]
  · change
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra {0} =
        splitFockIota K 0
    rw [splitFock_basis_eq_ιMulti_sorted K
      (n := 1) (by decide)]
    have hs :
        ({0} : Finset (Fin 4)).sort
            (fun a b => a ≤ b) = [0] := by
      exact splitFock_sort_eq_of_eq_toFinset _ _
        (by decide) (by decide) (by decide)
    simp [splitFockSortedIndex, hs, splitFockIota,
      ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]

private theorem splitFockEvenBasis_eq_vector (i : Fin 8) :
    splitFockEvenBasis K i = splitFockEvenBasisVector K i := by
  simp [splitFockEvenBasis]

private theorem splitFockOddBasis_eq_vector (i : Fin 8) :
    splitFockOddBasis K i = splitFockOddBasisVector K i := by
  simp [splitFockOddBasis]

private theorem splitFockIota_sq_tail
    (i : Fin 4) (z : ExteriorAlgebra K (Fin 4 → K)) :
    splitFockIota K i * (splitFockIota K i * z) = 0 := by
  rw [← mul_assoc, splitFockIota,
    ExteriorAlgebra.ι_sq_zero, zero_mul]

private theorem splitFockIota_swap_tail_of_lt
    (i j : Fin 4) (_h : i < j)
    (z : ExteriorAlgebra K (Fin 4 → K)) :
    splitFockIota K j * (splitFockIota K i * z) =
      -(splitFockIota K i * (splitFockIota K j * z)) := by
  have hswap :
      splitFockIota K j * splitFockIota K i =
        -(splitFockIota K i * splitFockIota K j) := by
    apply eq_neg_of_add_eq_zero_left
    exact ExteriorAlgebra.ι_add_mul_swap _ _
  calc
    splitFockIota K j * (splitFockIota K i * z) =
        (splitFockIota K j * splitFockIota K i) * z := by
      rw [mul_assoc]
    _ = (-(splitFockIota K i * splitFockIota K j)) * z := by
      rw [hswap]
    _ = -(splitFockIota K i *
        (splitFockIota K j * z)) := by
      rw [neg_mul, mul_assoc]

private theorem splitFockIota_raw_sq_tail
    (i : Fin 4) (z : ExteriorAlgebra K (Fin 4 → K)) :
    ExteriorAlgebra.ι K ((Pi.basisFun K (Fin 4)) i) *
        (ExteriorAlgebra.ι K ((Pi.basisFun K (Fin 4)) i) * z) = 0 := by
  simpa [splitFockIota] using splitFockIota_sq_tail K i z

private theorem splitFockIota_raw_swap_of_lt
    (i j : Fin 4) (h : i < j) :
    ExteriorAlgebra.ι K ((Pi.basisFun K (Fin 4)) j) *
        ExteriorAlgebra.ι K ((Pi.basisFun K (Fin 4)) i) =
      -(ExteriorAlgebra.ι K ((Pi.basisFun K (Fin 4)) i) *
        ExteriorAlgebra.ι K ((Pi.basisFun K (Fin 4)) j)) := by
  simpa [splitFockIota] using
    splitFockIota_swap_tail_of_lt K i j h 1

private theorem splitFockIota_raw_swap_tail_of_lt
    (i j : Fin 4) (h : i < j)
    (z : ExteriorAlgebra K (Fin 4 → K)) :
    ExteriorAlgebra.ι K ((Pi.basisFun K (Fin 4)) j) *
        (ExteriorAlgebra.ι K ((Pi.basisFun K (Fin 4)) i) * z) =
      -(ExteriorAlgebra.ι K ((Pi.basisFun K (Fin 4)) i) *
        (ExteriorAlgebra.ι K ((Pi.basisFun K (Fin 4)) j) * z)) := by
  simpa [splitFockIota] using
    splitFockIota_swap_tail_of_lt K i j h z


private theorem splitFock_basisFun_eq_single (i : Fin 4) :
    (Pi.basisFun K (Fin 4)) i = Pi.single i 1 := by
  ext j
  simp

private theorem splitFockPiIota_sq_tail
    (i : Fin 4) (z : ExteriorAlgebra K (Fin 4 → K)) :
    ExteriorAlgebra.ι K (Pi.single i 1 : Fin 4 → K) *
        (ExteriorAlgebra.ι K (Pi.single i 1 : Fin 4 → K) * z) = 0 := by
  simpa [splitFock_basisFun_eq_single] using
    splitFockIota_raw_sq_tail K i z

private theorem splitFockPiIota_swap_of_lt
    (i j : Fin 4) (h : i < j) :
    ExteriorAlgebra.ι K (Pi.single j 1 : Fin 4 → K) *
        ExteriorAlgebra.ι K (Pi.single i 1 : Fin 4 → K) =
      -(ExteriorAlgebra.ι K (Pi.single i 1 : Fin 4 → K) *
        ExteriorAlgebra.ι K (Pi.single j 1 : Fin 4 → K)) := by
  simpa [splitFock_basisFun_eq_single] using
    splitFockIota_raw_swap_of_lt K i j h

private theorem splitFockPiIota_swap_tail_of_lt
    (i j : Fin 4) (h : i < j)
    (z : ExteriorAlgebra K (Fin 4 → K)) :
    ExteriorAlgebra.ι K (Pi.single j 1 : Fin 4 → K) *
        (ExteriorAlgebra.ι K (Pi.single i 1 : Fin 4 → K) * z) =
      -(ExteriorAlgebra.ι K (Pi.single i 1 : Fin 4 → K) *
        (ExteriorAlgebra.ι K (Pi.single j 1 : Fin 4 → K) * z)) := by
  simpa [splitFock_basisFun_eq_single] using
    splitFockIota_raw_swap_tail_of_lt K i j h z

private def splitFockEvenToOddBasisOutput
    (i j : Fin 8) : SplitFockOdd K := ![
  ![splitFockOddBasisVector K 7, 0, 0, 0,
    splitFockOddBasisVector K 4, splitFockOddBasisVector K 5,
    splitFockOddBasisVector K 6, 0],
  ![splitFockOddBasisVector K 1, 0, -splitFockOddBasisVector K 6,
    -splitFockOddBasisVector K 5, splitFockOddBasisVector K 0, 0, 0, 0],
  ![splitFockOddBasisVector K 2, splitFockOddBasisVector K 6, 0,
    -splitFockOddBasisVector K 4, 0, -splitFockOddBasisVector K 0, 0, 0],
  ![splitFockOddBasisVector K 3, splitFockOddBasisVector K 5,
    splitFockOddBasisVector K 4, 0, 0, 0,
    splitFockOddBasisVector K 0, 0],
  ![0, splitFockOddBasisVector K 7, 0, 0, 0,
    -splitFockOddBasisVector K 3, -splitFockOddBasisVector K 2,
    splitFockOddBasisVector K 4],
  ![0, 0, splitFockOddBasisVector K 7, 0,
    -splitFockOddBasisVector K 3, 0, splitFockOddBasisVector K 1,
    -splitFockOddBasisVector K 5],
  ![0, 0, 0, splitFockOddBasisVector K 7,
    splitFockOddBasisVector K 2, splitFockOddBasisVector K 1, 0,
    splitFockOddBasisVector K 6],
  ![0, splitFockOddBasisVector K 1, splitFockOddBasisVector K 2,
    splitFockOddBasisVector K 3, 0, 0, 0,
    splitFockOddBasisVector K 0]] i j

private def splitFockOddToEvenBasisOutput
    (i j : Fin 8) : SplitFockEven K := ![
  ![splitFockEvenBasisVector K 7, splitFockEvenBasisVector K 1,
    splitFockEvenBasisVector K 2, splitFockEvenBasisVector K 3, 0, 0, 0, 0],
  ![0, 0, splitFockEvenBasisVector K 6,
    splitFockEvenBasisVector K 5, -splitFockEvenBasisVector K 7, 0, 0,
    -splitFockEvenBasisVector K 1],
  ![0, -splitFockEvenBasisVector K 6, 0,
    splitFockEvenBasisVector K 4, 0, splitFockEvenBasisVector K 7, 0,
    -splitFockEvenBasisVector K 2],
  ![0, -splitFockEvenBasisVector K 5, -splitFockEvenBasisVector K 4, 0,
    0, 0, -splitFockEvenBasisVector K 7, -splitFockEvenBasisVector K 3],
  ![-splitFockEvenBasisVector K 4, -splitFockEvenBasisVector K 0, 0, 0,
    0, splitFockEvenBasisVector K 3, splitFockEvenBasisVector K 2, 0],
  ![splitFockEvenBasisVector K 5, 0, -splitFockEvenBasisVector K 0, 0,
    splitFockEvenBasisVector K 3, 0, -splitFockEvenBasisVector K 1, 0],
  ![-splitFockEvenBasisVector K 6, 0, 0, -splitFockEvenBasisVector K 0,
    -splitFockEvenBasisVector K 2, -splitFockEvenBasisVector K 1, 0, 0],
  ![0, 0, 0, 0, splitFockEvenBasisVector K 4,
    splitFockEvenBasisVector K 5, splitFockEvenBasisVector K 6,
    splitFockEvenBasisVector K 0]] i j

set_option maxHeartbeats 1000000 in
-- The 64 explicit exterior-algebra reductions need a larger simplifier budget.
private theorem splitFockGeneratorEvenToOdd_basis_output
    (i j : Fin 8) :
    splitFockGeneratorEvenToOdd K
        (splitVectorZornBasis K i) (splitFockEvenBasis K j) =
      splitFockEvenToOddBasisOutput K i j := by
  fin_cases i <;> fin_cases j
  all_goals
    rw [splitVectorZornBasis_eq_source,
      splitFockEvenBasis_eq_vector]
    apply Subtype.ext
    simp [splitVectorZornBasisSource,
      splitFockGeneratorEvenToOdd,
      exteriorFockGenerator_apply,
      splitFockEvenBasisVector_val,
      splitFockOddBasisVector_val,
      splitFockEvenProduct, splitFockOddProduct,
      splitFockEvenToOddBasisOutput,
      splitFockPiIota_sq_tail,
      splitFockPiIota_swap_of_lt,
      splitFockPiIota_swap_tail_of_lt,
      splitFockIota,
      CliffordAlgebra.contractLeft_ι_mul]

set_option maxHeartbeats 1000000 in
-- The 64 explicit exterior-algebra reductions need a larger simplifier budget.
private theorem splitFockGeneratorOddToEven_basis_output
    (i j : Fin 8) :
    splitFockGeneratorOddToEven K
        (splitVectorZornBasis K i) (splitFockOddBasis K j) =
      splitFockOddToEvenBasisOutput K i j := by
  fin_cases i <;> fin_cases j
  all_goals
    rw [splitVectorZornBasis_eq_source,
      splitFockOddBasis_eq_vector]
    apply Subtype.ext
    simp [splitVectorZornBasisSource,
      splitFockGeneratorOddToEven,
      exteriorFockGenerator_apply,
      splitFockEvenBasisVector_val,
      splitFockOddBasisVector_val,
      splitFockEvenProduct, splitFockOddProduct,
      splitFockOddToEvenBasisOutput,
      splitFockPiIota_sq_tail,
      splitFockPiIota_swap_of_lt,
      splitFockPiIota_swap_tail_of_lt,
      splitFockIota,
      CliffordAlgebra.contractLeft_ι_mul]


/-! ## Integral coordinate certificates for the Zorn tables -/

/-- Standard Zorn coordinates, over the integers. -/
private def splitFockVectorCoordinateInt
    (i : Fin 8) : Zorn.Octonion ℤ :=
  Pi.single i 1

/-- Signed positive-half-spin coordinates, over the integers. -/
private def splitFockEvenCoordinateInt :
    Fin 8 → Zorn.Octonion ℤ := ![
  Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1,
  Pi.single 4 1, -(Pi.single 5 1), Pi.single 6 1, Pi.single 7 1]

/-- Signed negative-half-spin coordinates, over the integers. -/
private def splitFockOddCoordinateInt :
    Fin 8 → Zorn.Octonion ℤ := ![
  Pi.single 0 1, -(Pi.single 1 1), -(Pi.single 2 1),
  -(Pi.single 3 1), -(Pi.single 4 1), Pi.single 5 1,
  -(Pi.single 6 1), Pi.single 7 1]

/-- Integral coordinate table for the even-to-odd generator. -/
private def splitFockEvenToOddCoordinateInt :
    Fin 8 → Fin 8 → Zorn.Octonion ℤ := ![
  ![Pi.single 7 1, 0, 0, 0, -(Pi.single 4 1), Pi.single 5 1,
    -(Pi.single 6 1), 0],
  ![-(Pi.single 1 1), 0, Pi.single 6 1, -(Pi.single 5 1),
    Pi.single 0 1, 0, 0, 0],
  ![-(Pi.single 2 1), -(Pi.single 6 1), 0, Pi.single 4 1,
    0, -(Pi.single 0 1), 0, 0],
  ![-(Pi.single 3 1), Pi.single 5 1, -(Pi.single 4 1), 0,
    0, 0, Pi.single 0 1, 0],
  ![0, Pi.single 7 1, 0, 0, 0, Pi.single 3 1, Pi.single 2 1,
    -(Pi.single 4 1)],
  ![0, 0, Pi.single 7 1, 0, Pi.single 3 1, 0,
    -(Pi.single 1 1), -(Pi.single 5 1)],
  ![0, 0, 0, Pi.single 7 1, -(Pi.single 2 1),
    -(Pi.single 1 1), 0, -(Pi.single 6 1)],
  ![0, -(Pi.single 1 1), -(Pi.single 2 1), -(Pi.single 3 1),
    0, 0, 0, Pi.single 0 1]]

/-- Integral coordinate table for the odd-to-even generator. -/
private def splitFockOddToEvenCoordinateInt :
    Fin 8 → Fin 8 → Zorn.Octonion ℤ := ![
  ![Pi.single 7 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1,
    0, 0, 0, 0],
  ![0, 0, Pi.single 6 1, -(Pi.single 5 1), -(Pi.single 7 1),
    0, 0, -(Pi.single 1 1)],
  ![0, -(Pi.single 6 1), 0, Pi.single 4 1, 0, Pi.single 7 1,
    0, -(Pi.single 2 1)],
  ![0, Pi.single 5 1, -(Pi.single 4 1), 0, 0, 0,
    -(Pi.single 7 1), -(Pi.single 3 1)],
  ![-(Pi.single 4 1), -(Pi.single 0 1), 0, 0, 0,
    Pi.single 3 1, Pi.single 2 1, 0],
  ![-(Pi.single 5 1), 0, -(Pi.single 0 1), 0, Pi.single 3 1,
    0, -(Pi.single 1 1), 0],
  ![-(Pi.single 6 1), 0, 0, -(Pi.single 0 1),
    -(Pi.single 2 1), -(Pi.single 1 1), 0, 0],
  ![0, 0, 0, 0, Pi.single 4 1, -(Pi.single 5 1),
    Pi.single 6 1, Pi.single 0 1]]

private theorem splitFockEvenToOddCoordinateInt_table :
    ∀ (i j : Fin 8),
      splitFockEvenToOddCoordinateInt i j =
        Zorn.paraMul ℤ (splitFockVectorCoordinateInt i)
          (splitFockEvenCoordinateInt j) := by
  decide

private theorem splitFockOddToEvenCoordinateInt_table :
    ∀ (i j : Fin 8),
      splitFockOddToEvenCoordinateInt i j =
        Zorn.paraMul ℤ (splitFockOddCoordinateInt j)
          (splitFockVectorCoordinateInt i) := by
  decide

private theorem splitFockVectorCoordinateInt_map (i : Fin 8) :
    Zorn.map (Int.castRingHom K) (splitFockVectorCoordinateInt i) =
      Pi.single i 1 := by
  ext k
  fin_cases i <;> fin_cases k <;>
    simp [splitFockVectorCoordinateInt, Zorn.map]

private theorem splitFockEvenCoordinateInt_map (i : Fin 8) :
    Zorn.map (Int.castRingHom K) (splitFockEvenCoordinateInt i) =
      splitFockEvenZornSignEquiv K (Pi.single i 1) := by
  ext k
  fin_cases i <;> fin_cases k <;>
    simp [splitFockEvenCoordinateInt, Zorn.map,
      splitFockEvenZornSignEquiv]

private theorem splitFockOddCoordinateInt_map (i : Fin 8) :
    Zorn.map (Int.castRingHom K) (splitFockOddCoordinateInt i) =
      splitFockOddZornSignEquiv K (Pi.single i 1) := by
  ext k
  fin_cases i <;> fin_cases k <;>
    simp [splitFockOddCoordinateInt, Zorn.map,
      splitFockOddZornSignEquiv]

private theorem splitFockEvenToOddBasisOutput_coordinate
    (i j : Fin 8) :
    splitFockOddZornEquiv K (splitFockEvenToOddBasisOutput K i j) =
      Zorn.map (Int.castRingHom K)
        (splitFockEvenToOddCoordinateInt i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [splitFockEvenToOddBasisOutput,
      splitFockEvenToOddCoordinateInt,
      splitFockOddCoordinateInt,
      splitFockOddZornEquiv_basisVector,
      ← splitFockOddCoordinateInt_map K]

private theorem splitFockOddToEvenBasisOutput_coordinate
    (i j : Fin 8) :
    splitFockEvenZornEquiv K (splitFockOddToEvenBasisOutput K i j) =
      Zorn.map (Int.castRingHom K)
        (splitFockOddToEvenCoordinateInt i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [splitFockOddToEvenBasisOutput,
      splitFockOddToEvenCoordinateInt,
      splitFockEvenCoordinateInt,
      splitFockEvenZornEquiv_basisVector,
      ← splitFockEvenCoordinateInt_map K]

private theorem splitFockEvenToOddCoordinate_table (i j : Fin 8) :
    Zorn.map (Int.castRingHom K)
        (splitFockEvenToOddCoordinateInt i j) =
      Zorn.paraMul K
        (Zorn.map (Int.castRingHom K) (splitFockVectorCoordinateInt i))
        (Zorn.map (Int.castRingHom K) (splitFockEvenCoordinateInt j)) := by
  rw [← Zorn.map_paraMul]
  exact congrArg (Zorn.map (Int.castRingHom K))
    (splitFockEvenToOddCoordinateInt_table i j)

private theorem splitFockOddToEvenCoordinate_table (i j : Fin 8) :
    Zorn.map (Int.castRingHom K)
        (splitFockOddToEvenCoordinateInt i j) =
      Zorn.paraMul K
        (Zorn.map (Int.castRingHom K) (splitFockOddCoordinateInt j))
        (Zorn.map (Int.castRingHom K) (splitFockVectorCoordinateInt i)) := by
  rw [← Zorn.map_paraMul]
  exact congrArg (Zorn.map (Int.castRingHom K))
    (splitFockOddToEvenCoordinateInt_table i j)

/-- The exact 64-entry even-to-odd Fock/Zorn generator table. -/
theorem splitFockGeneratorEvenToOdd_chart_basis (i j : Fin 8) :
    splitFockOddZornEquiv K
        (splitFockGeneratorEvenToOdd K
          (splitVectorZornBasis K i) (splitFockEvenBasis K j)) =
      Zorn.paraMul K
        (splitVectorZornEquiv K (splitVectorZornBasis K i))
        (splitFockEvenZornEquiv K (splitFockEvenBasis K j)) := by
  rw [splitFockGeneratorEvenToOdd_basis_output,
    splitFockEvenBasis_eq_vector,
    splitFockEvenToOddBasisOutput_coordinate,
    splitVectorZornEquiv_basis,
    splitFockEvenZornEquiv_basisVector,
    ← splitFockVectorCoordinateInt_map K i,
    ← splitFockEvenCoordinateInt_map K j]
  exact splitFockEvenToOddCoordinate_table K i j

/-- The exact 64-entry odd-to-even Fock/Zorn generator table. -/
theorem splitFockGeneratorOddToEven_chart_basis (i j : Fin 8) :
    splitFockEvenZornEquiv K
        (splitFockGeneratorOddToEven K
          (splitVectorZornBasis K i) (splitFockOddBasis K j)) =
      Zorn.paraMul K
        (splitFockOddZornEquiv K (splitFockOddBasis K j))
        (splitVectorZornEquiv K (splitVectorZornBasis K i)) := by
  rw [splitFockGeneratorOddToEven_basis_output,
    splitFockOddBasis_eq_vector,
    splitFockOddToEvenBasisOutput_coordinate,
    splitVectorZornEquiv_basis,
    splitFockOddZornEquiv_basisVector,
    ← splitFockVectorCoordinateInt_map K i,
    ← splitFockOddCoordinateInt_map K j]
  exact splitFockOddToEvenCoordinate_table K i j

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

/-- The Fock generator from the positive to the negative half-spin module
matches left para-octonion multiplication in the chosen triality charts. -/
theorem splitFockGeneratorEvenToOdd_chart :
    ∀ (x : SplitD4Space K) (s : SplitFockEven K),
      splitFockOddZornEquiv K (splitFockGeneratorEvenToOdd K x s) =
        Zorn.paraMul K (splitVectorZornEquiv K x)
          (splitFockEvenZornEquiv K s) :=
  (splitFockGeneratorEvenToOdd_chart_iff_basis K).2
    (splitFockGeneratorEvenToOdd_chart_basis K)

/-- The Fock generator from the negative to the positive half-spin module
matches right para-octonion multiplication in the chosen triality charts. -/
theorem splitFockGeneratorOddToEven_chart :
    ∀ (x : SplitD4Space K) (s : SplitFockOdd K),
      splitFockEvenZornEquiv K (splitFockGeneratorOddToEven K x s) =
        Zorn.paraMul K (splitFockOddZornEquiv K s)
          (splitVectorZornEquiv K x) :=
  (splitFockGeneratorOddToEven_chart_iff_basis K).2
    (splitFockGeneratorOddToEven_chart_basis K)

end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality
