/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card

/-!
# An exact binary-icosahedral packet in SL(2, F5)

The four coordinates encode a two-by-two matrix over `Fin 5`. Bounded
fixed-point closure constructs exact finite subsets modelling the subgroups
used in the companion Wolfram audit. The final theorems are evaluated by
Lean's kernel `decide`; no generated axiom is used.

This certificate establishes the cardinal arithmetic of the finite
degree-five/degree-six model. It does not package the subsets as Lean
`Subgroup` objects or establish the E8-valued common-gauge or double-coset
factorization.

Source: the user-provided *Prime-Marked Compatible Frames and the Remaining
Cases of Serre's Conjecture II* and the companion Wolfram Language audit
(10 August 2026); the source supports the statement and matrix model.
-/


namespace RiemannResearch.E8.BinaryIcosahedralFinite

abbrev F5 := Fin 5
abbrev M := F5 × F5 × F5 × F5

def a (x : M) : F5 := x.1
def b (x : M) : F5 := x.2.1
def c (x : M) : F5 := x.2.2.1
def d (x : M) : F5 := x.2.2.2

def mat (a b c d : F5) : M := (a, b, c, d)

def mul (x y : M) : M :=
  mat
    (a x * a y + b x * c y)
    (a x * b y + b x * d y)
    (c x * a y + d x * c y)
    (c x * b y + d x * d y)

instance : Mul M := ⟨mul⟩
instance : One M := ⟨mat 1 0 0 1⟩

def det (x : M) : F5 := a x * d x - b x * c x
def sl2 : Finset M := Finset.univ.filter (fun x => det x = 1)
def inv (x : M) : M := mat (d x) (-b x) (-c x) (a x)
def conj (x y : M) : M := x * y * inv x

def expand (gens current : Finset M) : Finset M :=
  current ∪ (current.product gens).image (fun p => p.1 * p.2)

def generated (gens : Finset M) : ℕ → Finset M
  | 0 => {1}
  | n + 1 => expand gens (generated gens n)

def u : M := mat 1 1 0 1
def i : M := mat 2 0 0 3
def j : M := mat 0 1 4 0

def q8 : Finset M := generated {i, j} 8

def binaryTetrahedral : Finset M :=
  sl2.filter (fun x => q8.image (conj x) = q8)

def binaryDihedral : Finset M := generated {u, i} 20
def overlap : Finset M := binaryTetrahedral ∩ binaryDihedral
def c4 : Finset M := generated {i} 4

def productSet : Finset M :=
  (binaryTetrahedral.product binaryDihedral).image (fun p => p.1 * p.2)

def mpow (x : M) : ℕ → M
  | 0 => 1
  | n + 1 => mpow x n * x

def elementOrder (x : M) : ℕ :=
  (((List.range 120).map Nat.succ).find? (fun n => mpow x n = 1)).getD 0

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
/-- Exact finite packet: orders, closure, overlap element orders, product
factorization, and the two fixed-field indices. -/
theorem packet :
    sl2.card = 120 ∧
    q8.card = 8 ∧
    expand {i, j} q8 = q8 ∧
    q8 ∩ sl2 = q8 ∧
    binaryTetrahedral.card = 24 ∧
    binaryDihedral.card = 20 ∧
    expand {u, i} binaryDihedral = binaryDihedral ∧
    binaryDihedral ∩ sl2 = binaryDihedral ∧
    overlap.card = 4 ∧
    (overlap.filter fun x => elementOrder x = 1).card = 1 ∧
    (overlap.filter fun x => elementOrder x = 2).card = 1 ∧
    (overlap.filter fun x => elementOrder x = 4).card = 2 ∧
    productSet = sl2 ∧
    productSet.card = 120 ∧
    sl2.card / binaryTetrahedral.card = 5 ∧
    sl2.card / binaryDihedral.card = 6 := by
  decide

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
/-- The four-element overlap is exactly the stabilized cyclic closure of
the order-four matrix `i`. -/
theorem overlap_is_c4 :
    overlap = c4 ∧ c4.card = 4 ∧ expand {i} c4 = c4 := by
  decide

end RiemannResearch.E8.BinaryIcosahedralFinite
