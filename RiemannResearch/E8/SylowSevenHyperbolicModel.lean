/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.E8.RationalInvolutionsAudit

/-!
# Sylow-seven hyperbolic-model certificates

The explicit 256-element quadratic-space computation and atomic partition
from the 27 July 2026 rational-involutions manuscript.
-/

namespace RiemannResearch.E8.RationalInvolutionsAudit

/-! ## The exact Sylow-seven hyperbolic model -/

def bitNat (b : Bool) : Nat := if b then 1 else 0

def dot3 (x y : Nat) : Bool :=
  (Nat.testBit x 0 && Nat.testBit y 0) ^^
  (Nat.testBit x 1 && Nat.testBit y 1) ^^
  (Nat.testBit x 2 && Nat.testBit y 2)

def q8 (v : Nat) : Bool :=
  dot3 v (v / 8) ^^ (Nat.testBit v 6 && Nat.testBit v 7)

def g7 (v : Nat) : Nat :=
  bitNat (Nat.testBit v 2) +
  2 * bitNat (Nat.testBit v 0 ^^ Nat.testBit v 2) +
  4 * bitNat (Nat.testBit v 1) +
  8 * bitNat (Nat.testBit v 3 ^^ Nat.testBit v 5) +
  16 * bitNat (Nat.testBit v 3) +
  32 * bitNat (Nat.testBit v 4) +
  64 * bitNat (Nat.testBit v 6) +
  128 * bitNat (Nat.testBit v 7)

def g7Pow (n v : Nat) : Nat := Nat.iterate g7 n v

def singular8B (v : Nat) : Bool :=
  decide (v ≠ 0 ∧ v < 256) && !q8 v

def orbit7 (v : Nat) : Finset Nat :=
  (Finset.range 7).image fun n => g7Pow n v

def orbitRepresentativeB (v : Nat) : Bool :=
  singular8B v && (List.range 7).all fun n => decide (v ≤ g7Pow n v)

def sevenOrbitRepresentativeB (v : Nat) : Bool :=
  orbitRepresentativeB v && decide ((orbit7 v).card = 7)

def orbitXor (v : Nat) : Nat :=
  (List.range 7).foldl (fun a n => Nat.xor a (g7Pow n v)) 0

def polar8 (v w : Nat) : Bool :=
  q8 (Nat.xor v w) ^^ q8 v ^^ q8 w

theorem sylowSeven_order :
    (∀ v : Fin 256, g7Pow 7 v.val = v.val) ∧
    (∀ i : Fin 7, i.val ≠ 0 →
      ∃ v : Fin 256, g7Pow i.val v.val ≠ v.val) := by
  set_option maxRecDepth 100000 in decide

theorem nonzero_singular_card :
    ((Finset.range 256).filter fun v => singular8B v = true).card = 135 := by
  set_option maxRecDepth 100000 in decide

theorem singular_fixed_points :
    ((Finset.range 256).filter fun v =>
      singular8B v = true ∧ g7 v = v) = {64, 128} := by
  set_option maxRecDepth 100000 in decide

theorem seven_orbit_representative_card :
    ((Finset.range 256).filter fun v =>
      sevenOrbitRepresentativeB v = true).card = 19 := by
  set_option maxRecDepth 100000 in decide

/-- Exact 5,5,5,4 orbit-sum distribution from equation (14.13). -/
theorem seven_orbit_sum_distribution :
    let reps := (Finset.range 256).filter fun v =>
      sevenOrbitRepresentativeB v = true
    (reps.filter fun v => orbitXor v = 0).card = 5 ∧
    (reps.filter fun v => orbitXor v = 64).card = 5 ∧
    (reps.filter fun v => orbitXor v = 128).card = 5 ∧
    (reps.filter fun v => orbitXor v = 192).card = 4 := by
  set_option maxRecDepth 100000 in decide

theorem balanced_orbits_orthogonal_to_r :
    ∀ v : Fin 256, sevenOrbitRepresentativeB v.val = true →
      orbitXor v.val = 0 →
      ∀ n : Fin 7, polar8 192 (g7Pow n.val v.val) = false := by
  set_option maxRecDepth 100000 in decide

/-! ## The 15 + 120 atomic partition in U plus U-dual -/

def atomicSingularB (v : Nat) : Bool :=
  decide (v ≠ 0 ∧ v < 256) && !dot4 v (v / 16)

def atomicSmallB (v : Nat) : Bool :=
  atomicSingularB v && decide (v < 16)

def atomicLargeB (v : Nat) : Bool :=
  atomicSingularB v && decide (16 ≤ v)

def listXor (s : List Nat) : Nat := s.foldl Nat.xor 0

theorem atomic_partition_card :
    let small := (Finset.range 256).filter fun v => atomicSmallB v = true
    let large := (Finset.range 256).filter fun v => atomicLargeB v = true
    let singular := (Finset.range 256).filter fun v => atomicSingularB v = true
    small.card = 15 ∧ large.card = 120 ∧
      small ∪ large = singular ∧ Disjoint small large := by
  set_option maxRecDepth 100000 in decide

theorem atomic_partition_vector_sums :
    listXor ((List.range 256).filter atomicSmallB) = 0 ∧
    listXor ((List.range 256).filter atomicLargeB) = 0 := by
  set_option maxRecDepth 100000 in decide

end RiemannResearch.E8.RationalInvolutionsAudit
