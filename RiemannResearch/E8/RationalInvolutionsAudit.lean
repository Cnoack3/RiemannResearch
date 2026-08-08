/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Rational involutions and hidden Weyl-7: exact audit

This module kernel-checks the self-contained arithmetic, binary linear-algebra,
and formal group-theoretic parts of the paper *Rational Involutions and Hidden
Weyl-7 Monodromy toward Serre's Conjecture II for E8* (27 July 2026).

The declarations below correspond to the exact calculations in Proposition
16.1, the no-go argument of Proposition 10.7, the odd-degree argument of
Theorem 10.35, and the affine-fiber statement behind Theorem 10.51. They do
not package the paper's algebraic-group, Galois-cohomological, or
packet-compatibility inputs as axioms.
-/

namespace RiemannResearch.E8.RationalInvolutionsAudit

/-! ## The 15 by 15 complement-incidence matrix -/

def dot4 (x y : Nat) : Bool :=
  (Nat.testBit x 0 && Nat.testBit y 0) ^^
  (Nat.testBit x 1 && Nat.testBit y 1) ^^
  (Nat.testBit x 2 && Nat.testBit y 2) ^^
  (Nat.testBit x 3 && Nat.testBit y 3)

def incidenceEntry (i j : Fin 15) : ℤ :=
  if dot4 (i.val + 1) (j.val + 1) then 1 else 0

theorem incidence_row_sum :
    ∀ i : Fin 15, ∑ j : Fin 15, incidenceEntry i j = 8 := by
  set_option maxRecDepth 100000 in decide

/-- Exact Gram identity B B-transpose = 4 (I + J), entry by entry. -/
theorem incidence_gram :
    ∀ i j : Fin 15,
      ∑ u : Fin 15, incidenceEntry i u * incidenceEntry j u =
        if i = j then 8 else 4 := by
  set_option maxRecDepth 100000 in decide

theorem incidence_trace :
    ∑ i : Fin 15, incidenceEntry i i = 8 := by
  set_option maxRecDepth 100000 in decide

/-! ## Printed binary certificates -/

theorem tits_binary_certificate :
    Nat.xor (Nat.xor (Nat.xor (Nat.xor 0x10024 0x88) 0xfe) 0x9600) 0x9652 =
      0x10000 := by
  set_option maxRecDepth 100000 in decide

/-- The printed decimal right side of (14.4) is 2^32. -/
theorem s4_overlap_binary_certificate :
    Nat.xor (Nat.xor (Nat.xor (Nat.xor 169 118) 222) 43374) 4295010671 =
      2 ^ 32 := by
  set_option maxRecDepth 100000 in decide

theorem kleinFour_binary_certificate :
    Nat.xor (Nat.xor 168 42240) 107944 = 2 ^ 16 := by
  set_option maxRecDepth 100000 in decide

/-! ## Integral degree-56 defect and dimension arithmetic -/

def degree56OrbitDeterminant (c1 c2 c3 c4 : ℤ) : ℤ :=
  -16 * (c2 - 2 * c3) ^ 3 * (c2 - c4) ^ 3 * (3 * c2 - c4) *
    (-4 * c1 + c2 + 2 * c3 + 2 * c4)

theorem degree56OrbitDeterminant_divisible_by_sixteen
    (c1 c2 c3 c4 : ℤ) :
    16 ∣ degree56OrbitDeterminant c1 c2 c3 c4 := by
  refine ⟨-((c2 - 2 * c3) ^ 3 * (c2 - c4) ^ 3 * (3 * c2 - c4) *
    (-4 * c1 + c2 + 2 * c3 + 2 * c4)), ?_⟩
  simp [degree56OrbitDeterminant]
  ring

theorem degree56OrbitDeterminant_minimizer :
    degree56OrbitDeterminant (-1) (-1) 0 (-2) = 16 := by
  norm_num [degree56OrbitDeterminant]

theorem cartanTransporter_dimension_arithmetic :
    248 * 247 / 2 = 30628 ∧
    120 * 119 / 2 + 128 * 127 / 2 = 15268 ∧
    15268 + 128 = 15396 ∧
    30628 - 15396 = 15232 ∧
    15268 - 120 = 15148 := by
  norm_num

theorem cartanTransporter_cubicEquation_count :
    (120 * 119 / 2) * 128 + (128 * 127 * 126 / 6) = 1255296 := by
  norm_num

/-- Arithmetic consistency of tables (14.2), (14.6), (14.8), and (14.11). -/
theorem finiteCohomology_rank_arithmetic :
    8 - 7 = 1 ∧ 7 - 7 = 0 ∧ 8 - 8 = 0 ∧
    10 - 5 = 5 ∧ 8 - 6 = 2 ∧
    5 + 3 = 8 ∧ 2 + 2 = 4 ∧
    4232 - 4054 - 176 = 2 ∧
    72 - 52 - 16 = 4 ∧
    8 - 6 = 2 := by
  norm_num

theorem packetStabilizer_order_arithmetic :
    20160 / 15 = 1344 ∧
    20160 / 35 = 576 ∧
    16 * (6 * 6) = 576 ∧
    16 * 360 = 5760 ∧
    5760 = 10 * 576 := by
  norm_num

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

/-! ## Formal structural arguments -/

/-- Proposition 10.7. -/
theorem commutative_of_two_factor_norm
    {G : Type*} [Group G] (N : G × G →* G)
    (hleft : ∀ g : G, N (g, 1) = g)
    (hright : ∀ g : G, N (1, g) = g) :
    ∀ g h : G, g * h = h * g := by
  intro g h
  calc
    g * h = N (g, 1) * N (1, h) := by rw [hleft, hright]
    _ = N ((g, 1) * (1, h)) := (N.map_mul (g, 1) (1, h)).symm
    _ = N ((1, h) * (g, 1)) := by simp
    _ = N (1, h) * N (g, 1) := N.map_mul (1, h) (g, 1)
    _ = h * g := by rw [hleft, hright]

theorem no_two_factor_norm_of_noncommuting
    {G : Type*} [Group G] (g h : G) (hne : g * h ≠ h * g) :
    ¬ ∃ N : G × G →* G,
      (∀ x : G, N (x, 1) = x) ∧ (∀ x : G, N (1, x) = x) := by
  rintro ⟨N, hleft, hright⟩
  exact hne (commutative_of_two_factor_norm N hleft hright g h)

/-- Additive restriction-corestriction form of Theorem 10.35. -/
theorem odd_degree_restriction_injective_mod_two
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (res : A →+ B) (cor : B →+ A) {d : ℕ}
    (hindex : ∀ x, cor (res x) = d • x) (hodd : Odd d)
    {x : A} (hres : ∃ y : B, res x = 2 • y) :
    ∃ z : A, x = 2 • z := by
  obtain ⟨q, rfl⟩ := hodd
  obtain ⟨y, hy⟩ := hres
  refine ⟨cor y - q • x, ?_⟩
  have hcor : (2 * q + 1) • x = 2 • cor y := by
    rw [← hindex x, hy, map_nsmul]
  simp only [add_nsmul, one_nsmul, mul_nsmul] at hcor
  have hs : q • 2 • x = 2 • q • x := by
    rw [← mul_nsmul, ← mul_nsmul, Nat.mul_comm]
  rw [hs] at hcor
  have hx : x = 2 • cor y - 2 • q • x :=
    eq_sub_iff_add_eq'.2 hcor
  calc
    x = 2 • cor y - 2 • q • x := hx
    _ = 2 • (cor y - q • x) := by
      simp only [two_nsmul]
      abel

/-- The affine-fiber statement behind Theorem 10.51. -/
theorem boundary_fiber_is_kernel_torsor
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (boundary : A →+ B) (e : B) (x : A) (hx : boundary x = e) :
    ∀ y : A, boundary y = e ↔
      ∃! k : boundary.ker, y = x + (k : A) := by
  intro y
  constructor
  · intro hy
    let k : boundary.ker := ⟨y - x, by
      simp [AddMonoidHom.mem_ker, map_sub, hy, hx]⟩
    refine ⟨k, ?_, ?_⟩
    · change y = x + (y - x)
      abel
    · intro k' hk'
      apply Subtype.ext
      change (k' : A) = y - x
      rw [hk']
      abel
  · rintro ⟨k, hk, -⟩
    rw [hk, map_add, hx]
    simp [AddMonoidHom.mem_ker.mp k.property]

end RiemannResearch.E8.RationalInvolutionsAudit
