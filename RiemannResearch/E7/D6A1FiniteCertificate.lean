/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


/-!
# The E7 root system and D6 + A1 lattice glue

This model enumerates 126 distinct roots in coordinates scaled by two and
kernel-checks their squared scaled norm eight.  An algebraic rescaling lemma
then gives the exact rational norm two without reducing rational arithmetic
over the entire list.  The module also records the `D₆A₁` Gram matrix and
the half-spin glue vector.  The final exact-order-two theorem proves both
nonmembership of the glue vector and membership of its double in the `D₆A₁`
root lattice.  Reflection closure is not asserted here: direct
kernel reduction of all 15,876 pairs exceeds the verifier gateway budget.

These are root and lattice certificates; identifying the corresponding
algebraic subgroup and its Clifford-component label remains a separate
geometric construction.

Source: the user-provided Wolfram Language certificate
`serre_ii_wolfram_certificates.wl` (10 August 2026); the source supports
the coordinate model and target equalities.
-/

open Matrix

namespace RiemannResearch.E7.D6A1FiniteCertificate

abbrev I7 := Fin 7
abbrev Vec7 := I7 → ℚ
abbrev Vec7Scaled := I7 → ℤ

def scaledSigns2 : List ℤ := [-2, 2]
def scaledSigns1 : List ℤ := [-1, 1]

def scaledPairRoot (i j : ℕ) (si sj : ℤ) : Vec7Scaled :=
  fun k => if k.val = i then si else if k.val = j then sj else 0

def scaledD6Roots : List Vec7Scaled :=
  (List.range 6).flatMap fun i =>
    (List.range 6).flatMap fun j =>
      if i < j then
        scaledSigns2.flatMap fun si =>
          scaledSigns2.map fun sj => scaledPairRoot i j si sj
      else []

def scaledA1Root (s : ℤ) : Vec7Scaled :=
  fun k => if k.val = 6 then s else 0

def scaledA1Roots : List Vec7Scaled := scaledSigns2.map scaledA1Root

def scaledBitSign (n k : ℕ) : ℤ := if n.testBit k then -1 else 1

def scaledNegativeCount (n : ℕ) : ℕ :=
  ((List.range 6).filter fun k => n.testBit k).length

def scaledHalfRoot (n : ℕ) (t : ℤ) : Vec7Scaled :=
  fun k => if k.val < 6 then scaledBitSign n k.val else t

def scaledHalfRoots : List Vec7Scaled :=
  (List.range 64).flatMap fun n =>
    if scaledNegativeCount n % 2 = 1 then
      scaledSigns1.map (scaledHalfRoot n)
    else []

def e7ScaledRoots : List Vec7Scaled :=
  scaledD6Roots ++ scaledA1Roots ++ scaledHalfRoots

def e7ScaledDot (x y : Vec7Scaled) : ℤ :=
  ∑ i : I7, (if i.val = 6 then 2 else 1) * x i * y i

def unscale2 (x : Vec7Scaled) : Vec7 :=
  fun i => (x i : ℚ) / 2

def signs : List ℚ := [-1, 1]

def pairRoot (i j : ℕ) (si sj : ℚ) : Vec7 :=
  fun k => if k.val = i then si else if k.val = j then sj else 0

def d6Roots : List Vec7 :=
  (List.range 6).flatMap fun i =>
    (List.range 6).flatMap fun j =>
      if i < j then signs.flatMap fun si => signs.map fun sj => pairRoot i j si sj
      else []

def a1Root (s : ℚ) : Vec7 := fun k => if k.val = 6 then s else 0
def a1Roots : List Vec7 := signs.map a1Root

def bitSign (n k : ℕ) : ℚ := if n.testBit k then -1 else 1

def negativeCount (n : ℕ) : ℕ :=
  ((List.range 6).filter fun k => n.testBit k).length

def halfRoot (n : ℕ) (t : ℚ) : Vec7 :=
  fun k => if k.val < 6 then bitSign n k.val / 2 else t / 2

def halfRoots : List Vec7 :=
  (List.range 64).flatMap fun n =>
    if negativeCount n % 2 = 1 then signs.map (halfRoot n) else []

def e7Roots : List Vec7 := d6Roots ++ a1Roots ++ halfRoots

def e7Dot (x y : Vec7) : ℚ :=
  ∑ i : I7, (if i.val = 6 then 2 else 1) * x i * y i

theorem e7Dot_unscale2 (x y : Vec7Scaled) :
    e7Dot (unscale2 x) (unscale2 y) = (e7ScaledDot x y : ℚ) / 4 := by
  simp only [e7Dot, unscale2, e7ScaledDot]
  push_cast
  simp_rw [div_eq_mul_inv]
  ring_nf
  simp_rw [← Finset.sum_mul]

def e7Reflect (x a : Vec7) : Vec7 :=
  fun i => x i - (2 * e7Dot x a / e7Dot a a) * a i

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem e7_root_count : e7ScaledRoots.length = 126 := by
  decide

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem e7_roots_nodup : e7ScaledRoots.Nodup := by
  decide

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem e7_scaled_root_norms :
    e7ScaledRoots.Forall (fun x => e7ScaledDot x x = 8) := by
  decide

theorem e7_root_norms :
    (e7ScaledRoots.map unscale2).Forall (fun x => e7Dot x x = 2) := by
  rw [List.forall_map_iff]
  apply e7_scaled_root_norms.imp
  intro x hx
  change e7Dot (unscale2 x) (unscale2 x) = 2
  rw [e7Dot_unscale2, hx]
  norm_num

abbrev Mat7Z := Matrix I7 I7 ℤ

def d6a1SimpleRootsZ : Mat7Z := ![
  ![1,-1,0,0,0,0,0], ![0,1,-1,0,0,0,0],
  ![0,0,1,-1,0,0,0], ![0,0,0,1,-1,0,0],
  ![0,0,0,0,1,-1,0], ![0,0,0,0,1,1,0],
  ![0,0,0,0,0,0,1]]

/-- The numerator of the usual half-integral glue vector. -/
def e7GlueNumerator : Vec7Scaled := ![1,1,1,1,1,-1,1]

def e7GlueDoubleCoordinates : Vec7Scaled := ![1,2,3,4,3,2,1]

def InD6A1RootLattice (x : Vec7Scaled) : Prop :=
  ∃ z : Vec7Scaled, d6a1SimpleRootsZ.transpose.mulVec z = x

/-- The half-vector represented by x / 2 is in the root lattice exactly
when x belongs to twice the integral root lattice. -/
def InTwiceD6A1RootLattice (x : Vec7Scaled) : Prop :=
  ∃ z : Vec7Scaled,
    (fun i => 2 * (d6a1SimpleRootsZ.transpose.mulVec z) i) = x

set_option maxHeartbeats 0 in
-- The finite coordinate certificate needs an unrestricted reduction budget.
set_option maxRecDepth 100000 in
theorem e7Glue_double_coordinates :
    d6a1SimpleRootsZ.transpose.mulVec e7GlueDoubleCoordinates =
      e7GlueNumerator := by
  decide

theorem e7Glue_not_twice_mem :
    ¬ InTwiceD6A1RootLattice e7GlueNumerator := by
  rintro ⟨z, hz⟩
  have h0 := congrFun hz (0 : I7)
  have hdiv : (2 : ℤ) ∣ e7GlueNumerator 0 :=
    ⟨(d6a1SimpleRootsZ.transpose.mulVec z) 0, h0.symm⟩
  norm_num [e7GlueNumerator] at hdiv

/-- The half-spin numerator represents a nonzero class whose double is in
the D₆A₁ root lattice. -/
theorem e7Glue_has_exact_order_two :
    ¬ InTwiceD6A1RootLattice e7GlueNumerator ∧
      InD6A1RootLattice e7GlueNumerator := by
  exact ⟨e7Glue_not_twice_mem,
    ⟨e7GlueDoubleCoordinates, e7Glue_double_coordinates⟩⟩

/-- The labelled versions of the four sorted index triples permitted by the
trialitarian isotropy classification over fields with `I_q^3 = 0`.

This definition records the finite table; it does not assert that data
arising from an E7 group satisfy the table's isotropy hypothesis.

Source: F. K. Bingöl and A. Quéguiner-Mathieu,
*Triality over fields with I^3=0*, arXiv:2312.10442; the source supports the
classification table used in the research program. -/
def AllowedTrialitarianIndexTriple (a b c : ℕ) : Prop :=
  (a = 1 ∧ b = 1 ∧ c = 1) ∨
  ((a = 1 ∧ b = 2 ∧ c = 2) ∨
   (a = 2 ∧ b = 1 ∧ c = 2) ∨
   (a = 2 ∧ b = 2 ∧ c = 1)) ∨
  ((a = 1 ∧ b = 4 ∧ c = 4) ∨
   (a = 4 ∧ b = 1 ∧ c = 4) ∨
   (a = 4 ∧ b = 4 ∧ c = 1)) ∨
  (a = 2 ∧ b = 2 ∧ c = 2)

/-- The exact finite consequence used by Target E7-INDEX: if the labelled
`23` component has index four, one of the other two labelled components
has index one. -/
theorem index_four_forces_labelled_split
    {i12 i13 i23 : ℕ}
    (hallowed : AllowedTrialitarianIndexTriple i12 i13 i23)
    (h23 : i23 = 4) :
    i12 = 1 ∨ i13 = 1 := by
  subst i23
  rcases hallowed with h111 | h122 | h144 | h222
  · rcases h111 with ⟨_, _, h⟩
    norm_num at h
  · rcases h122 with h | h | h
    all_goals rcases h with ⟨_, _, h⟩
    all_goals norm_num at h
  · rcases h144 with h | h | h
    · exact Or.inl h.1
    · exact Or.inr h.2.1
    · norm_num at h
  · norm_num at h222

end RiemannResearch.E7.D6A1FiniteCertificate
