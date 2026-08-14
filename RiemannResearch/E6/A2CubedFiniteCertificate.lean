/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


/-!
# E6 roots, the minuscule 27, and signed S3 symmetry

Using weights scaled by three, this module enumerates the 72 E6 roots and
27 minuscule weights, proves their exact unscaled rational norms, exhausts
all six permutations of the three A2 factors, and checks the simultaneous
duality rule. A permutation preserves the chosen 27 exactly when the
duality sign equals its inversion parity; the opposite sign sends the 27
to its dual.

The final computation proves that the three displayed central characters
have common kernel exactly the diagonal copy of mu3. These are finite
root/weight certificates and do not construct an oriented A2-cubed frame
over a field.

Source: the user-provided Wolfram Language certificate
`serre_ii_wolfram_certificates.wl` (10 August 2026); the source supports
the coordinate model and target equalities.
-/

namespace RiemannResearch.E6.A2CubedFiniteCertificate

abbrev I3 := Fin 3
abbrev Vec3 := I3 → ℤ
abbrev TripleVec := I3 → Vec3
abbrev Perm3 := I3 → I3

def a2Weight3 (i : I3) : Vec3 := fun j => if j = i then 2 else -1
def a2Weights3 : List Vec3 := List.ofFn a2Weight3

def a2Roots3 : List Vec3 :=
  a2Weights3.flatMap fun x =>
    a2Weights3.flatMap fun y => if x = y then [] else [x - y]

def factorRoot (b : I3) (r : Vec3) : TripleVec :=
  fun c => if c = b then r else 0

def factorRoots : List TripleVec :=
  (List.ofFn fun b : I3 => b).flatMap fun b =>
    a2Roots3.map (factorRoot b)

def tensorWeights : List TripleVec :=
  a2Weights3.flatMap fun x =>
    a2Weights3.flatMap fun y =>
      a2Weights3.map fun z => ![x,y,z]

def e6Roots3 : List TripleVec :=
  factorRoots ++ tensorWeights ++ tensorWeights.map (- ·)

def weights12 : List TripleVec :=
  a2Weights3.flatMap fun x => a2Weights3.map fun y => ![x,-y,0]

def weights23 : List TripleVec :=
  a2Weights3.flatMap fun y => a2Weights3.map fun z => ![0,y,-z]

def weights31 : List TripleVec :=
  a2Weights3.flatMap fun x => a2Weights3.map fun z => ![-x,0,z]

def weights27_3 : List TripleVec := weights12 ++ weights23 ++ weights31

def dot3 (x y : TripleVec) : ℤ :=
  ∑ b : I3, ∑ i : I3, x b i * y b i

def permsWithParity : List (Perm3 × ℤ) := [
  (![0,1,2],1), (![0,2,1],-1), (![1,0,2],-1),
  (![1,2,0],1), (![2,0,1],1), (![2,1,0],-1)]

def permutationFunctions : List Perm3 := permsWithParity.map Prod.fst

def inversionCount (p : Perm3) : ℕ :=
  (((Finset.univ : Finset I3) ×ˢ (Finset.univ : Finset I3)).filter
    fun ij => ij.1 < ij.2 ∧ p ij.2 < p ij.1).card

def permutationParity (p : Perm3) : ℤ :=
  if inversionCount p % 2 = 0 then 1 else -1

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem permutationFunctions_nodup : permutationFunctions.Nodup := by
  decide

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem permutationFunctions_exhaust :
    ∀ p : Perm3, Function.Bijective p ↔ p ∈ permutationFunctions := by
  decide

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem permsWithParity_correct :
    permsWithParity.Forall fun pp => permutationParity pp.1 = pp.2 := by
  decide

def signs : List ℤ := [-1,1]

def signedAct (p : Perm3) (s : ℤ) (x : TripleVec) : TripleVec :=
  fun b => s • x (p b)

abbrev sameSet (xs ys : List TripleVec) : Prop :=
  xs.toFinset = ys.toFinset

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem e6_root_count : e6Roots3.length = 72 := by
  decide

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem e6_roots_nodup : e6Roots3.Nodup := by
  decide

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem e6_scaled_root_norms :
    e6Roots3.Forall (fun x => dot3 x x = 18) := by
  decide

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem e6_weight_count : weights27_3.length = 27 := by
  decide

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem e6_weights_nodup : weights27_3.Nodup := by
  decide

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem e6_scaled_weight_norms :
    weights27_3.Forall (fun x => dot3 x x = 12) := by
  decide

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem signed_permutations_preserve_roots :
    permsWithParity.Forall fun pp =>
      signs.Forall fun s =>
        sameSet (e6Roots3.map (signedAct pp.1 s)) e6Roots3 := by
  decide

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem preserves_27_iff_sign_eq_parity :
    permsWithParity.Forall fun pp =>
      signs.Forall fun s =>
        sameSet (weights27_3.map (signedAct pp.1 s)) weights27_3 ↔
          s = pp.2 := by
  decide

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem sends_27_to_dual_iff_sign_neg_parity :
    permsWithParity.Forall fun pp =>
      signs.Forall fun s =>
        sameSet (weights27_3.map (signedAct pp.1 s))
            (weights27_3.map (- ·)) ↔ s = -pp.2 := by
  decide

abbrev TripleVecQ := I3 → I3 → ℚ

def unscale3 (x : TripleVec) : TripleVecQ :=
  fun b i => (x b i : ℚ) / 3

def dotQ (x y : TripleVecQ) : ℚ :=
  ∑ b : I3, ∑ i : I3, x b i * y b i

theorem dotQ_unscale3 (x : TripleVec) :
    dotQ (unscale3 x) (unscale3 x) = (dot3 x x : ℚ) / 9 := by
  simp only [dotQ, unscale3, dot3]
  push_cast
  ring_nf
  rw [Finset.sum_mul]
  congr 1
  funext b
  rw [Finset.sum_mul]

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem e6_root_norms :
    (e6Roots3.map unscale3).Forall (fun x => dotQ x x = 2) := by
  rw [List.forall_map_iff]
  apply e6_scaled_root_norms.imp
  intro x hx
  change dotQ (unscale3 x) (unscale3 x) = 2
  rw [dotQ_unscale3, hx]
  norm_num

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem e6_weight_norms :
    (weights27_3.map unscale3).Forall (fun x => dotQ x x = 4/3) := by
  rw [List.forall_map_iff]
  apply e6_scaled_weight_norms.imp
  intro x hx
  change dotQ (unscale3 x) (unscale3 x) = 4/3
  rw [dotQ_unscale3, hx]
  norm_num

abbrev Mu3Triple := I3 → ZMod 3

def centerElements : List (ZMod 3) := [0,1,2]

def centerTriples : List Mu3Triple :=
  centerElements.flatMap fun a =>
    centerElements.flatMap fun b =>
      centerElements.map fun c => ![a,b,c]

def centralCharacters : List Mu3Triple :=
  [![1,2,0], ![0,1,2], ![2,0,1]]

def centralValue (chi z : Mu3Triple) : ZMod 3 :=
  ∑ i : I3, chi i * z i

def commonCentralKernel : List Mu3Triple :=
  centerTriples.filter fun z =>
    centralCharacters.all fun chi => centralValue chi z = 0

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem centerTriples_nodup : centerTriples.Nodup := by
  decide

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem centerTriples_card : centerTriples.length = 27 := by
  decide

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem commonCentralKernel_eq_diagonal :
    commonCentralKernel = [![0,0,0], ![1,1,1], ![2,2,2]] := by
  decide

end RiemannResearch.E6.A2CubedFiniteCertificate
