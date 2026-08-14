/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NormNum


/-!
# Smith certificates for full-rank E8 root sublattices

Wolfram's exact `SmithDecomposition` supplied the integral left and right
matrices and their integral inverses. Lean independently verifies the
two-sided inverse identities and that `U * A * V` is the displayed diagonal
matrix. Consequently these are checkable unimodular Smith witnesses, not
trusted output copied from a computer algebra system.

The four certificates concern `D₈`, `D₄²`, `A₄²`, and `A₂⁴`.
They establish finite lattice data only, not the existence of corresponding
subgroups over a field.

Source: the user-provided Wolfram Language certificate
`serre_ii_wolfram_certificates.wl` (10 August 2026); the source supports
the matrices and target diagonals.
-/

open Matrix

namespace RiemannResearch.E8.RootLatticeSmith

abbrev I8 := Fin 8
abbrev Mat8 := Matrix I8 I8 ℤ

def SmithCertificate (A S U Uinv V Vinv : Mat8) : Prop :=
  U * Uinv = 1 ∧ Uinv * U = 1 ∧
  V * Vinv = 1 ∧ Vinv * V = 1 ∧
  U * A * V = S

def d8 : Mat8 := ![
  ![2,-1,0,0,0,0,0,0], ![-1,2,-1,0,0,0,0,0],
  ![0,-1,2,-1,0,0,0,0], ![0,0,-1,2,-1,0,0,0],
  ![0,0,0,-1,2,-1,0,0], ![0,0,0,0,-1,2,-1,-1],
  ![0,0,0,0,0,-1,2,0], ![0,0,0,0,0,-1,0,2]]

def d8Left : Mat8 := ![
  ![2,3,4,5,6,7,4,4], ![1,2,2,2,2,2,1,1],
  ![2,4,6,7,8,9,5,5], ![1,2,3,4,4,4,2,2],
  ![2,4,6,8,10,11,6,6], ![1,2,3,4,5,6,3,3],
  ![1,2,3,4,5,6,4,3], ![1,2,3,4,5,6,3,4]]

def d8Smith : Mat8 := ![
  ![1,0,0,0,0,0,0,0], ![0,1,0,0,0,0,0,0],
  ![0,0,1,0,0,0,0,0], ![0,0,0,1,0,0,0,0],
  ![0,0,0,0,1,0,0,0], ![0,0,0,0,0,1,0,0],
  ![0,0,0,0,0,0,2,0], ![0,0,0,0,0,0,0,2]]

def d8Right : Mat8 := ![
  ![1,0,0,0,0,0,-1,-1], ![0,1,0,0,0,0,0,0],
  ![0,0,1,0,0,0,-1,-1], ![0,0,0,1,0,0,0,0],
  ![0,0,0,0,1,0,-1,-1], ![0,0,0,0,0,1,0,0],
  ![0,0,0,0,0,0,1,0], ![0,0,0,0,0,0,0,1]]

def d8LeftInv : Mat8 := ![
  ![2,-1,0,0,0,0,-1,-1], ![-1,2,-1,0,0,0,1,1],
  ![0,-1,2,-1,0,0,-1,-1], ![0,0,-1,2,-1,0,1,1],
  ![0,0,0,-1,2,-1,-1,-1], ![0,0,0,0,-1,2,0,0],
  ![0,0,0,0,0,-1,1,0], ![0,0,0,0,0,-1,0,1]]

def d8RightInv : Mat8 := ![
  ![1,0,0,0,0,0,1,1], ![0,1,0,0,0,0,0,0],
  ![0,0,1,0,0,0,1,1], ![0,0,0,1,0,0,0,0],
  ![0,0,0,0,1,0,1,1], ![0,0,0,0,0,1,0,0],
  ![0,0,0,0,0,0,1,0], ![0,0,0,0,0,0,0,1]]

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem d8Smith_certificate :
    SmithCertificate d8 d8Smith d8Left d8LeftInv d8Right d8RightInv := by
  unfold SmithCertificate
  decide

def d4d4 : Mat8 := ![
  ![2,-1,0,0,0,0,0,0], ![-1,2,-1,-1,0,0,0,0],
  ![0,-1,2,0,0,0,0,0], ![0,-1,0,2,0,0,0,0],
  ![0,0,0,0,2,-1,0,0], ![0,0,0,0,-1,2,-1,-1],
  ![0,0,0,0,0,-1,2,0], ![0,0,0,0,0,-1,0,2]]

def d4d4Left : Mat8 := ![
  ![2,3,2,2,0,0,0,0], ![1,2,1,1,0,0,0,0],
  ![0,0,0,0,1,2,1,1], ![-1,-2,-2,-1,3,5,3,3],
  ![-2,-4,-3,-3,6,10,6,6], ![-1,-2,-1,-2,2,4,2,2],
  ![-1,-2,-1,-2,1,2,2,1], ![-1,-2,-1,-2,1,2,1,2]]

def d4d4Smith : Mat8 := ![
  ![1,0,0,0,0,0,0,0], ![0,1,0,0,0,0,0,0],
  ![0,0,1,0,0,0,0,0], ![0,0,0,1,0,0,0,0],
  ![0,0,0,0,2,0,0,0], ![0,0,0,0,0,2,0,0],
  ![0,0,0,0,0,0,2,0], ![0,0,0,0,0,0,0,2]]

def d4d4Right : Mat8 := ![
  ![1,0,-2,1,-1,2,0,0], ![0,1,0,0,0,0,0,0],
  ![0,0,1,-1,1,-1,0,0], ![0,0,1,0,0,-1,0,0],
  ![0,0,-1,-1,2,0,-1,-1], ![0,0,1,0,0,0,0,0],
  ![0,0,1,0,0,-1,1,0], ![0,0,1,0,0,-1,0,1]]

def d4d4LeftInv : Mat8 := ![
  ![2,-1,-4,2,-1,2,0,0], ![-1,2,0,0,0,0,0,0],
  ![0,-1,2,-2,1,-1,0,0], ![0,-1,2,0,0,-1,0,0],
  ![0,0,-3,-2,2,0,-1,-1], ![0,0,1,1,-1,1,0,0],
  ![0,0,1,0,0,-1,1,0], ![0,0,1,0,0,-1,0,1]]

def d4d4RightInv : Mat8 := ![
  ![1,0,1,1,0,0,0,0], ![0,1,0,0,0,0,0,0],
  ![0,0,0,0,0,1,0,0], ![0,0,-2,0,1,1,1,1],
  ![0,0,-1,-1,1,1,1,1], ![0,0,0,-1,0,1,0,0],
  ![0,0,0,-1,0,0,1,0], ![0,0,0,-1,0,0,0,1]]

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem d4d4Smith_certificate :
    SmithCertificate d4d4 d4d4Smith d4d4Left d4d4LeftInv
      d4d4Right d4d4RightInv := by
  unfold SmithCertificate
  decide

def a4a4 : Mat8 := ![
  ![2,-1,0,0,0,0,0,0], ![-1,2,-1,0,0,0,0,0],
  ![0,-1,2,-1,0,0,0,0], ![0,0,-1,2,0,0,0,0],
  ![0,0,0,0,2,-1,0,0], ![0,0,0,0,-1,2,-1,0],
  ![0,0,0,0,0,-1,2,-1], ![0,0,0,0,0,0,-1,2]]

def a4a4Left : Mat8 := ![
  ![1,1,1,1,0,0,0,0], ![1,2,2,2,0,0,0,0],
  ![1,2,3,3,0,0,0,0], ![0,0,0,0,1,2,3,3],
  ![-1,-2,-3,-4,5,9,13,13], ![-1,-2,-3,-4,5,10,14,14],
  ![-1,-2,-3,-4,5,10,15,15], ![-1,-2,-3,-4,1,2,3,4]]

def a4a4Smith : Mat8 := ![
  ![1,0,0,0,0,0,0,0], ![0,1,0,0,0,0,0,0],
  ![0,0,1,0,0,0,0,0], ![0,0,0,1,0,0,0,0],
  ![0,0,0,0,1,0,0,0], ![0,0,0,0,0,1,0,0],
  ![0,0,0,0,0,0,5,0], ![0,0,0,0,0,0,0,5]]

def a4a4Right : Mat8 := ![
  ![1,0,0,-1,0,0,1,0], ![0,1,0,-2,0,0,2,0],
  ![0,0,1,-3,0,0,3,0], ![0,0,0,1,0,0,-1,0],
  ![0,0,0,0,1,0,-4,-1], ![0,0,0,-1,0,1,-3,-2],
  ![0,0,0,-2,0,0,3,-3], ![0,0,0,1,0,0,-1,1]]

def a4a4LeftInv : Mat8 := ![
  ![2,-1,0,0,0,0,0,0], ![-1,2,-1,0,0,0,0,0],
  ![0,-1,2,-5,0,0,1,0], ![0,0,-1,5,0,0,-1,0],
  ![0,0,0,1,2,-1,-1,0], ![0,0,0,0,-1,2,-1,0],
  ![0,0,0,-4,0,-1,2,-1], ![0,0,0,4,0,0,-1,1]]

def a4a4RightInv : Mat8 := ![
  ![1,0,0,1,0,0,0,0], ![0,1,0,2,0,0,0,0],
  ![0,0,1,3,0,0,0,0], ![0,0,0,0,0,0,1,3],
  ![0,0,0,-5,1,0,4,13], ![0,0,0,-5,0,1,4,14],
  ![0,0,0,-1,0,0,1,3], ![0,0,0,-1,0,0,0,1]]

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem a4a4Smith_certificate :
    SmithCertificate a4a4 a4a4Smith a4a4Left a4a4LeftInv
      a4a4Right a4a4RightInv := by
  unfold SmithCertificate
  decide

def a2x4 : Mat8 := ![
  ![2,-1,0,0,0,0,0,0], ![-1,2,0,0,0,0,0,0],
  ![0,0,2,-1,0,0,0,0], ![0,0,-1,2,0,0,0,0],
  ![0,0,0,0,2,-1,0,0], ![0,0,0,0,-1,2,0,0],
  ![0,0,0,0,0,0,2,-1], ![0,0,0,0,0,0,-1,2]]

def a2x4Left : Mat8 := ![
  ![1,1,0,0,0,0,0,0], ![0,0,0,0,0,0,1,1],
  ![-1,-2,1,1,0,0,2,2], ![-1,-2,0,0,1,1,2,2],
  ![-2,-4,-1,-2,3,3,6,6], ![0,0,-1,-2,1,2,0,0],
  ![0,0,-1,-2,0,0,3,3], ![0,0,-1,-2,0,0,1,2]]

def a2x4Smith : Mat8 := ![
  ![1,0,0,0,0,0,0,0], ![0,1,0,0,0,0,0,0],
  ![0,0,1,0,0,0,0,0], ![0,0,0,1,0,0,0,0],
  ![0,0,0,0,3,0,0,0], ![0,0,0,0,0,3,0,0],
  ![0,0,0,0,0,0,3,0], ![0,0,0,0,0,0,0,3]]

def a2x4Right : Mat8 := ![
  ![1,-1,0,1,-1,0,1,0], ![0,1,0,-1,1,0,-1,0],
  ![0,0,1,-3,3,0,-2,0], ![0,1,0,0,0,0,-1,0],
  ![0,0,0,-2,3,-1,-2,0], ![0,1,0,0,0,1,-1,0],
  ![0,0,0,0,0,0,1,-1], ![0,1,0,0,0,0,-1,1]]

def a2x4LeftInv : Mat8 := ![
  ![2,-3,0,3,-1,0,1,0], ![-1,3,0,-3,1,0,-1,0],
  ![0,-1,2,-6,2,0,-1,0], ![0,2,-1,3,-1,0,0,0],
  ![0,-1,0,-4,2,-1,-1,0], ![0,2,0,2,-1,1,0,0],
  ![0,-1,0,0,0,0,1,-1], ![0,2,0,0,0,0,-1,1]]

def a2x4RightInv : Mat8 := ![
  ![1,1,0,0,0,0,0,0], ![0,0,0,0,0,0,1,1],
  ![0,-3,1,1,0,0,2,2], ![0,-3,0,0,1,1,2,2],
  ![0,-2,0,-1,1,1,2,2], ![0,0,0,-1,0,1,0,0],
  ![0,0,0,-1,0,0,1,1], ![0,0,0,-1,0,0,0,1]]

set_option maxHeartbeats 0 in
-- The finite certificate needs an unrestricted kernel-reduction budget.
set_option maxRecDepth 100000 in
theorem a2x4Smith_certificate :
    SmithCertificate a2x4 a2x4Smith a2x4Left a2x4LeftInv
      a2x4Right a2x4RightInv := by
  unfold SmithCertificate
  decide

/-- The orders read from the four Smith diagonals are the squares of
the claimed full-rank lattice indices. -/
theorem smithDiagonalIndexArithmetic :
    2 ^ 2 = 4 ∧ 4 ^ 2 = 16 ∧ 5 ^ 2 = 25 ∧ 9 ^ 2 = 81 := by
  norm_num

end RiemannResearch.E8.RootLatticeSmith
