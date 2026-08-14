/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Cartan
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# The combinatorial D4 triality layer

This file is the dependency-neutral triality foundation shared by the type-D
and E8 branches. It formalizes the part of triality visible on the Dynkin
diagram:

* the three outer labels `V`, `S+`, and `S-`;
* the faithful `S3` action fixing the central node;
* preservation of the D4 Cartan matrix;
* explicit order-three and order-two generators; and
* canonical coordinate presentations of `D4 x D4` in the two orderings used
  by the E8 finite certificates.

The labels are semantic names only. This module does **not** construct the
vector or half-spin representations of `Spin(8)`, an algebraic group scheme,
a lift of a diagram symmetry to that group scheme, or Galois/fpqc descent.
`DiagramDescent` then classifies the image of any supplied abstract group
action by its order. It does not construct a Galois action, identify such an
action with an algebraic form, or perform effective descent.

Schaposnik--Schulz, *Triality for Homogeneous Polynomials*, Section 2,
https://arxiv.org/abs/2009.13573, supports the terminology: the three external
nodes correspond to the vector and two spin representations, and the diagram
symmetry group is `S3`. The declarations below are independent finite Lean
proofs of the displayed combinatorics.
-/

open Matrix

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

/-- Labels for the three outer nodes of D4. No representations are
constructed by this datatype. -/
inductive TrialityLabel where
  | vector
  | halfSpinPlus
  | halfSpinMinus
  deriving DecidableEq, Repr

/-- The chosen order `V, S+, S-` on the three outer labels. -/
def finThreeEquivLabel : Fin 3 ≃ TrialityLabel where
  toFun := ![.vector, .halfSpinPlus, .halfSpinMinus]
  invFun
    | .vector => 0
    | .halfSpinPlus => 1
    | .halfSpinMinus => 2
  left_inv i := by fin_cases i <;> rfl
  right_inv label := by cases label <;> rfl

instance : Fintype TrialityLabel :=
  Fintype.ofEquiv (Fin 3) finThreeEquivLabel

theorem card_trialityLabel : Fintype.card TrialityLabel = 3 := by
  decide

/-- The central node and the three labelled outer nodes of D4. -/
inductive Node where
  | central
  | outer (label : TrialityLabel)
  deriving DecidableEq, Repr

/-- The node type is canonically `Option TrialityLabel`. -/
def nodeEquivOption : Node ≃ Option TrialityLabel where
  toFun
    | .central => none
    | .outer label => some label
  invFun
    | none => .central
    | some label => .outer label
  left_inv node := by cases node <;> rfl
  right_inv node := by cases node <;> rfl

instance : Fintype Node :=
  Fintype.ofEquiv (Option TrialityLabel) nodeEquivOption.symm

theorem card_node : Fintype.card Node = 4 := by
  decide

/-- The full permutation group on the three outer labels. -/
abbrev DiagramSymmetry := Equiv.Perm TrialityLabel

/-- Extend a permutation of the outer labels by fixing the central node. -/
def diagramPerm (σ : DiagramSymmetry) : Equiv.Perm Node where
  toFun
    | .central => .central
    | .outer label => .outer (σ label)
  invFun
    | .central => .central
    | .outer label => .outer (σ.symm label)
  left_inv node := by cases node <;> simp
  right_inv node := by cases node <;> simp

/-- The `S3` action on all four D4 nodes. -/
def diagramAction : DiagramSymmetry →* Equiv.Perm Node where
  toFun := diagramPerm
  map_one' := by
    ext node
    cases node <;> rfl
  map_mul' σ τ := by
    ext node
    cases node <;> rfl

theorem diagramAction_injective : Function.Injective diagramAction := by
  intro σ τ h
  apply Equiv.ext
  intro label
  have hlabel := DFunLike.congr_fun h (Node.outer label)
  exact Node.outer.inj hlabel

theorem card_diagramSymmetry : Fintype.card DiagramSymmetry = 6 := by
  decide

/-- The simply-laced D4 Cartan matrix on semantically labelled nodes. -/
def cartan : Matrix Node Node ℤ
  | .central, .central => 2
  | .central, .outer _ => -1
  | .outer _, .central => -1
  | .outer left, .outer right => if left = right then 2 else 0

@[simp] theorem cartan_diagramAction
    (σ : DiagramSymmetry) (i j : Node) :
    cartan (diagramAction σ i) (diagramAction σ j) = cartan i j := by
  cases i <;> cases j <;>
    simp [diagramAction, diagramPerm, cartan]

/-- Mathlib's D4 order: `V, central, S+, S-`. -/
def finFourEquivNode : Fin 4 ≃ Node where
  toFun :=
    ![.outer .vector, .central, .outer .halfSpinPlus, .outer .halfSpinMinus]
  invFun
    | .central => 1
    | .outer .vector => 0
    | .outer .halfSpinPlus => 2
    | .outer .halfSpinMinus => 3
  left_inv i := by fin_cases i <;> rfl
  right_inv node := by
    cases node with
    | central => rfl
    | outer label => cases label <;> rfl

/-- The labelled matrix, transported to Mathlib's `Fin 4` indexing. -/
def cartanFinFour : Matrix (Fin 4) (Fin 4) ℤ :=
  fun i j => cartan (finFourEquivNode i) (finFourEquivNode j)

theorem cartanFinFour_eq_mathlib : cartanFinFour = CartanMatrix.D 4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The order-three cycle `V -> S+ -> S- -> V`. -/
def trialityCycle : DiagramSymmetry where
  toFun
    | .vector => .halfSpinPlus
    | .halfSpinPlus => .halfSpinMinus
    | .halfSpinMinus => .vector
  invFun
    | .vector => .halfSpinMinus
    | .halfSpinPlus => .vector
    | .halfSpinMinus => .halfSpinPlus
  left_inv label := by cases label <;> rfl
  right_inv label := by cases label <;> rfl

@[simp] theorem trialityCycle_vector :
    trialityCycle .vector = .halfSpinPlus := rfl

@[simp] theorem trialityCycle_halfSpinPlus :
    trialityCycle .halfSpinPlus = .halfSpinMinus := rfl

@[simp] theorem trialityCycle_halfSpinMinus :
    trialityCycle .halfSpinMinus = .vector := rfl

theorem trialityCycle_cubed : trialityCycle ^ 3 = 1 := by
  decide

theorem trialityCycle_ne_one : trialityCycle ≠ 1 := by
  decide

theorem orderOf_trialityCycle : orderOf trialityCycle = 3 :=
  orderOf_eq_prime trialityCycle_cubed trialityCycle_ne_one

/-- The involution fixing `V` and exchanging `S+` with `S-`. -/
def halfSpinSwap : DiagramSymmetry :=
  Equiv.swap .halfSpinPlus .halfSpinMinus

theorem halfSpinSwap_squared : halfSpinSwap ^ 2 = 1 := by
  decide

theorem halfSpinSwap_ne_one : halfSpinSwap ≠ 1 := by
  decide

theorem orderOf_halfSpinSwap : orderOf halfSpinSwap = 2 :=
  orderOf_eq_prime halfSpinSwap_squared halfSpinSwap_ne_one

theorem halfSpinSwap_conj_trialityCycle :
    halfSpinSwap * trialityCycle * halfSpinSwap = trialityCycle⁻¹ := by
  decide

/-- The four possible image types for a D4 diagram action. This is a
classification label, not a constructed Galois action. -/
inductive DiagramImageKind where
  | trivial
  | cyclicTwo
  | cyclicThree
  | symmetricThree
  deriving DecidableEq, Repr

namespace DiagramImageKind

def IsNontrialitarian : DiagramImageKind → Prop
  | .trivial | .cyclicTwo => True
  | .cyclicThree | .symmetricThree => False

def IsTrialitarian : DiagramImageKind → Prop
  | .trivial | .cyclicTwo => False
  | .cyclicThree | .symmetricThree => True

theorem nontrialitarian_or_trialitarian (kind : DiagramImageKind) :
    kind.IsNontrialitarian ∨ kind.IsTrialitarian := by
  cases kind <;> simp [IsNontrialitarian, IsTrialitarian]

end DiagramImageKind

/-- An abstract group action on the three outer D4 nodes. The intended Galois
interpretation is not part of this structure. -/
structure DiagramDescent (Γ : Type*) [Group Γ] where
  action : Γ →* DiagramSymmetry

namespace DiagramDescent

/-- The order of the image of the supplied diagram action. -/
noncomputable def imageOrder {Γ : Type*} [Group Γ]
    (D : DiagramDescent Γ) : ℕ :=
  Nat.card D.action.range

theorem diagramSymmetry_natCard : Nat.card DiagramSymmetry = 6 := by
  rw [Nat.card_eq_fintype_card]
  exact card_diagramSymmetry

theorem imageOrder_cases {Γ : Type*} [Group Γ]
    (D : DiagramDescent Γ) :
    D.imageOrder = 1 ∨ D.imageOrder = 2 ∨
      D.imageOrder = 3 ∨ D.imageOrder = 6 := by
  have hdvd : D.imageOrder ∣ 6 := by
    rw [← diagramSymmetry_natCard]
    exact Subgroup.card_subgroup_dvd_card D.action.range
  have hpos : 0 < D.imageOrder := Nat.card_pos
  have hle : D.imageOrder ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : D.imageOrder
  all_goals norm_num at hdvd
  all_goals norm_num

/-- Classify the supplied action by the order of its image in `S3`. -/
noncomputable def kind {Γ : Type*} [Group Γ]
    (D : DiagramDescent Γ) : DiagramImageKind :=
  if D.imageOrder = 1 then .trivial
  else if D.imageOrder = 2 then .cyclicTwo
  else if D.imageOrder = 3 then .cyclicThree
  else .symmetricThree

theorem kind_eq_trivial_iff {Γ : Type*} [Group Γ]
    (D : DiagramDescent Γ) :
    D.kind = .trivial ↔ D.imageOrder = 1 := by
  rcases D.imageOrder_cases with h | h | h | h <;>
    simp [kind, h]

theorem kind_eq_cyclicTwo_iff {Γ : Type*} [Group Γ]
    (D : DiagramDescent Γ) :
    D.kind = .cyclicTwo ↔ D.imageOrder = 2 := by
  rcases D.imageOrder_cases with h | h | h | h <;>
    simp [kind, h]

theorem kind_eq_cyclicThree_iff {Γ : Type*} [Group Γ]
    (D : DiagramDescent Γ) :
    D.kind = .cyclicThree ↔ D.imageOrder = 3 := by
  rcases D.imageOrder_cases with h | h | h | h <;>
    simp [kind, h]

theorem kind_eq_symmetricThree_iff {Γ : Type*} [Group Γ]
    (D : DiagramDescent Γ) :
    D.kind = .symmetricThree ↔ D.imageOrder = 6 := by
  rcases D.imageOrder_cases with h | h | h | h <;>
    simp [kind, h]

theorem isTrialitarian_iff {Γ : Type*} [Group Γ]
    (D : DiagramDescent Γ) :
    D.kind.IsTrialitarian ↔
      D.imageOrder = 3 ∨ D.imageOrder = 6 := by
  rcases D.imageOrder_cases with h | h | h | h <;>
    simp [kind, DiagramImageKind.IsTrialitarian, h]

end DiagramDescent

/-- Two orthogonal D4 copies before choosing an eight-coordinate order. -/
abbrev PairNode := Node ⊕ Node

def pairCartanOnNodes : Matrix PairNode PairNode ℤ
  | .inl i, .inl j => cartan i j
  | .inr i, .inr j => cartan i j
  | _, _ => 0

/-- Two consecutive D4 components, each in Mathlib's order
`V, central, S+, S-`. -/
def finEightEquivPairNode : Fin 8 ≃ PairNode :=
  finSumFinEquiv.symm.trans
    (Equiv.sumCongr finFourEquivNode finFourEquivNode)

/-- The canonical block-diagonal D4 x D4 Cartan matrix. -/
def pairCartan : Matrix (Fin 8) (Fin 8) ℤ :=
  fun i j =>
    pairCartanOnNodes (finEightEquivPairNode i) (finEightEquivPairNode j)

theorem pairCartan_eq_displayed :
    pairCartan =
      ![
        ![2, -1, 0, 0, 0, 0, 0, 0],
        ![-1, 2, -1, -1, 0, 0, 0, 0],
        ![0, -1, 2, 0, 0, 0, 0, 0],
        ![0, -1, 0, 2, 0, 0, 0, 0],
        ![0, 0, 0, 0, 2, -1, 0, 0],
        ![0, 0, 0, 0, -1, 2, -1, -1],
        ![0, 0, 0, 0, 0, -1, 2, 0],
        ![0, 0, 0, 0, 0, -1, 0, 2]
      ] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Reindex each D4 block so that the central node appears first. -/
def centralFirstReindex : Equiv.Perm (Fin 8) :=
  Equiv.swap 0 1 * Equiv.swap 4 5

/-- The same D4 x D4 matrix in the central-first ATLAS ordering. -/
def pairCartanCentralFirst : Matrix (Fin 8) (Fin 8) ℤ :=
  fun i j => pairCartan (centralFirstReindex i) (centralFirstReindex j)

theorem pairCartanCentralFirst_eq_displayed :
    pairCartanCentralFirst =
      ![
        ![2, -1, -1, -1, 0, 0, 0, 0],
        ![-1, 2, 0, 0, 0, 0, 0, 0],
        ![-1, 0, 2, 0, 0, 0, 0, 0],
        ![-1, 0, 0, 2, 0, 0, 0, 0],
        ![0, 0, 0, 0, 2, -1, -1, -1],
        ![0, 0, 0, 0, -1, 2, 0, 0],
        ![0, 0, 0, 0, -1, 0, 2, 0],
        ![0, 0, 0, 0, -1, 0, 0, 2]
      ] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality
