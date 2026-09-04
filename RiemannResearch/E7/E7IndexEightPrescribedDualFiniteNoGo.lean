/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.E7IndexEightPrescribedDualCommonSplitter

/-!
A finite no-go model for the prescribed-dual affine fibre.
This is a model of the abstract transfer/index/kernel axioms, not a Brauer
group of a field and not a counterexample to E7.
-/

namespace RiemannResearch.E7.QuaternionTrialityPacket.PrescribedDualFiniteNoGo

abbrev F2 := ZMod 2
abbrev A3 := Fin 3 → F2
abbrev V2 := Fin 2 → F2
abbrev B4 := V2 × V2
abbrev C2 := V2

def tail : A3 → V2 := fun a => ![a 1, a 2]
def includeTail : V2 → A3 := fun v => ![0, v 0, v 1]

def res : A3 →+ B4 where
  toFun a := (tail a, tail a)
  map_zero' := by decide
  map_add' := by decide

def cor : B4 →+ A3 where
  toFun p := includeTail (p.1 + p.2)
  map_zero' := by decide
  map_add' := by decide

def conjugate : B4 →+ B4 where
  toFun p := (p.2, p.1)
  map_zero' := rfl
  map_add' _ _ := rfl

def transfer : QuadraticBrauerTransferModel A3 B4 where
  res := res
  cor := cor
  conjugate := conjugate
  res_cor := by decide
  cor_res := by decide
  conjugate_res := by decide

/-- Its kernel is span {((1,0),0), (0,(0,1))}. -/
def down : B4 →+ C2 where
  toFun p := ![p.1 1, p.2 0]
  map_zero' := by decide
  map_add' := by decide

/-- Its kernel is span {q2,q3}, exactly cor(ker down). -/
def dualDown : A3 →+ F2 where
  toFun a := a 0
  map_zero' := rfl
  map_add' _ _ := rfl

def weightA (a : A3) : Nat :=
  ((Finset.univ : Finset (Fin 3)).filter fun i => a i ≠ 0).card
def weightV (a : V2) : Nat :=
  ((Finset.univ : Finset (Fin 2)).filter fun i => a i ≠ 0).card
def weightB (p : B4) : Nat := max (weightV p.1) (weightV p.2)

def IsQuaternionA (a : A3) : Prop := weightA a ≤ 1
def IsQuaternionB (p : B4) : Prop := weightB p ≤ 1

private instance isQuaternionADecidable (a : A3) :
    Decidable (IsQuaternionA a) :=
  inferInstanceAs (Decidable (weightA a ≤ 1))
private instance isQuaternionBDecidable (p : B4) :
    Decidable (IsQuaternionB p) :=
  inferInstanceAs (Decidable (weightB p ≤ 1))

def symbolicIndexA (a : A3) : Nat := 2 ^ weightA a
def symbolicIndexB (p : B4) : Nat := 2 ^ weightB p

def indexModelA : BrauerIndexModel A3 where
  index := symbolicIndexA
  index_zero := by decide
  index_add_le_mul := by decide

def indexModelB : BrauerIndexModel B4 where
  index := symbolicIndexB
  index_zero := by decide
  index_add_le_mul := by decide

def q1 : A3 := ![1, 0, 0]
def q2 : A3 := ![0, 1, 0]
def q3 : A3 := ![0, 0, 1]
def alpha : A3 := q2 + q3
def beta : A3 := q1 + q2

def s : B4 := (![1, 0], ![0, 0])
def t : B4 := (![0, 0], ![0, 1])
def r : B4 := s + t

theorem exponentTwoA : IsExponentTwo A3 := by
  change ∀ a : A3, a + a = 0
  decide

theorem exponentTwoB : IsExponentTwo B4 := by
  change ∀ b : B4, b + b = 0
  decide

theorem transfer_exact :
    CorestrictionKernelIsRestrictionImage transfer := by
  change ∀ k : B4, transfer.cor k = 0 →
    ∃ a : A3, transfer.res a = k
  decide

theorem conjugation_involutive :
    ∀ b : B4, transfer.conjugate (transfer.conjugate b) = b := by
  decide

theorem hardIndexPattern :
    IsQuaternionA q1 ∧ IsQuaternionA q2 ∧ IsQuaternionA q3 ∧
    indexModelA.index (q1 + q2 + q3) = 8 ∧
    indexModelA.index (q1 + q2) = 4 ∧
    indexModelA.index (q1 + q3) = 4 ∧
    indexModelA.index (q2 + q3) = 4 := by
  decide

theorem quaternionA_index_le_two :
    ∀ a : A3, IsQuaternionA a → indexModelA.index a ≤ 2 := by
  decide

theorem quaternionB_index_le_two :
    ∀ b : B4, IsQuaternionB b → indexModelB.index b ≤ 2 := by
  decide

theorem restriction_index_le :
    ∀ a : A3, indexModelB.index (transfer.res a) ≤ indexModelA.index a := by
  decide

theorem corestriction_index_le_square :
    ∀ b : B4,
      indexModelA.index (transfer.cor b) ≤
        indexModelB.index b * indexModelB.index b := by
  decide

theorem conjugation_preserves_index :
    ∀ b : B4,
      indexModelB.index (transfer.conjugate b) = indexModelB.index b := by
  decide

theorem restriction_preserves_quaternion :
    ∀ a : A3, IsQuaternionA a →
      IsQuaternionB (transfer.res a) := by
  decide

theorem quadraticRestrictionKernel_index_le_two :
    ∀ a : A3, transfer.res a = 0 → indexModelA.index a ≤ 2 := by
  decide

theorem first_is_split : transfer.res q1 = 0 := by decide

theorem layerKernel_quaternion :
    LayerRestrictionKernelConsistsOfQuaternionClasses
      down IsQuaternionB := by
  change ∀ b : B4, down b = 0 → IsQuaternionB b
  decide

theorem conjugation_preserves_quaternion :
    ConjugationPreservesQuaternionClasses transfer IsQuaternionB := by
  change ∀ b : B4, IsQuaternionB b →
    IsQuaternionB (transfer.conjugate b)
  decide

theorem layerKernel_not_conjugationStable :
    ∃ b : B4, down b = 0 ∧
      down (transfer.conjugate b) ≠ 0 := by
  decide

theorem dual_detection :
    AddSubgroup.map transfer.cor down.ker = dualDown.ker := by
  ext a
  simp only [AddSubgroup.mem_map, AddMonoidHom.mem_ker]
  change
    (∃ b : B4, down b = 0 ∧ transfer.cor b = a) ↔
      dualDown a = 0
  revert a
  decide

theorem detects_exactly :
    DualQuarticRestrictionDetectsLayerCorestrictions
      transfer down dualDown :=
  dual_detection

theorem dual_splits_prescribed_labels :
    dualDown q2 = 0 ∧ dualDown q3 = 0 ∧ dualDown alpha = 0 := by
  decide

theorem upper_splits_neither_remaining_label :
    down (transfer.res q2) ≠ 0 ∧
      down (transfer.res q3) ≠ 0 := by
  decide

theorem constituent_kernel_witnesses :
    down s = 0 ∧ down t = 0 ∧
      transfer.cor s = q2 ∧ transfer.cor t = q3 := by
  decide

/-- The finite obstruction is rigid: there is no nonzero simultaneous
restriction/corestriction-kernel direction along which its canonical
crossed witness could be repaired. -/
theorem canonicalCrossedDirection_trivial :
    ∀ δ : CanonicalCrossedDirection transfer down,
      (δ : B4) = 0 := by
  rintro ⟨x, hx⟩
  change down x = 0 ∧ transfer.cor x = 0 at hx
  change x = 0
  revert x
  decide

/-- The general affine-direction criterion recovers the failure of a
quaternion point in the finite model from rigidity of the direction space
and failure of its unique basepoint. -/
theorem no_quaternionPoint_by_trivialDirection :
    ¬ ∃ x ∈ CanonicalCrossedFibre transfer down q2 q3,
      IsQuaternionB (x + transfer.res beta) := by
  have hr :
      r ∈ CanonicalCrossedFibre transfer down q2 q3 := by
    change down r = 0 ∧ transfer.cor r = q2 + q3
    decide
  rw [exists_quaternionPoint_iff_basepoint_of_trivial_direction
    transfer down IsQuaternionB q2 q3 beta r hr
      canonicalCrossedDirection_trivial]
  decide

theorem alpha_kernel_fibre_unique :
    ∀ x : B4,
      (down x = 0 ∧ transfer.cor x = alpha) ↔ x = r := by
  decide

theorem unique_translate_value :
    r + transfer.res beta = (![0, 0], ![1, 1]) := by
  decide

theorem alpha_kernel_fibre_translate_not_quaternion :
    ∀ x : B4,
      down x = 0 → transfer.cor x = alpha →
        ¬ IsQuaternionB (x + transfer.res beta) := by
  decide

theorem no_crossed_rectangle_explicit :
    ¬ ∃ s t : B4,
      down s = 0 ∧ down t = 0 ∧
      transfer.cor s = q2 ∧ transfer.cor t = q3 ∧
      IsQuaternionB (t + transfer.conjugate s) := by
  decide

theorem no_crossed_rectangle :
    ¬ HasCrossedQuaternionKernelRectangle
      transfer down IsQuaternionB q2 q3 := by
  exact no_crossed_rectangle_explicit

/-- Even after recording that the chosen layer kernel consists of quaternion
classes, this abstract model has no layer-constrained linked lift. -/
theorem no_layerKernelCorestrictionLinkedQuaternionLift :
    ¬ HasLayerKernelCorestrictionLinkedQuaternionLift
      transfer down IsQuaternionB alpha beta := by
  rintro ⟨x, hxDown, _, hxCor, hxTranslate⟩
  exact
    alpha_kernel_fibre_translate_not_quaternion
      x hxDown hxCor hxTranslate

theorem prescribed_dual_and_fibre_but_no_quaternion_translate :
    dualDown q2 = 0 ∧
    dualDown alpha = 0 ∧
    (∃ x : B4, down x = 0 ∧ transfer.cor x = alpha) ∧
    (¬ ∃ x : B4, down x = 0 ∧ transfer.cor x = alpha ∧
      IsQuaternionB (x + transfer.res beta)) := by
  decide

end RiemannResearch.E7.QuaternionTrialityPacket.PrescribedDualFiniteNoGo
