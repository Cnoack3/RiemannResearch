/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.LinearAlgebra.RootSystem.D4Triality

/-!
# The permutation-stable related-triples model of D4 triality

This file constructs an actual faithful outer-label S3 action on a
tensor-stabilizer group. A point is a triple of linear automorphisms, indexed
by V, S+, S-, which preserves one trilinear tensor in every one of the six
orders of those labels. Reindexing the three components therefore gives a
group automorphism, and these automorphisms form a faithful S3 action.

The three component homomorphisms are permuted by this action. Thus this
module proves the representation-compatibility pattern expected of triality,
rather than merely constructing an abstract action on a group.

This is deliberately a tensor-stabilizer group, not yet an identification
with Mathlib's pointwise spinGroup and not a representable group scheme.
The comparison with the exterior-Fock vector and half-spin representations
requires a triality tensor and a proved equivalence with the Spin points.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

universe uK uV

section TensorGroup

variable (K : Type uK) [Field K]
variable (V : Type uV) [AddCommGroup V] [Module K V]

abbrev TrialityLinearTriple :=
  TrialityLabel → (V ≃ₗ[K] V)

abbrev TrialityTensor :=
  V →ₗ[K] V →ₗ[K] V →ₗ[K] K

def permutationStableTrialityGroup
    (T : TrialityTensor K V) :
    Subgroup (TrialityLinearTriple K V) where
  carrier := {g | ∀ (σ : DiagramSymmetry) (x y z : V),
    T (g (σ .vector) x)
        (g (σ .halfSpinPlus) y)
        (g (σ .halfSpinMinus) z) =
      T x y z}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh σ x y z
    simp only [Pi.mul_apply, LinearEquiv.mul_apply]
    rw [hg σ, hh σ]
  inv_mem' := by
    intro g hg σ x y z
    have h := hg σ
      ((g (σ .vector))⁻¹ x)
      ((g (σ .halfSpinPlus))⁻¹ y)
      ((g (σ .halfSpinMinus))⁻¹ z)
    simpa using h.symm

def trialitySignTriple (l : TrialityLabel) :
    TrialityLinearTriple K V :=
  fun k => if k = l then 1 else LinearEquiv.neg K

theorem trialitySignTriple_mem
    (T : TrialityTensor K V) (l : TrialityLabel) :
    trialitySignTriple K V l ∈
      permutationStableTrialityGroup K V T := by
  intro σ x y z
  have h := σ.apply_symm_apply l
  cases hs : σ.symm l with
  | vector =>
      have hv : σ .vector = l := by simpa [hs] using h
      have hp : σ .halfSpinPlus ≠ l := by
        intro hp
        have := σ.injective (hv.trans hp.symm)
        contradiction
      have hm : σ .halfSpinMinus ≠ l := by
        intro hm
        have := σ.injective (hv.trans hm.symm)
        contradiction
      simp [trialitySignTriple, hv, hp, hm]
  | halfSpinPlus =>
      have hp : σ .halfSpinPlus = l := by simpa [hs] using h
      have hv : σ .vector ≠ l := by
        intro hv
        have := σ.injective (hv.trans hp.symm)
        contradiction
      have hm : σ .halfSpinMinus ≠ l := by
        intro hm
        have := σ.injective (hp.trans hm.symm)
        contradiction
      simp [trialitySignTriple, hv, hp, hm]
  | halfSpinMinus =>
      have hm : σ .halfSpinMinus = l := by simpa [hs] using h
      have hv : σ .vector ≠ l := by
        intro hv
        have := σ.injective (hv.trans hm.symm)
        contradiction
      have hp : σ .halfSpinPlus ≠ l := by
        intro hp
        have := σ.injective (hp.trans hm.symm)
        contradiction
      simp [trialitySignTriple, hv, hp, hm]

noncomputable def trialitySignMarker
    (T : TrialityTensor K V) (l : TrialityLabel) :
    permutationStableTrialityGroup K V T :=
  ⟨trialitySignTriple K V l, trialitySignTriple_mem K V T l⟩

def trialityReindex
    (T : TrialityTensor K V) (σ : DiagramSymmetry) :
    MulAut (permutationStableTrialityGroup K V T) where
  toFun g :=
    ⟨fun l => g.1 (σ⁻¹ l), by
      intro τ x y z
      simpa [Equiv.Perm.mul_apply] using
        g.property (σ⁻¹ * τ) x y z⟩
  invFun g :=
    ⟨fun l => g.1 (σ l), by
      intro τ x y z
      simpa [Equiv.Perm.mul_apply] using
        g.property (σ * τ) x y z⟩
  left_inv g := by
    apply Subtype.ext
    funext l
    simp
  right_inv g := by
    apply Subtype.ext
    funext l
    simp
  map_mul' g h := by
    apply Subtype.ext
    funext l
    rfl

def trialityTensorAction
    (T : TrialityTensor K V) :
    DiagramSymmetry →*
      MulAut (permutationStableTrialityGroup K V T) where
  toFun := trialityReindex K V T
  map_one' := by
    ext g l
    rfl
  map_mul' σ τ := by
    ext g l
    rfl

def trialityComponent
    (T : TrialityTensor K V) (l : TrialityLabel) :
    permutationStableTrialityGroup K V T →* (V ≃ₗ[K] V) where
  toFun g := g.1 l
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem trialityComponent_action
    (T : TrialityTensor K V)
    (σ : DiagramSymmetry) (l : TrialityLabel)
    (g : permutationStableTrialityGroup K V T) :
    trialityComponent K V T l
        (trialityTensorAction K V T σ g) =
      trialityComponent K V T (σ⁻¹ l) g :=
  rfl

@[simp] theorem trialityComponent_action_image
    (T : TrialityTensor K V)
    (σ : DiagramSymmetry) (l : TrialityLabel)
    (g : permutationStableTrialityGroup K V T) :
    trialityComponent K V T (σ l)
        (trialityTensorAction K V T σ g) =
      trialityComponent K V T l g := by
  simp

@[simp] theorem trialityTensorAction_signMarker
    (T : TrialityTensor K V)
    (σ : DiagramSymmetry) (l : TrialityLabel) :
    trialityTensorAction K V T σ (trialitySignMarker K V T l) =
      trialitySignMarker K V T (σ l) := by
  apply Subtype.ext
  funext k
  change
    (if σ⁻¹ k = l then 1 else LinearEquiv.neg K) =
      (if k = σ l then 1 else LinearEquiv.neg K)
  by_cases h : σ⁻¹ k = l
  · have hk : k = σ l := by
      simpa using congrArg σ h
    rw [if_pos h, if_pos hk]
  · have hk : k ≠ σ l := by
      intro hk
      apply h
      simp [hk]
    rw [if_neg h, if_neg hk]

end TensorGroup

section Faithful

variable (K : Type uK) [Field K] [Invertible (2 : K)]
variable (V : Type uV) [AddCommGroup V] [Module K V] [Nontrivial V]

theorem trialitySignTriple_injective :
    Function.Injective (trialitySignTriple K V) := by
  intro a b h
  by_contra hab
  have he : (1 : V ≃ₗ[K] V) = LinearEquiv.neg K := by
    simpa [trialitySignTriple, hab] using congrFun h a
  obtain ⟨x : V, hx⟩ := exists_ne (0 : V)
  have hxapp := congrArg (fun e : V ≃ₗ[K] V => e x) he
  change x = -x at hxapp
  have htwo : (2 : K) • x = 0 := by
    calc
      (2 : K) • x = x + x := two_smul K x
      _ = -x + x := congrArg (fun y : V => y + x) hxapp
      _ = 0 := neg_add_cancel x
  have hxzero : x = 0 :=
    (smul_eq_zero.mp htwo).resolve_left
      (isUnit_of_invertible (2 : K)).ne_zero
  exact hx hxzero

theorem trialityTensorAction_injective
    (T : TrialityTensor K V) :
    Function.Injective (trialityTensorAction K V T) := by
  intro σ τ h
  apply Equiv.ext
  intro l
  apply trialitySignTriple_injective K V
  have hm := congrArg
    (fun a : MulAut (permutationStableTrialityGroup K V T) =>
      a (trialitySignMarker K V T l)) h
  rw [trialityTensorAction_signMarker,
    trialityTensorAction_signMarker] at hm
  exact congrArg Subtype.val hm

theorem orderOf_trialityTensorAction_trialityCycle
    (T : TrialityTensor K V) :
    orderOf (trialityTensorAction K V T trialityCycle) = 3 := by
  rw [orderOf_injective (trialityTensorAction K V T)
    (trialityTensorAction_injective K V T)]
  exact orderOf_trialityCycle

theorem orderOf_trialityTensorAction_halfSpinSwap
    (T : TrialityTensor K V) :
    orderOf (trialityTensorAction K V T halfSpinSwap) = 2 := by
  rw [orderOf_injective (trialityTensorAction K V T)
    (trialityTensorAction_injective K V T)]
  exact orderOf_halfSpinSwap

end Faithful

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality


namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

/-- An automorphism is inner when it is conjugation by an element of the
underlying group. -/
def IsInnerAutomorphism {G : Type*} [Group G] (a : MulAut G) : Prop :=
  ∃ g : G, a = MulAut.conj g

namespace IsInnerAutomorphism

/-- Inner automorphisms fix every central element. -/
theorem fix_of_mem_center {G : Type*} [Group G]
    {a : MulAut G} (ha : IsInnerAutomorphism a)
    {z : G} (hz : z ∈ Subgroup.center G) :
    a z = z := by
  rcases ha with ⟨g, rfl⟩
  rw [MulAut.conj_apply]
  have hcomm : g * z = z * g :=
    (Subgroup.mem_center_iff.mp hz) g
  rw [hcomm]
  simp

end IsInnerAutomorphism

universe uK uV

section Outer

variable (K : Type uK) [Field K] [Invertible (2 : K)]
variable (V : Type uV) [AddCommGroup V] [Module K V] [Nontrivial V]

/-- The three sign markers are central in the tensor-stabilizer group. -/
theorem trialitySignMarker_mem_center
    (T : TrialityTensor K V) (l : TrialityLabel) :
    trialitySignMarker K V T l ∈
      Subgroup.center (permutationStableTrialityGroup K V T) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  funext k
  ext x
  by_cases hk : k = l
  · subst k
    simp [trialitySignMarker, trialitySignTriple]
  · simp [trialitySignMarker, trialitySignTriple, hk]

/-- Every nontrivial diagram relabeling is genuinely outer: it cannot be
conjugation by an element of the tensor-stabilizer group. -/
theorem trialityTensorAction_not_inner_of_ne_one
    (T : TrialityTensor K V) (σ : DiagramSymmetry)
    (hσ : σ ≠ 1) :
    ¬ IsInnerAutomorphism (trialityTensorAction K V T σ) := by
  intro hinner
  apply hσ
  apply Equiv.ext
  intro l
  have hfix := hinner.fix_of_mem_center
    (trialitySignMarker_mem_center K V T l)
  rw [trialityTensorAction_signMarker] at hfix
  apply trialitySignTriple_injective K V
  exact congrArg Subtype.val hfix

end Outer

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality
