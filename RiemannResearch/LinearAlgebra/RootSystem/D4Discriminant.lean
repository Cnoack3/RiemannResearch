/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Ring
import RiemannResearch.LinearAlgebra.RootSystem.D4Lattice

/-!
# The D4 discriminant group and its triality action

For the based D4 root lattice `Q` inside the weight lattice `P`, this file
computes
`P / Q ≃ (ZMod 2) × (ZMod 2)`.
The three outer fundamental-weight classes are exactly the three nonzero
elements, and the diagram-triality group acts faithfully by additive
permutations of this quotient.

Thus the labels `V`, `S+`, and `S-` now denote exact discriminant classes
traditionally associated with the vector and two half-spin highest weights.
They still do not denote constructed representations. No Spin(8) group scheme,
representation-theoretic triality lift, or Galois/fpqc descent is constructed
here.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

/-- The two parity coordinates on the D4 weight lattice. -/
abbrev DiscriminantModel := ZMod 2 × ZMod 2

/-- In the order `V, central, S+, S-`, the discriminant parity map is
`x ↦ (x_V + x_{S+}, x_V + x_{S-}) mod 2`. -/
def parityMap : WeightCoordinates →+ DiscriminantModel where
  toFun x :=
    (((x 0 + x 2 : ℤ) : ZMod 2),
      ((x 0 + x 3 : ℤ) : ZMod 2))
  map_zero' := by
    simp
  map_add' x y := by
    ext <;> simp <;> ring

theorem parityMap_cartanMap (x : RootCoordinates) :
    parityMap (cartanMap x) = 0 := by
  have htwo : (2 : ZMod 2) = 0 := by
    decide
  ext <;> simp [parityMap] <;> ring_nf
  all_goals simp [htwo]

/-- The integral Cartan image is exactly the kernel of the two parity
coordinates. The reverse inclusion uses an explicit integral preimage. -/
theorem rootSublattice_eq_parityMap_ker :
    rootSublattice = parityMap.ker := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact parityMap_cartanMap y
  · intro x hx
    change parityMap x = 0 at hx
    have hfst := congrArg Prod.fst hx
    have hsnd := congrArg Prod.snd hx
    change ((x 0 + x 2 : ℤ) : ZMod 2) = 0 at hfst
    change ((x 0 + x 3 : ℤ) : ZMod 2) = 0 at hsnd
    have hd₁ : (2 : ℤ) ∣ x 0 + x 2 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (x 0 + x 2) 2).mp hfst
    have hd₂ : (2 : ℤ) ∣ x 0 + x 3 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (x 0 + x 3) 2).mp hsnd
    rcases hd₁ with ⟨k, hk⟩
    rcases hd₂ with ⟨l, hl⟩
    refine ⟨![
      x 1 + k + l,
      2 * x 1 + 2 * k + 2 * l - x 0,
      x 1 + 2 * k + l - x 0,
      x 1 + k + 2 * l - x 0], ?_⟩
    rw [cartanMap_apply]
    ext i
    fin_cases i <;> simp <;> omega

theorem parityMap_surjective :
    Function.Surjective parityMap := by
  rintro ⟨a, b⟩
  refine ⟨![0, 0, a.cast, b.cast], ?_⟩
  ext <;> simp [parityMap]

/-- The D4 discriminant group `P / Q` in based coordinates. -/
abbrev DiscriminantGroup :=
  WeightCoordinates ⧸ rootSublattice

/-- The canonical parity-coordinate presentation
`P / Q ≃ (ZMod 2) × (ZMod 2)`. -/
noncomputable def discriminantEquivParity :
    DiscriminantGroup ≃+ DiscriminantModel :=
  (QuotientAddGroup.quotientAddEquivOfEq
      rootSublattice_eq_parityMap_ker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      parityMap parityMap_surjective)

@[simp]
theorem discriminantEquivParity_mk (x : WeightCoordinates) :
    discriminantEquivParity
        (QuotientAddGroup.mk' rootSublattice x) =
      parityMap x := by
  unfold discriminantEquivParity
  rw [AddEquiv.trans_apply]
  change
    (QuotientAddGroup.quotientKerEquivOfSurjective
      parityMap parityMap_surjective)
      ((QuotientAddGroup.quotientAddEquivOfEq
        rootSublattice_eq_parityMap_ker)
        (x : WeightCoordinates ⧸ rootSublattice)) =
      parityMap x
  rw [QuotientAddGroup.quotientAddEquivOfEq_mk]
  change
    QuotientAddGroup.kerLift parityMap
      (x : WeightCoordinates ⧸ parityMap.ker) =
    parityMap x
  exact QuotientAddGroup.kerLift_mk parityMap x

theorem natCard_discriminantGroup :
    Nat.card DiscriminantGroup = 4 := by
  rw [Nat.card_congr discriminantEquivParity.toEquiv]
  norm_num [Nat.card_prod]

/-- The three nonzero parity vectors, labelled by the outer D4 nodes. -/
def labelParity : TrialityLabel → DiscriminantModel
  | .vector => (1, 1)
  | .halfSpinPlus => (1, 0)
  | .halfSpinMinus => (0, 1)

@[simp]
theorem parityMap_outerFundamentalWeight (label : TrialityLabel) :
    parityMap (outerFundamentalWeight label) = labelParity label := by
  cases label <;>
    simp [parityMap, outerFundamentalWeight, labelParity]

theorem labelParity_ne_zero (label : TrialityLabel) :
    labelParity label ≠ 0 := by
  cases label <;> decide

theorem labelParity_injective :
    Function.Injective labelParity := by
  intro a b h
  cases a <;> cases b <;> simp_all [labelParity]

/-- The quotient class of an outer fundamental weight. -/
def fundamentalClass (label : TrialityLabel) : DiscriminantGroup :=
  QuotientAddGroup.mk' rootSublattice (outerFundamentalWeight label)

@[simp]
theorem discriminantEquivParity_fundamentalClass
    (label : TrialityLabel) :
    discriminantEquivParity (fundamentalClass label) =
      labelParity label := by
  change
    discriminantEquivParity
        (QuotientAddGroup.mk' rootSublattice
          (outerFundamentalWeight label)) =
      labelParity label
  rw [discriminantEquivParity_mk, parityMap_outerFundamentalWeight]

theorem fundamentalClass_ne_zero (label : TrialityLabel) :
    fundamentalClass label ≠ 0 := by
  intro h
  apply labelParity_ne_zero label
  rw [← discriminantEquivParity_fundamentalClass label]
  simpa using congrArg discriminantEquivParity h

theorem fundamentalClass_injective :
    Function.Injective fundamentalClass := by
  intro a b h
  apply labelParity_injective
  rw [← discriminantEquivParity_fundamentalClass a,
    ← discriminantEquivParity_fundamentalClass b, h]

/-- The permutation of the four parity vectors induced by a diagram
symmetry. -/
def modelActionFun
    (σ : DiagramSymmetry) (x : DiscriminantModel) :
    DiscriminantModel :=
  if x = 0 then 0
  else if x = labelParity .vector then labelParity (σ .vector)
  else if x = labelParity .halfSpinPlus then
    labelParity (σ .halfSpinPlus)
  else labelParity (σ .halfSpinMinus)

theorem modelActionFun_label :
    ∀ σ label,
      modelActionFun σ (labelParity label) = labelParity (σ label) := by
  decide

theorem modelActionFun_add :
    ∀ σ x y,
      modelActionFun σ (x + y) =
        modelActionFun σ x + modelActionFun σ y := by
  decide

theorem modelActionFun_one :
    ∀ x, modelActionFun 1 x = x := by
  decide

theorem modelActionFun_mul :
    ∀ σ τ x,
      modelActionFun (σ * τ) x =
        modelActionFun σ (modelActionFun τ x) := by
  decide

theorem modelActionFun_symm_left :
    ∀ σ x, modelActionFun σ.symm (modelActionFun σ x) = x := by
  decide

theorem modelActionFun_symm_right :
    ∀ σ x, modelActionFun σ (modelActionFun σ.symm x) = x := by
  decide

def modelActionPerm
    (σ : DiagramSymmetry) : Equiv.Perm DiscriminantModel where
  toFun := modelActionFun σ
  invFun := modelActionFun σ.symm
  left_inv := modelActionFun_symm_left σ
  right_inv := modelActionFun_symm_right σ

/-- The faithful S3 action on the explicit four-element discriminant model. -/
def modelAction :
    DiagramSymmetry →* Equiv.Perm DiscriminantModel where
  toFun := modelActionPerm
  map_one' := by
    apply Equiv.ext
    exact modelActionFun_one
  map_mul' σ τ := by
    apply Equiv.ext
    exact modelActionFun_mul σ τ

@[simp]
theorem modelAction_label
    (σ : DiagramSymmetry) (label : TrialityLabel) :
    modelAction σ (labelParity label) = labelParity (σ label) :=
  modelActionFun_label σ label

theorem modelAction_add
    (σ : DiagramSymmetry) (x y : DiscriminantModel) :
    modelAction σ (x + y) = modelAction σ x + modelAction σ y :=
  modelActionFun_add σ x y

theorem modelAction_injective :
    Function.Injective modelAction := by
  intro σ τ h
  apply Equiv.ext
  intro label
  apply labelParity_injective
  rw [← modelAction_label σ label,
    ← modelAction_label τ label, h]

noncomputable def discriminantActionPerm
    (σ : DiagramSymmetry) : Equiv.Perm DiscriminantGroup :=
  discriminantEquivParity.toEquiv.trans (modelAction σ) |>.trans
    discriminantEquivParity.symm.toEquiv

@[simp]
theorem discriminantEquivParity_discriminantActionPerm_apply
    (σ : DiagramSymmetry) (x : DiscriminantGroup) :
    discriminantEquivParity (discriminantActionPerm σ x) =
      modelAction σ (discriminantEquivParity x) := by
  change
    discriminantEquivParity
      (discriminantEquivParity.symm
        (modelAction σ (discriminantEquivParity x))) =
      modelAction σ (discriminantEquivParity x)
  exact discriminantEquivParity.apply_symm_apply _

/-- Diagram triality acts on the discriminant quotient. The target is the
permutation group; `discriminantAction_add` records that every permutation in
the image is additive. -/
noncomputable def discriminantAction :
    DiagramSymmetry →* Equiv.Perm DiscriminantGroup where
  toFun := discriminantActionPerm
  map_one' := by
    apply Equiv.ext
    intro x
    apply discriminantEquivParity.injective
    rw [discriminantEquivParity_discriminantActionPerm_apply]
    change modelActionFun 1 (discriminantEquivParity x) =
      discriminantEquivParity x
    exact modelActionFun_one _
  map_mul' σ τ := by
    apply Equiv.ext
    intro x
    apply discriminantEquivParity.injective
    rw [discriminantEquivParity_discriminantActionPerm_apply]
    change
      modelActionFun (σ * τ) (discriminantEquivParity x) =
        discriminantEquivParity
          (discriminantActionPerm σ (discriminantActionPerm τ x))
    rw [discriminantEquivParity_discriminantActionPerm_apply,
      discriminantEquivParity_discriminantActionPerm_apply]
    exact modelActionFun_mul σ τ _

@[simp]
theorem discriminantAction_fundamentalClass
    (σ : DiagramSymmetry) (label : TrialityLabel) :
    discriminantAction σ (fundamentalClass label) =
      fundamentalClass (σ label) := by
  apply discriminantEquivParity.injective
  change
    discriminantEquivParity
        (discriminantActionPerm σ (fundamentalClass label)) =
      discriminantEquivParity (fundamentalClass (σ label))
  rw [discriminantEquivParity_discriminantActionPerm_apply,
    discriminantEquivParity_fundamentalClass, modelAction_label,
    discriminantEquivParity_fundamentalClass]

theorem discriminantAction_add
    (σ : DiagramSymmetry) (x y : DiscriminantGroup) :
    discriminantAction σ (x + y) =
      discriminantAction σ x + discriminantAction σ y := by
  apply discriminantEquivParity.injective
  change
    discriminantEquivParity (discriminantActionPerm σ (x + y)) =
      discriminantEquivParity
        (discriminantActionPerm σ x + discriminantActionPerm σ y)
  calc
    _ = modelAction σ (discriminantEquivParity (x + y)) :=
      discriminantEquivParity_discriminantActionPerm_apply σ (x + y)
    _ = modelAction σ
        (discriminantEquivParity x + discriminantEquivParity y) := by
      rw [discriminantEquivParity.map_add]
    _ = modelAction σ (discriminantEquivParity x) +
        modelAction σ (discriminantEquivParity y) :=
      modelAction_add σ _ _
    _ = discriminantEquivParity (discriminantActionPerm σ x) +
        discriminantEquivParity (discriminantActionPerm σ y) := by
      rw [discriminantEquivParity_discriminantActionPerm_apply,
        discriminantEquivParity_discriminantActionPerm_apply]
    _ = _ := by
      rw [discriminantEquivParity.map_add]

theorem discriminantAction_injective :
    Function.Injective discriminantAction := by
  intro σ τ h
  apply modelAction_injective
  apply Equiv.ext
  intro m
  obtain ⟨x, rfl⟩ := discriminantEquivParity.surjective m
  have hx :=
    congrArg discriminantEquivParity (DFunLike.congr_fun h x)
  change
    discriminantEquivParity (discriminantActionPerm σ x) =
      discriminantEquivParity (discriminantActionPerm τ x) at hx
  simpa only
    [discriminantEquivParity_discriminantActionPerm_apply] using hx

theorem orderOf_discriminantAction_trialityCycle :
    orderOf (discriminantAction trialityCycle) = 3 := by
  rw [orderOf_injective discriminantAction discriminantAction_injective]
  exact orderOf_trialityCycle

theorem orderOf_discriminantAction_halfSpinSwap :
    orderOf (discriminantAction halfSpinSwap) = 2 := by
  rw [orderOf_injective discriminantAction discriminantAction_injective]
  exact orderOf_halfSpinSwap

def labelOfNonzeroModel
    (x : {x : DiscriminantModel // x ≠ 0}) : TrialityLabel :=
  if x.1 = labelParity .vector then .vector
  else if x.1 = labelParity .halfSpinPlus then .halfSpinPlus
  else .halfSpinMinus

def labelParityEquivNonzeroModel :
    TrialityLabel ≃ {x : DiscriminantModel // x ≠ 0} where
  toFun label := ⟨labelParity label, labelParity_ne_zero label⟩
  invFun := labelOfNonzeroModel
  left_inv := by
    decide
  right_inv := by
    decide

noncomputable def nonzeroModelEquivNonzeroDiscriminant :
    {x : DiscriminantModel // x ≠ 0} ≃
      {x : DiscriminantGroup // x ≠ 0} where
  toFun x := ⟨discriminantEquivParity.symm x.1, by
    intro h
    apply x.2
    have he := congrArg discriminantEquivParity h
    simpa using he⟩
  invFun x := ⟨discriminantEquivParity x.1, by
    intro h
    apply x.2
    apply discriminantEquivParity.injective
    simpa using h⟩
  left_inv x := by
    apply Subtype.ext
    exact discriminantEquivParity.apply_symm_apply x.1
  right_inv x := by
    apply Subtype.ext
    exact discriminantEquivParity.symm_apply_apply x.1

/-- The three outer labels are exactly the three nonzero D4 discriminant
classes. -/
noncomputable def trialityLabelEquivNonzeroDiscriminant :
    TrialityLabel ≃ {x : DiscriminantGroup // x ≠ 0} :=
  labelParityEquivNonzeroModel.trans
    nonzeroModelEquivNonzeroDiscriminant

@[simp]
theorem trialityLabelEquivNonzeroDiscriminant_apply
    (label : TrialityLabel) :
    trialityLabelEquivNonzeroDiscriminant label =
      ⟨fundamentalClass label, fundamentalClass_ne_zero label⟩ := by
  apply Subtype.ext
  apply discriminantEquivParity.injective
  rw [discriminantEquivParity_fundamentalClass]
  exact discriminantEquivParity.apply_symm_apply (labelParity label)

namespace DiagramDescent

/-- A supplied diagram action induces an action on the D4 discriminant
quotient. -/
noncomputable def discriminantQuotientAction
    {Γ : Type*} [Group Γ] (D : DiagramDescent Γ) :
    Γ →* Equiv.Perm DiscriminantGroup :=
  discriminantAction.comp D.action

/-- The order of the image of the induced discriminant action. -/
noncomputable def discriminantImageOrder
    {Γ : Type*} [Group Γ] (D : DiagramDescent Γ) : ℕ :=
  Nat.card (D.discriminantQuotientAction.range)

noncomputable def diagramImageToDiscriminantImage
    {Γ : Type*} [Group Γ] (D : DiagramDescent Γ) :
    D.action.range → D.discriminantQuotientAction.range :=
  fun x => ⟨discriminantAction x.1, by
    rcases x.2 with ⟨γ, hγ⟩
    refine ⟨γ, ?_⟩
    change discriminantAction (D.action γ) = discriminantAction x.1
    rw [hγ]⟩

theorem diagramImageToDiscriminantImage_bijective
    {Γ : Type*} [Group Γ] (D : DiagramDescent Γ) :
    Function.Bijective D.diagramImageToDiscriminantImage := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply discriminantAction_injective
    exact congrArg Subtype.val h
  · rintro ⟨y, γ, hγ⟩
    refine ⟨⟨D.action γ, ⟨γ, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change discriminantAction (D.action γ) = y
    exact hγ

noncomputable def diagramImageEquivDiscriminantImage
    {Γ : Type*} [Group Γ] (D : DiagramDescent Γ) :
    D.action.range ≃ D.discriminantQuotientAction.range :=
  Equiv.ofBijective D.diagramImageToDiscriminantImage
    D.diagramImageToDiscriminantImage_bijective

/-- Passing from the three outer labels to their nonzero discriminant classes
does not change the image order of any supplied diagram action. -/
theorem discriminantImageOrder_eq_imageOrder
    {Γ : Type*} [Group Γ] (D : DiagramDescent Γ) :
    D.discriminantImageOrder = D.imageOrder := by
  unfold discriminantImageOrder imageOrder
  exact Nat.card_congr D.diagramImageEquivDiscriminantImage.symm

end DiagramDescent
end RiemannResearch.LinearAlgebra.RootSystem.D4Triality
