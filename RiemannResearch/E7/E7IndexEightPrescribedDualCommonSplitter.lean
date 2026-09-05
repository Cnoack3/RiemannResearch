/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E7.E7IndexEightDualQuarticIncidence

/-!
# Prescribed dual common splitters and the remaining affine point

Over a field of characteristic different from two with vanishing
`H³(F, μ₂^⊗3)`, the Lam--Leep--Tignol construction can be oriented so that
the nonnormal quartic member of a dihedral dual pair splits two prescribed
quaternion classes.  Tignol's relative Brauer-kernel description, together
with a projection-formula absorption of its extra quadratic-symbol term,
then places both classes in the corestriction image of one upper
quadratic-layer kernel.

The field-theoretic construction is not formalized here:
`HasPrescribedDualCommonSplitter` is the exact interface it must provide.
The formal consequences make the canonical corestriction fibre nonempty and
identify it as a torsor under the simultaneous restriction/corestriction
kernel.  A crossed quaternion rectangle exists exactly when one translated
point of that fibre is quaternion; this module does not assert that such a
point exists.

Reference: Lam--Leep--Tignol, *Biquaternion algebras and quartic extensions*,
Theorem 4.2 and Proposition 3.3,
<https://www.numdam.org/item/PMIHES_1993__77__63_0.pdf>;
Tignol, *Tores associés à une algèbre étale quartique*, Corollary 3.5 and
Example 5.3, <https://arxiv.org/abs/1704.04072>.
-/

namespace RiemannResearch.E7.QuaternionTrialityPacket

universe u v w y

variable {A : Type u} {B : Type v} {C : Type w} {E : Type y}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup E]

/-- One Tignol dual pair whose dual member splits both prescribed base
classes. -/
def HasPrescribedDualCommonSplitter
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (dualDown : A →+ E)
    (q₂ q₃ : A) : Prop :=
  DualQuarticRestrictionDetectsLayerCorestrictions T down dualDown ∧
    dualDown q₂ = 0 ∧ dualDown q₃ = 0

/-- The affine fibre of upper-layer-kernel classes with prescribed total
corestriction. -/
def CanonicalCrossedFibre
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (q₂ q₃ : A) : Set B :=
  {r | down r = 0 ∧ T.cor r = q₂ + q₃}

/-- The simultaneous restriction/corestriction kernel translating the
canonical crossed fibre. -/
def CanonicalCrossedDirection
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) : AddSubgroup B :=
  down.ker ⊓ T.cor.ker

/-- The upper quadratic layer kills no new restriction of a
ground-field class beyond those already killed over the quadratic base. -/
def UpperLayerAddsNoNewGroundRestrictionKernel
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) : Prop :=
  ∀ γ : A, down (T.res γ) = 0 → T.res γ = 0

/-- Under quadratic-transfer exactness, a canonical direction is exactly the
restriction of a ground-field class that becomes split over the upper
quartic layer. -/
theorem mem_canonicalCrossedDirection_iff_exists_restricted_layerSplitter
    (hA₂ : IsExponentTwo A)
    (T : QuadraticBrauerTransferModel A B)
    (hexact : CorestrictionKernelIsRestrictionImage T)
    (down : B →+ C)
    (δ : B) :
    δ ∈ CanonicalCrossedDirection T down ↔
      ∃ γ : A, down (T.res γ) = 0 ∧ T.res γ = δ := by
  constructor
  · intro hδ
    have hmem := AddSubgroup.mem_inf.mp hδ
    have hdown : down δ = 0 := AddMonoidHom.mem_ker.mp hmem.1
    have hcor : T.cor δ = 0 := AddMonoidHom.mem_ker.mp hmem.2
    rcases hexact δ hcor with ⟨γ, hγ⟩
    exact ⟨γ, by simpa only [hγ] using hdown, hγ⟩
  · rintro ⟨γ, hdown, rfl⟩
    apply AddSubgroup.mem_inf.mpr
    constructor
    · exact AddMonoidHom.mem_ker.mpr hdown
    · apply AddMonoidHom.mem_ker.mpr
      rw [T.cor_res, hA₂ γ]

/-- Exactness identifies the affine direction subgroup with the restriction
image of the ground-field classes split by the full quartic layer. -/
theorem canonicalCrossedDirection_eq_restriction_map_layerKernel
    (hA₂ : IsExponentTwo A)
    (T : QuadraticBrauerTransferModel A B)
    (hexact : CorestrictionKernelIsRestrictionImage T)
    (down : B →+ C) :
    CanonicalCrossedDirection T down =
      AddSubgroup.map T.res (down.comp T.res).ker := by
  ext δ
  rw [mem_canonicalCrossedDirection_iff_exists_restricted_layerSplitter
    hA₂ T hexact down δ]
  constructor
  · rintro ⟨γ, hdown, hres⟩
    exact
      ⟨γ, AddMonoidHom.mem_ker.mpr hdown, hres⟩
  · rintro ⟨γ, hγ, hres⟩
    exact
      ⟨γ, AddMonoidHom.mem_ker.mp hγ, hres⟩

/-- The canonical direction is trivial exactly when the upper layer kills no
new restricted ground-field Brauer class. -/
theorem canonicalCrossedDirection_trivial_iff_upperLayerAddsNoNew
    (hA₂ : IsExponentTwo A)
    (T : QuadraticBrauerTransferModel A B)
    (hexact : CorestrictionKernelIsRestrictionImage T)
    (down : B →+ C) :
    (∀ δ : CanonicalCrossedDirection T down, (δ : B) = 0) ↔
      UpperLayerAddsNoNewGroundRestrictionKernel T down := by
  constructor
  · intro htrivial γ hdown
    have hmem :
        T.res γ ∈ CanonicalCrossedDirection T down :=
      (mem_canonicalCrossedDirection_iff_exists_restricted_layerSplitter
        hA₂ T hexact down (T.res γ)).mpr
          ⟨γ, hdown, rfl⟩
    exact htrivial ⟨T.res γ, hmem⟩
  · intro hNoNew δ
    rcases
        (mem_canonicalCrossedDirection_iff_exists_restricted_layerSplitter
          hA₂ T hexact down (δ : B)).mp δ.property with
      ⟨γ, hdown, hres⟩
    exact hres.symm.trans (hNoNew γ hdown)

/-- The exact residual algebraic condition after a quadratic upper layer has
been fixed: a class in its restriction kernel has prescribed corestriction,
and both it and its prescribed translate are quaternion classes.

Unlike `HasCorestrictionLinkedQuaternionLift`, this remembers the chosen
layer.  The extra kernel condition is essential for the prescribed-dual
quartic incidence problem. -/
def HasLayerKernelCorestrictionLinkedQuaternionLift
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C)
    (IsQuaternionClassB : B → Prop)
    (α β : A) : Prop :=
  ∃ r : B,
    down r = 0 ∧
      IsQuaternionClassB r ∧
      T.cor r = α ∧
      IsQuaternionClassB (r + T.res β)

/-- Once based, the canonical crossed fibre is a simply transitive affine
space under the simultaneous restriction/corestriction kernel. -/
theorem mem_canonicalCrossedFibre_iff_existsUnique_direction
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (q₂ q₃ : A)
    (r₀ : B)
    (hr₀ : r₀ ∈ CanonicalCrossedFibre T down q₂ q₃)
    (r : B) :
    r ∈ CanonicalCrossedFibre T down q₂ q₃ ↔
      ∃! δ : CanonicalCrossedDirection T down,
        r = r₀ + (δ : B) := by
  change
    (down r = 0 ∧ T.cor r = q₂ + q₃) ↔ _
  change down r₀ = 0 ∧ T.cor r₀ = q₂ + q₃ at hr₀
  rcases hr₀ with ⟨hr₀Down, hr₀Cor⟩
  constructor
  · rintro ⟨hrDown, hrCor⟩
    let δ : CanonicalCrossedDirection T down :=
      ⟨r - r₀, by
        change down (r - r₀) = 0 ∧ T.cor (r - r₀) = 0
        constructor
        · rw [map_sub, hrDown, hr₀Down, sub_self]
        · rw [map_sub, hrCor, hr₀Cor, sub_self]⟩
    have hδ : r = r₀ + (δ : B) := by
      change r = r₀ + (r - r₀)
      abel
    refine ⟨δ, hδ, ?_⟩
    intro ε hε
    apply Subtype.ext
    exact add_left_cancel (hε.symm.trans hδ)
  · rintro ⟨δ, hδ, _⟩
    have hδMem := AddSubgroup.mem_inf.mp δ.property
    have hδDown : down (δ : B) = 0 :=
      AddMonoidHom.mem_ker.mp hδMem.1
    have hδCor : T.cor (δ : B) = 0 :=
      AddMonoidHom.mem_ker.mp hδMem.2
    constructor
    · rw [hδ, map_add, hr₀Down, hδDown, add_zero]
    · rw [hδ, map_add, hr₀Cor, hδCor, add_zero]

/-- The translated quaternion-point problem is exactly an orbit-intersection
problem for the direction subgroup, independently of the chosen basepoint. -/
theorem exists_quaternionPoint_iff_exists_directionCorrection
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C)
    (IsQuaternionClassB : B → Prop)
    (q₂ q₃ β : A)
    (r₀ : B)
    (hr₀ : r₀ ∈ CanonicalCrossedFibre T down q₂ q₃) :
    (∃ r ∈ CanonicalCrossedFibre T down q₂ q₃,
        IsQuaternionClassB (r + T.res β)) ↔
      ∃ δ : CanonicalCrossedDirection T down,
        IsQuaternionClassB (r₀ + (δ : B) + T.res β) := by
  constructor
  · rintro ⟨r, hr, hrQuaternion⟩
    rcases
        (mem_canonicalCrossedFibre_iff_existsUnique_direction
          T down q₂ q₃ r₀ hr₀ r).mp hr with
      ⟨δ, hδ, _⟩
    exact ⟨δ, by simpa only [hδ] using hrQuaternion⟩
  · rintro ⟨δ, hδQuaternion⟩
    refine ⟨r₀ + (δ : B), ?_, hδQuaternion⟩
    apply
      (mem_canonicalCrossedFibre_iff_existsUnique_direction
        T down q₂ q₃ r₀ hr₀ (r₀ + (δ : B))).mpr
    refine ⟨δ, rfl, ?_⟩
    intro ε hε
    apply Subtype.ext
    exact add_left_cancel hε.symm

/-- If the chosen basepoint has a non-quaternion prescribed translate, then
any successful point of the same canonical fibre must be obtained from it by
a nonzero simultaneous restriction/corestriction-kernel direction.

This isolates the exact source of flexibility left after fixing the LLT--
Tignol quartic layer: a failed explicit crossed witness can only be repaired
inside `ker down ∩ ker T.cor`, never by choosing another decomposition of the
same point. -/
theorem exists_nonzero_directionCorrection_of_basepoint_not_quaternion
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C)
    (IsQuaternionClassB : B → Prop)
    (q₂ q₃ β : A)
    (r₀ : B)
    (hr₀ : r₀ ∈ CanonicalCrossedFibre T down q₂ q₃)
    (hr₀NotQuaternion :
      ¬ IsQuaternionClassB (r₀ + T.res β))
    (hExists :
      ∃ r ∈ CanonicalCrossedFibre T down q₂ q₃,
        IsQuaternionClassB (r + T.res β)) :
    ∃ δ : CanonicalCrossedDirection T down,
      (δ : B) ≠ 0 ∧
        IsQuaternionClassB (r₀ + (δ : B) + T.res β) := by
  rcases
      (exists_quaternionPoint_iff_exists_directionCorrection
        T down IsQuaternionClassB q₂ q₃ β r₀ hr₀).mp hExists with
    ⟨δ, hδQuaternion⟩
  refine ⟨δ, ?_, hδQuaternion⟩
  intro hδZero
  apply hr₀NotQuaternion
  simpa only [hδZero, add_zero] using hδQuaternion

/-- With corestriction exactness, every successful repair of a bad
basepoint is already the restriction of a ground-field class which is
nontrivial over the quadratic base but split by the upper quartic layer. -/
theorem exists_nonzero_restrictedGroundCorrection_of_bad_basepoint
    (hA₂ : IsExponentTwo A)
    (T : QuadraticBrauerTransferModel A B)
    (hexact : CorestrictionKernelIsRestrictionImage T)
    (down : B →+ C)
    (IsQuaternionClassB : B → Prop)
    (q₂ q₃ β : A)
    (r₀ : B)
    (hr₀ : r₀ ∈ CanonicalCrossedFibre T down q₂ q₃)
    (hr₀NotQuaternion :
      ¬ IsQuaternionClassB (r₀ + T.res β))
    (hExists :
      ∃ r ∈ CanonicalCrossedFibre T down q₂ q₃,
        IsQuaternionClassB (r + T.res β)) :
    ∃ γ : A,
      down (T.res γ) = 0 ∧
        T.res γ ≠ 0 ∧
          IsQuaternionClassB
            (r₀ + T.res γ + T.res β) := by
  rcases
      exists_nonzero_directionCorrection_of_basepoint_not_quaternion
        T down IsQuaternionClassB q₂ q₃ β
          r₀ hr₀ hr₀NotQuaternion hExists with
    ⟨δ, hδNonzero, hδQuaternion⟩
  rcases
      (mem_canonicalCrossedDirection_iff_exists_restricted_layerSplitter
        hA₂ T hexact down (δ : B)).mp δ.property with
    ⟨γ, hγDown, hγRes⟩
  refine ⟨γ, hγDown, ?_, ?_⟩
  · intro hγZero
    exact hδNonzero (hγRes.symm.trans hγZero)
  · simpa only [hγRes] using hδQuaternion

/-- If the simultaneous restriction/corestriction kernel is trivial, then
the translated quaternion-point problem has no hidden choice: it is decided
by any one basepoint of the canonical fibre. -/
theorem exists_quaternionPoint_iff_basepoint_of_trivial_direction
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C)
    (IsQuaternionClassB : B → Prop)
    (q₂ q₃ β : A)
    (r₀ : B)
    (hr₀ : r₀ ∈ CanonicalCrossedFibre T down q₂ q₃)
    (hDirectionTrivial :
      ∀ δ : CanonicalCrossedDirection T down, (δ : B) = 0) :
    (∃ r ∈ CanonicalCrossedFibre T down q₂ q₃,
        IsQuaternionClassB (r + T.res β)) ↔
      IsQuaternionClassB (r₀ + T.res β) := by
  constructor
  · intro hExists
    rcases
        (exists_quaternionPoint_iff_exists_directionCorrection
          T down IsQuaternionClassB q₂ q₃ β r₀ hr₀).mp hExists with
      ⟨δ, hδQuaternion⟩
    simpa only [hDirectionTrivial δ, add_zero] using hδQuaternion
  · intro hr₀Quaternion
    exact ⟨r₀, hr₀, hr₀Quaternion⟩

/-- When the kernel of the chosen quadratic restriction consists of
quaternion classes, the translated point problem on the canonical fibre is
exactly a layer-constrained corestriction-linked quaternion lift. -/
theorem exists_quaternionPoint_iff_hasLayerKernelCorestrictionLinkedQuaternionLift
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C)
    (IsQuaternionClassB : B → Prop)
    (hKernelQuaternion :
      LayerRestrictionKernelConsistsOfQuaternionClasses
        down IsQuaternionClassB)
    (q₂ q₃ β : A) :
    (∃ r ∈ CanonicalCrossedFibre T down q₂ q₃,
        IsQuaternionClassB (r + T.res β)) ↔
      HasLayerKernelCorestrictionLinkedQuaternionLift
        T down IsQuaternionClassB (q₂ + q₃) β := by
  constructor
  · rintro ⟨r, ⟨hrDown, hrCor⟩, hrTranslate⟩
    exact
      ⟨r, hrDown, hKernelQuaternion r hrDown, hrCor, hrTranslate⟩
  · rintro ⟨r, hrDown, _, hrCor, hrTranslate⟩
    exact ⟨r, ⟨hrDown, hrCor⟩, hrTranslate⟩

/-- Forgetting the chosen upper layer sends a layer-constrained lift to the
unrestricted corestriction-linked lift.  The converse is precisely the
missing layer-incidence assertion and is not claimed here. -/
theorem hasCorestrictionLinkedQuaternionLift_of_layerKernel
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C)
    (IsQuaternionClassB : B → Prop)
    (α β : A)
    (h :
      HasLayerKernelCorestrictionLinkedQuaternionLift
        T down IsQuaternionClassB α β) :
    HasCorestrictionLinkedQuaternionLift
      T IsQuaternionClassB α β := by
  rcases h with ⟨r, _, hrQuaternion, hrCor, hrTranslate⟩
  exact ⟨r, hrQuaternion, hrCor, hrTranslate⟩

/-- A prescribed dual common splitter supplies separate upper-kernel
preimages of both prescribed base classes. -/
theorem exists_kernelPreimages_of_prescribedDualCommonSplitter
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (dualDown : A →+ E)
    (q₂ q₃ : A)
    (h : HasPrescribedDualCommonSplitter T down dualDown q₂ q₃) :
    (∃ s : B, down s = 0 ∧ T.cor s = q₂) ∧
      ∃ t : B, down t = 0 ∧ T.cor t = q₃ := by
  rcases h with ⟨hDual, hq₂, hq₃⟩
  have hq₂Image : q₂ ∈ AddSubgroup.map T.cor down.ker := by
    rw [hDual]
    simpa only [AddMonoidHom.mem_ker] using hq₂
  have hq₃Image : q₃ ∈ AddSubgroup.map T.cor down.ker := by
    rw [hDual]
    simpa only [AddMonoidHom.mem_ker] using hq₃
  rw [AddSubgroup.mem_map] at hq₂Image hq₃Image
  rcases hq₂Image with ⟨s, hs, hcorS⟩
  rcases hq₃Image with ⟨t, ht, hcorT⟩
  exact ⟨⟨s, hs, hcorS⟩, ⟨t, ht, hcorT⟩⟩

/-- The canonical total corestriction fibre is nonempty once both labels
come from the same upper-layer kernel. -/
theorem canonicalCrossedFibre_nonempty_of_prescribedDualCommonSplitter
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (dualDown : A →+ E)
    (q₂ q₃ : A)
    (h : HasPrescribedDualCommonSplitter T down dualDown q₂ q₃) :
    (CanonicalCrossedFibre T down q₂ q₃).Nonempty := by
  rcases exists_kernelPreimages_of_prescribedDualCommonSplitter
      T down dualDown q₂ q₃ h with
    ⟨⟨s, hs, hcorS⟩, ⟨t, ht, hcorT⟩⟩
  refine ⟨s + t, ?_, ?_⟩
  · rw [map_add, hs, ht, add_zero]
  · rw [map_add, hcorS, hcorT]

/-- Under prescribed dual incidence, the whole crossed-rectangle problem is
exactly the existence of one quaternion point in the translated canonical
affine fibre. -/
theorem hasCrossedQuaternionKernelRectangle_iff_exists_quaternionPoint
    (hA₂ : IsExponentTwo A) (hB₂ : IsExponentTwo B)
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (dualDown : A →+ E)
    (IsQuaternionClassB : B → Prop)
    (q₁ q₂ q₃ : A)
    (hFirst : T.res q₁ = 0)
    (h : HasPrescribedDualCommonSplitter T down dualDown q₂ q₃) :
    HasCrossedQuaternionKernelRectangle
        T down IsQuaternionClassB q₂ q₃ ↔
      ∃ r ∈ CanonicalCrossedFibre T down q₂ q₃,
        IsQuaternionClassB (r + T.res (q₁ + q₂)) := by
  rcases h with ⟨hDual, hq₂, hq₃⟩
  rw [hasCrossedQuaternionKernelRectangle_iff_dualConstituentSplitting_and_kernelComplement
    hA₂ hB₂ T down dualDown hDual IsQuaternionClassB
      q₁ q₂ q₃ hFirst]
  rw [and_iff_right hq₂]
  constructor
  · rintro ⟨r, hrDown, hrCor, hrQuaternion⟩
    exact ⟨r, ⟨hrDown, hrCor⟩, hrQuaternion⟩
  · rintro ⟨r, ⟨hrDown, hrCor⟩, hrQuaternion⟩
    exact ⟨r, hrDown, hrCor, hrQuaternion⟩

/-- If an explicit point in the LLT--Tignol canonical fibre has a
non-quaternion translate, then existence of the desired crossed rectangle
forces a nonzero simultaneous kernel direction that repairs that point. -/
theorem crossedRectangle_forces_nonzero_direction_of_bad_basepoint
    (hA₂ : IsExponentTwo A) (hB₂ : IsExponentTwo B)
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (dualDown : A →+ E)
    (IsQuaternionClassB : B → Prop)
    (q₁ q₂ q₃ : A)
    (hFirst : T.res q₁ = 0)
    (h : HasPrescribedDualCommonSplitter T down dualDown q₂ q₃)
    (r₀ : B)
    (hr₀ : r₀ ∈ CanonicalCrossedFibre T down q₂ q₃)
    (hr₀NotQuaternion :
      ¬ IsQuaternionClassB (r₀ + T.res (q₁ + q₂)))
    (hRectangle :
      HasCrossedQuaternionKernelRectangle
        T down IsQuaternionClassB q₂ q₃) :
    ∃ δ : CanonicalCrossedDirection T down,
      (δ : B) ≠ 0 ∧
        IsQuaternionClassB
          (r₀ + (δ : B) + T.res (q₁ + q₂)) := by
  apply
    exists_nonzero_directionCorrection_of_basepoint_not_quaternion
      T down IsQuaternionClassB q₂ q₃ (q₁ + q₂)
        r₀ hr₀ hr₀NotQuaternion
  exact
    (hasCrossedQuaternionKernelRectangle_iff_exists_quaternionPoint
      hA₂ hB₂ T down dualDown IsQuaternionClassB
        q₁ q₂ q₃ hFirst h).mp hRectangle

/-- Under prescribed-dual incidence, the crossed rectangle is equivalent to
the exact layer-constrained linked-lift condition.  This is the formal
frontier: the prescribed splitter supplies a nonempty affine fibre, but no
existence theorem here forces the required quaternion translate. -/
theorem hasCrossedQuaternionKernelRectangle_iff_hasLayerKernelLinkedLift
    (hA₂ : IsExponentTwo A) (hB₂ : IsExponentTwo B)
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (dualDown : A →+ E)
    (IsQuaternionClassB : B → Prop)
    (hKernelQuaternion :
      LayerRestrictionKernelConsistsOfQuaternionClasses
        down IsQuaternionClassB)
    (q₁ q₂ q₃ : A)
    (hFirst : T.res q₁ = 0)
    (h : HasPrescribedDualCommonSplitter T down dualDown q₂ q₃) :
    HasCrossedQuaternionKernelRectangle
        T down IsQuaternionClassB q₂ q₃ ↔
      HasLayerKernelCorestrictionLinkedQuaternionLift
        T down IsQuaternionClassB
          (q₂ + q₃) (q₁ + q₂) := by
  calc
    HasCrossedQuaternionKernelRectangle
          T down IsQuaternionClassB q₂ q₃ ↔
        ∃ r ∈ CanonicalCrossedFibre T down q₂ q₃,
          IsQuaternionClassB (r + T.res (q₁ + q₂)) :=
      hasCrossedQuaternionKernelRectangle_iff_exists_quaternionPoint
        hA₂ hB₂ T down dualDown IsQuaternionClassB
          q₁ q₂ q₃ hFirst h
    _ ↔
        HasLayerKernelCorestrictionLinkedQuaternionLift
          T down IsQuaternionClassB
            (q₂ + q₃) (q₁ + q₂) :=
      exists_quaternionPoint_iff_hasLayerKernelCorestrictionLinkedQuaternionLift
        T down IsQuaternionClassB hKernelQuaternion
          q₂ q₃ (q₁ + q₂)

/-- The LLT--Tignol prescribed common splitter closes incidence and leaves
only the translated quaternion-point question. -/
theorem prescribedDualCommonSplitter_reduces_crossedRectangle_to_quaternionPoint
    (hA₂ : IsExponentTwo A) (hB₂ : IsExponentTwo B)
    (T : QuadraticBrauerTransferModel A B)
    (down : B →+ C) (dualDown : A →+ E)
    (IsQuaternionClassB : B → Prop)
    (q₁ q₂ q₃ : A)
    (hFirst : T.res q₁ = 0)
    (h : HasPrescribedDualCommonSplitter T down dualDown q₂ q₃) :
    HasCrossedQuaternionKernelRectangle
        T down IsQuaternionClassB q₂ q₃ ↔
      ∃ r : B,
        down r = 0 ∧
          T.cor r = q₂ + q₃ ∧
          IsQuaternionClassB (r + T.res (q₁ + q₂)) := by
  constructor
  · intro hRectangle
    rcases
        (hasCrossedQuaternionKernelRectangle_iff_exists_quaternionPoint
          hA₂ hB₂ T down dualDown IsQuaternionClassB
            q₁ q₂ q₃ hFirst h).mp hRectangle with
      ⟨r, ⟨hrDown, hrCor⟩, hrQuaternion⟩
    exact ⟨r, hrDown, hrCor, hrQuaternion⟩
  · rintro ⟨r, hrDown, hrCor, hrQuaternion⟩
    apply
      (hasCrossedQuaternionKernelRectangle_iff_exists_quaternionPoint
        hA₂ hB₂ T down dualDown IsQuaternionClassB
          q₁ q₂ q₃ hFirst h).mpr
    exact ⟨r, ⟨hrDown, hrCor⟩, hrQuaternion⟩

/-- In the hard total-index-eight row, a successful crossed quaternion cannot
be split by a conjugation-stable quadratic layer.  Thus its common slot cannot
descend from the ground field. -/
theorem totalIndexEight_crossedQuaternion_has_no_stableSplittingLayer
    (I : BrauerIndexModel A)
    (T : QuadraticBrauerTransferModel A B)
    (split : B →+ C)
    (IsQuaternionClassB : B → Prop)
    (hBGT : StableLayerQuaternionCorestrictionHasIndexAtMostTwo
      I T split IsQuaternionClassB)
    (q₁ q₂ q₃ : A)
    (hTotal : I.index (q₁ + q₂ + q₃) = 8)
    (hFirst : I.index q₁ ≤ 2)
    (hOpposite : I.index (q₂ + q₃) ≤ 4)
    (s t : B)
    (hcorS : T.cor s = q₂)
    (hcorT : T.cor t = q₃)
    (hCrossQuaternion :
      IsQuaternionClassB (t + T.conjugate s))
    (hCrossSplit : split (t + T.conjugate s) = 0) :
    ¬ ConjugationPreservesLayerRestrictionKernel T split := by
  apply totalIndexEight_quaternionPreimageLayer_not_conjugationStable
    I T split IsQuaternionClassB hBGT
      q₁ (q₂ + q₃) (by simpa [add_assoc] using hTotal)
      hFirst hOpposite (t + T.conjugate s)
      hCrossQuaternion hCrossSplit
  rw [map_add, T.cor_conjugate, hcorT, hcorS, add_comm]

end RiemannResearch.E7.QuaternionTrialityPacket
