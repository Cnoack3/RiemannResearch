import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import RiemannResearch.CategoryTheory.QuotientMatchingCRT
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Construction of the matching quotient from regular images

Source: user-provided argument, Theorem B of Categorical CRT: exact gluing and
energy (14 November 2026). This module constructs the object, rather than
requiring a pre-existing matching cone. The general image construction uses
finite products, regular-image factorizations, and the regular-cover calculus.
The final structural provider derives that calculus from the standard regular-
category data: finite limits, regular epi–mono factorizations, and pullback
stability. Composition stability is proved rather than assumed. Thus the final
CRT statements apply directly to arbitrary regular categories.
-/

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A regular image factorization of one morphism. -/
structure RegularImageFactorization {A B : C} (f : A ⟶ B) where
  object : C
  epi : A ⟶ object
  mono : object ⟶ B
  fac : epi ≫ mono = f
  epi_regular : IsRegularEpi epi
  mono_monic : Mono mono

/-- The regular-image part of a regular category's structure. -/
class HasRegularImageFactorizations (C : Type u) [Category.{v} C] : Prop where
  exists_factorization : ∀ {A B : C} (f : A ⟶ B), Nonempty (RegularImageFactorization f)

namespace GeneralizedEquivalence

variable [HasPullbacks C] {X : C} {I : Type w} {Y : I → C}

/-- Finite categorical CRT, including existence of the matching quotient.
The quotient is the regular image of the joint map into the product. Its
universal property is the full binary-image matching condition, and its kernel
is the intersection of the coordinate kernels. -/
theorem exists_matching_quotient [Fintype I] [Nonempty I] [HasProduct Y]
    [HasRegularImageFactorizations C]
    (hc : RegularCoverCalculus (C := C))
    (q : (i : I) → X ⟶ Y i) (hq : ∀ i, IsRegularEpi (q i))
    (hglue : LocalGluing (fun i => kernel (q i))) :
    ∃ (M : C) (f : X ⟶ M) (π : (i : I) → M ⟶ Y i),
      IsRegularEpi f ∧
      (∀ i, f ≫ π i = q i) ∧
      (∀ {T : C} (a b : T ⟶ M), (∀ i, a ≫ π i = b ≫ π i) → a = b) ∧
      (∀ (T : C) (a : (i : I) → T ⟶ Y i),
        (∀ i j, QuotientPair q a i j) ↔ ∃! b : T ⟶ M, ∀ i, b ≫ π i = a i) ∧
      (∀ (T : C) (a b : T ⟶ X), a ≫ f = b ≫ f ↔ ∀ i, a ≫ q i = b ≫ q i) := by
  obtain ⟨r⟩ := HasRegularImageFactorizations.exists_factorization (Pi.lift q)
  let π : (i : I) → r.object ⟶ Y i := fun i => r.mono ≫ Pi.π Y i
  haveI : IsRegularEpi r.epi := r.epi_regular
  haveI : Mono r.mono := r.mono_monic
  have hf : ∀ i, r.epi ≫ π i = q i := by
    intro i
    dsimp [π]
    rw [← Category.assoc, r.fac, Pi.lift_π]
  have hmono : ∀ {T : C} (a b : T ⟶ r.object),
      (∀ i, a ≫ π i = b ≫ π i) → a = b := by
    intro T a b hab
    apply (cancel_mono r.mono).mp
    apply Pi.hom_ext
    intro i
    simpa only [Category.assoc] using hab i
  refine ⟨r.object, r.epi, π, r.epi_regular, hf, hmono, ?_, ?_⟩
  · intro T a
    constructor
    · exact quotient_image_matching_universal hc q hq hglue π r.epi hf hmono a
    · rintro ⟨b, hb, _⟩ i j
      have hh := quotient_image_pairwise hc q π r.epi hf b i j
      simpa only [hb] using hh
  · intro T a b
    exact quotient_matching_kernel q π r.epi hf hmono a b

end GeneralizedEquivalence
end CategoryTheory

namespace CategoryTheory
variable {C : Type u} [Category.{v} C]

/-- Regular epimorphisms are extremal: a monic factor through which one
factors is necessarily an isomorphism. -/
theorem isIso_mono_of_regularEpi_factor {A B D : C}
    (g : A ⟶ D) [IsRegularEpi g] (h : A ⟶ B) (m : B ⟶ D)
    [Mono m] (hfac : h ≫ m = g) : IsIso m := by
  have hw : IsRegularEpi.left g ≫ h = IsRegularEpi.right g ≫ h := by
    apply (cancel_mono m).mp
    simpa only [Category.assoc, hfac] using IsRegularEpi.w g
  let s : D ⟶ B := IsRegularEpi.desc g h hw
  have hs : g ≫ s = h := IsRegularEpi.fac g h hw
  have h₁ : s ≫ m = 𝟙 D := by
    apply (cancel_epi g).mp
    rw [← Category.assoc, hs, hfac, Category.comp_id]
  have h₂ : m ≫ s = 𝟙 B := by
    apply (cancel_mono m).mp
    rw [Category.assoc, h₁, Category.comp_id, Category.id_comp]
  exact ⟨⟨s, h₂, h₁⟩⟩

/-- Closure under composition is derived from regular-image factorizations;
it is not an extra regular-category or CRT axiom. -/
theorem regularEpi_comp_of_regularImages [HasPullbacks C] [HasRegularImageFactorizations C]
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D)
    [IsRegularEpi f] [IsRegularEpi g] : IsRegularEpi (f ≫ g) := by
  obtain ⟨r⟩ := HasRegularImageFactorizations.exists_factorization (f ≫ g)
  haveI : IsRegularEpi r.epi := r.epi_regular
  haveI : Mono r.mono := r.mono_monic
  have hw : IsRegularEpi.left f ≫ r.epi = IsRegularEpi.right f ≫ r.epi := by
    apply (cancel_mono r.mono).mp
    rw [Category.assoc, r.fac, Category.assoc, r.fac, ← Category.assoc,
      ← Category.assoc, IsRegularEpi.w f]
  let h : B ⟶ r.object := IsRegularEpi.desc f r.epi hw
  have hh : f ≫ h = r.epi := IsRegularEpi.fac f r.epi hw
  have hfac : h ≫ r.mono = g := by
    apply (cancel_epi f).mp
    rw [← Category.assoc, hh, r.fac]
  haveI : IsIso r.mono := isIso_mono_of_regularEpi_factor g h r.mono hfac
  apply IsRegularEpi.of_epi_of_exists
  intro Z k hk
  have hwk : IsRegularEpi.left r.epi ≫ k = IsRegularEpi.right r.epi ≫ k := by
    apply equal_of_kernelPair hk
    have he := congrArg (fun t => t ≫ r.mono) (IsRegularEpi.w r.epi)
    simpa only [Category.assoc, r.fac] using he
  let z : r.object ⟶ Z := IsRegularEpi.desc r.epi k hwk
  refine ⟨inv r.mono ≫ z, ?_⟩
  calc
    (f ≫ g) ≫ (inv r.mono ≫ z) =
        (r.epi ≫ r.mono) ≫ (inv r.mono ≫ z) :=
      congrArg (fun t => t ≫ (inv r.mono ≫ z)) r.fac.symm
    _ = r.epi ≫ z := by simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    _ = k := IsRegularEpi.fac r.epi k hwk

/-- Standard regular-category structure on a finitely complete category:
regular epi–mono factorizations and pullback-stable regular epimorphisms.
Composition stability is proved above rather than included in this structure. -/
class RegularCategoryStructure (C : Type u) [Category.{v} C] [HasFiniteLimits C]
    : Prop extends HasRegularImageFactorizations C where
  regularEpi_pullback : ∀ {A B D : C} (p : A ⟶ D) (f : B ⟶ D),
    IsRegularEpi p → IsRegularEpi (pullback.snd p f)

/-- The local-witness calculus is a theorem of standard regular-category data. -/
theorem regularCoverCalculusOfRegular [HasFiniteLimits C] [RegularCategoryStructure C] :
    RegularCoverCalculus (C := C) where
  comp := by
    intro A B D p q hp hq
    letI := hp
    letI := hq
    exact regularEpi_comp_of_regularImages p q
  pullback := RegularCategoryStructure.regularEpi_pullback

namespace InternalEquivalencePresentation
variable [HasFiniteLimits C] [RegularCategoryStructure C] {X : C}

/-- The hereditary family CRT criterion in any regular category, with no
separately supplied cover calculus and no effective-quotient hypothesis. -/
theorem finite_crt_iff_gluing_of_regular {I : Type w}
    (R : I → InternalEquivalencePresentation X) :
    GeneralizedEquivalence.HasLocalFiniteCRT (fun i => (R i).toGeneralized) ↔
      GeneralizedEquivalence.LocalGluing (fun i => (R i).toGeneralized) :=
  finite_crt_iff_gluing regularCoverCalculusOfRegular R

end InternalEquivalencePresentation

namespace GeneralizedEquivalence
variable [HasFiniteLimits C] [RegularCategoryStructure C]
variable {X : C} {I : Type w} {Y : I → C}

/-- The finite joint-image matching quotient exists in every regular category.
Finite limits supply the joint product; regular images supply the quotient. -/
theorem exists_matching_quotient_of_regular [Fintype I] [Nonempty I]
    (q : (i : I) → X ⟶ Y i) (hq : ∀ i, IsRegularEpi (q i))
    (hglue : LocalGluing (fun i => kernel (q i))) :
    ∃ (M : C) (f : X ⟶ M) (π : (i : I) → M ⟶ Y i),
      IsRegularEpi f ∧
      (∀ i, f ≫ π i = q i) ∧
      (∀ {T : C} (a b : T ⟶ M), (∀ i, a ≫ π i = b ≫ π i) → a = b) ∧
      (∀ (T : C) (a : (i : I) → T ⟶ Y i),
        (∀ i j, QuotientPair q a i j) ↔ ∃! b : T ⟶ M, ∀ i, b ≫ π i = a i) ∧
      (∀ (T : C) (a b : T ⟶ X), a ≫ f = b ≫ f ↔ ∀ i, a ≫ q i = b ≫ q i) :=
  exists_matching_quotient regularCoverCalculusOfRegular q hq hglue

end GeneralizedEquivalence
end CategoryTheory
