import RiemannResearch.CategoryTheory.QuotientMatchingCRT
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# The categorical overlap-equalizer CRT

Source: user-provided argument, formula (C) of Categorical CRT: exact gluing and
energy (14 November 2026). The overlap objects and their reduction maps are
supplied with the exact criterion that equality in each overlap is local binary
realizability. Effective permuting join quotients provide that criterion; it is
not inferred from arbitrary equality in a common quotient.

The matching object is constructed as the equalizer of the two product maps.
The theorem identifies its quotient map, complete common kernel, and the
isomorphism case. The finite-product and equalizer instances are the relevant
finite limits, so a global finite-limit typeclass is unnecessary.
-/

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.GeneralizedEquivalence

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {X : C} {I : Type w} {Y : I → C} {O : I × I → C}
variable [HasProduct Y] [HasProduct O]

/-- The first coordinate of each pair, reduced to its overlap. -/
noncomputable def overlapProductLeft (l : (p : I × I) → Y p.1 ⟶ O p) :
    (∏ᶜ Y) ⟶ ∏ᶜ O :=
  Pi.lift (fun p => Pi.π Y p.1 ≫ l p)

/-- The second coordinate of each pair, reduced to its overlap. -/
noncomputable def overlapProductRight (r : (p : I × I) → Y p.2 ⟶ O p) :
    (∏ᶜ Y) ⟶ ∏ᶜ O :=
  Pi.lift (fun p => Pi.π Y p.2 ≫ r p)

/-- Formula (C), with an explicitly constructed categorical equalizer.
The overlap criterion is exactly where effective join quotients and
permutability enter; the gluing law is the independent finite CRT condition. -/
theorem exists_overlap_equalizer_quotient [Fintype I] [Nonempty I]
    (hc : RegularCoverCalculus (C := C))
    (q : (i : I) → X ⟶ Y i) (hq : ∀ i, IsRegularEpi (q i))
    (hglue : LocalGluing (fun i => kernel (q i)))
    (l : (p : I × I) → Y p.1 ⟶ O p)
    (r : (p : I × I) → Y p.2 ⟶ O p)
    [HasEqualizer (overlapProductLeft l) (overlapProductRight r)]
    (hoverlap : ∀ (T : C) (a : (i : I) → T ⟶ Y i) (i j : I),
      a i ≫ l (i, j) = a j ≫ r (i, j) ↔ QuotientPair q a i j) :
    ∃ f : X ⟶ equalizer (overlapProductLeft l) (overlapProductRight r),
      IsRegularEpi f ∧
      (∀ i, f ≫ (equalizer.ι (overlapProductLeft l) (overlapProductRight r) ≫ Pi.π Y i) = q i) ∧
      (∀ (T : C) (a b : T ⟶ X), a ≫ f = b ≫ f ↔ ∀ i, a ≫ q i = b ≫ q i) ∧
      ((∀ {T : C} (a b : T ⟶ X), (∀ i, a ≫ q i = b ≫ q i) → a = b) → IsIso f) := by
  let L := overlapProductLeft l
  let R := overlapProductRight r
  let M := equalizer L R
  let π : (i : I) → M ⟶ Y i := fun i => equalizer.ι L R ≫ Pi.π Y i
  have hqoverlap : ∀ i j, q i ≫ l (i, j) = q j ≫ r (i, j) := by
    intro i j
    apply (hoverlap X q i j).mpr
    exact ⟨X, 𝟙 X, inferInstance, 𝟙 X, by simp, by simp⟩
  have hw : Pi.lift q ≫ L = Pi.lift q ≫ R := by
    apply Pi.hom_ext
    rintro ⟨i, j⟩
    simpa [L, R, overlapProductLeft, overlapProductRight, Category.assoc] using hqoverlap i j
  let f : X ⟶ M := equalizer.lift (Pi.lift q) hw
  have hf : ∀ i, f ≫ π i = q i := by
    intro i
    dsimp [f, π]
    rw [← Category.assoc, equalizer.lift_ι, Pi.lift_π]
  have hmono : ∀ {T : C} (a b : T ⟶ M),
      (∀ i, a ≫ π i = b ≫ π i) → a = b := by
    intro T a b hab
    apply (cancel_mono (equalizer.ι L R)).mp
    apply Pi.hom_ext
    intro i
    simpa only [Category.assoc] using hab i
  have hmatch : ∀ i j, QuotientPair q π i j := by
    intro i j
    apply (hoverlap M π i j).mp
    have hh := congrArg (fun k => k ≫ Pi.π O (i, j)) (equalizer.condition L R)
    dsimp [π, M]
    simp only [Category.assoc]
    simpa only [Category.assoc, L, R, overlapProductLeft, overlapProductRight, Pi.lift_π] using hh
  refine ⟨f, quotient_matching_isRegularEpi hc q hq hglue π f hf hmono hmatch, hf, ?_, ?_⟩
  · intro T a b
    exact quotient_matching_kernel q π f hf hmono a b
  · intro hsep
    exact quotient_matching_isIso hc q hq hglue π f hf hmono hmatch hsep

end CategoryTheory.GeneralizedEquivalence
