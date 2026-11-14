import RiemannResearch.CategoryTheory.LocalFamilyCRT
import Mathlib.Data.Fintype.Basic

/-!
# Quotient matching reconstruction in the regular-cover calculus

Source: user-provided argument, Theorem B of Categorical CRT: exact gluing and
energy (14 November 2026), following the binary-image formulation of Hoefnagel,
Characterizations of majority categories, https://arxiv.org/abs/1902.06920.

The matching object is specified by its projections and their actual binary
local realizability. The theorem proves that its canonical map is a regular
 epimorphism and identifies its complete kernel relation. Thus it is the quotient
by the intersection kernel, whenever the indicated matching object is supplied.
No equality in a common quotient is substituted for actual binary realizability.
-/

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.GeneralizedEquivalence

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {X : C} {I : Type w} {Y : I → C}

/-- Binary quotient data are realized over a regular-epimorphic cover. -/
def QuotientPair (q : (i : I) → X ⟶ Y i) {T : C}
    (a : (i : I) → T ⟶ Y i) (i j : I) : Prop :=
  ∃ (U : C) (p : U ⟶ T), IsRegularEpi p ∧ ∃ z : U ⟶ X,
    z ≫ q i = p ≫ a i ∧ z ≫ q j = p ≫ a j

/-- Finitely many quotient coordinates can be lifted over a common cover. -/
theorem finite_local_lifts (hc : RegularCoverCalculus (C := C))
    (q : (i : I) → X ⟶ Y i) (hq : ∀ i, IsRegularEpi (q i))
    {T : C} (a : (i : I) → T ⟶ Y i) (F : Finset I) :
    ∃ (U : C) (p : U ⟶ T), IsRegularEpi p ∧
      ∀ i ∈ F, ∃ x : U ⟶ X, x ≫ q i = p ≫ a i := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨T, 𝟙 T, inferInstance, by simp⟩
  | @insert j F hj ih =>
    obtain ⟨U, p, hp, hx⟩ := ih
    let V := pullback (q j) (p ≫ a j)
    let e : V ⟶ U := pullback.snd (q j) (p ≫ a j)
    have he : IsRegularEpi e := hc.pullback (q j) (p ≫ a j) (hq j)
    refine ⟨V, e ≫ p, hc.comp e p he hp, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with hij | hi
    · subst i
      refine ⟨pullback.fst (q j) (p ≫ a j), ?_⟩
      simpa only [Category.assoc] using (pullback.condition (f := q j) (g := p ≫ a j))
    · obtain ⟨x, hxi⟩ := hx i hi
      refine ⟨e ≫ x, ?_⟩
      simpa only [Category.assoc] using congrArg (fun k => e ≫ k) hxi

/-- A binary quotient witness, after coordinate lifts, is a witness for the
actual composite of the kernel relations. -/
theorem quotientPair_kernel (hc : RegularCoverCalculus (C := C))
    {q : (i : I) → X ⟶ Y i} {T U : C} {a : (i : I) → T ⟶ Y i}
    (p : U ⟶ T) (x : I → (U ⟶ X))
    (hx : ∀ i, x i ≫ q i = p ≫ a i) {i j : I}
    (h : QuotientPair q a i j) :
    LocalComp (kernel (q i)) (kernel (q j)) (x i) (x j) := by
  obtain ⟨V, e, he, z, hzi, hzj⟩ := h
  refine ⟨pullback e p, pullback.snd e p, hc.pullback e p he,
    pullback.fst e p ≫ z, ?_, ?_⟩
  · change (pullback.snd e p ≫ x i) ≫ q i =
      (pullback.fst e p ≫ z) ≫ q i
    rw [Category.assoc, hx i, Category.assoc, hzi]
    simp only [← Category.assoc, pullback.condition]
  · change (pullback.fst e p ≫ z) ≫ q j =
      (pullback.snd e p ≫ x j) ≫ q j
    rw [Category.assoc, hzj, Category.assoc, hx j]
    simp only [← Category.assoc, pullback.condition]

/-- Finite compatible quotient data have a simultaneous local lift. -/
theorem quotient_crt_local_lift [Fintype I] [Nonempty I]
    (hc : RegularCoverCalculus (C := C))
    (q : (i : I) → X ⟶ Y i) (hq : ∀ i, IsRegularEpi (q i))
    (hglue : LocalGluing (fun i => kernel (q i)))
    {T : C} (a : (i : I) → T ⟶ Y i) (ha : ∀ i j, QuotientPair q a i j) :
    ∃ (U : C) (p : U ⟶ T), IsRegularEpi p ∧ ∃ z : U ⟶ X,
      ∀ i, z ≫ q i = p ≫ a i := by
  classical
  obtain ⟨U, p, hp, hx⟩ := finite_local_lifts hc q hq a Finset.univ
  have hxall : ∀ i, ∃ x : U ⟶ X, x ≫ q i = p ≫ a i :=
    fun i => hx i (Finset.mem_univ i)
  choose x hx using hxall
  have hcomp : LocalCompatible (fun i => kernel (q i)) Finset.univ x := by
    intro i _ j _
    exact quotientPair_kernel hc p x hx (ha i j)
  obtain ⟨V, e, he, z, hz⟩ := hasLocalFiniteCRT_of_localGluing hc hglue
    Finset.univ Finset.univ_nonempty U x hcomp
  refine ⟨V, e ≫ p, hc.comp e p he hp, z, ?_⟩
  intro i
  have hzi : z ≫ q i = (e ≫ x i) ≫ q i := hz i (Finset.mem_univ i)
  simpa only [Category.assoc, hx i] using hzi

/-- The canonical map to an actual finite binary matching object is a regular
 epimorphism. The projection hypothesis is the membership condition defining
that matching object, stated on generalized points. -/
theorem quotient_matching_isRegularEpi [Fintype I] [Nonempty I]
    (hc : RegularCoverCalculus (C := C))
    (q : (i : I) → X ⟶ Y i) (hq : ∀ i, IsRegularEpi (q i))
    (hglue : LocalGluing (fun i => kernel (q i)))
    {M : C} (π : (i : I) → M ⟶ Y i) (f : X ⟶ M)
    (hf : ∀ i, f ≫ π i = q i)
    (hmono : ∀ {T : C} (a b : T ⟶ M), (∀ i, a ≫ π i = b ≫ π i) → a = b)
    (hmatch : ∀ i j, QuotientPair q π i j) : IsRegularEpi f := by
  obtain ⟨U, p, hp, z, hz⟩ := quotient_crt_local_lift hc q hq hglue π hmatch
  letI : IsRegularEpi p := hp
  apply isRegularEpi_of_cover_factor hc p z f
  apply hmono
  intro i
  simpa only [Category.assoc, hf i] using hz i

/-- The matching quotient's kernel is exactly the intersection of all
coordinate kernels, on every generalized point. -/
theorem quotient_matching_kernel
    (q : (i : I) → X ⟶ Y i) {M : C} (π : (i : I) → M ⟶ Y i) (f : X ⟶ M)
    (hf : ∀ i, f ≫ π i = q i)
    (hmono : ∀ {T : C} (a b : T ⟶ M), (∀ i, a ≫ π i = b ≫ π i) → a = b)
    {T : C} (a b : T ⟶ X) :
    a ≫ f = b ≫ f ↔ ∀ i, a ≫ q i = b ≫ q i := by
  constructor
  · intro h i
    simpa only [Category.assoc, hf i] using congrArg (fun k => k ≫ π i) h
  · intro h
    apply hmono
    intro i
    simpa only [Category.assoc, hf i] using h i


/-- If the common kernel is the diagonal, matching reconstruction is an
isomorphism and all generalized points lift uniquely without covers. -/
theorem quotient_matching_isIso [Fintype I] [Nonempty I]
    (hc : RegularCoverCalculus (C := C))
    (q : (i : I) → X ⟶ Y i) (hq : ∀ i, IsRegularEpi (q i))
    (hglue : LocalGluing (fun i => kernel (q i)))
    {M : C} (π : (i : I) → M ⟶ Y i) (f : X ⟶ M)
    (hf : ∀ i, f ≫ π i = q i)
    (hmono : ∀ {T : C} (a b : T ⟶ M), (∀ i, a ≫ π i = b ≫ π i) → a = b)
    (hmatch : ∀ i j, QuotientPair q π i j)
    (hsep : ∀ {T : C} (a b : T ⟶ X), (∀ i, a ≫ q i = b ≫ q i) → a = b) :
    IsIso f := by
  haveI : IsRegularEpi f := quotient_matching_isRegularEpi hc q hq hglue π f hf hmono hmatch
  haveI : Mono f := ⟨by
    intro T a b hab
    exact hsep a b ((quotient_matching_kernel q π f hf hmono a b).mp hab)⟩
  exact isIso_of_regularEpi_of_mono f (IsRegularEpi.getStruct f)


/-- Universal property of binary matching: any compatible tuple has a unique
map to a jointly monic quotient-image cone. This avoids assuming that the
matching object has already been constructed. -/
theorem quotient_image_matching_universal [Fintype I] [Nonempty I]
    (hc : RegularCoverCalculus (C := C))
    (q : (i : I) → X ⟶ Y i) (hq : ∀ i, IsRegularEpi (q i))
    (hglue : LocalGluing (fun i => kernel (q i)))
    {M : C} (π : (i : I) → M ⟶ Y i) (f : X ⟶ M)
    (hf : ∀ i, f ≫ π i = q i)
    (hmono : ∀ {T : C} (a b : T ⟶ M), (∀ i, a ≫ π i = b ≫ π i) → a = b)
    {T : C} (a : (i : I) → T ⟶ Y i) (ha : ∀ i j, QuotientPair q a i j) :
    ∃! b : T ⟶ M, ∀ i, b ≫ π i = a i := by
  obtain ⟨U, p, hp, z, hz⟩ := quotient_crt_local_lift hc q hq hglue a ha
  haveI : IsRegularEpi p := hp
  have hw : IsRegularEpi.left p ≫ (z ≫ f) = IsRegularEpi.right p ≫ (z ≫ f) := by
    apply hmono
    intro i
    simp only [Category.assoc, hf i, hz i]
    simpa only [Category.assoc] using congrArg (fun k => k ≫ a i) (IsRegularEpi.w p)
  let b : T ⟶ M := IsRegularEpi.desc p (z ≫ f) hw
  have hb : p ≫ b = z ≫ f := IsRegularEpi.fac p (z ≫ f) hw
  have hbi : ∀ i, b ≫ π i = a i := by
    intro i
    apply (cancel_epi p).mp
    rw [← Category.assoc, hb, Category.assoc, hf i]
    exact hz i
  refine ⟨b, hbi, ?_⟩
  intro c hc
  exact hmono c b (fun i => (hc i).trans (hbi i).symm)

/-- Every generalized point in a quotient image satisfies the actual binary
image conditions. Together with `quotient_image_matching_universal`, this
identifies the regular image with the matching object. -/
theorem quotient_image_pairwise (hc : RegularCoverCalculus (C := C))
    (q : (i : I) → X ⟶ Y i) {M : C} (π : (i : I) → M ⟶ Y i)
    (f : X ⟶ M) [IsRegularEpi f] (hf : ∀ i, f ≫ π i = q i)
    {T : C} (b : T ⟶ M) (i j : I) :
    QuotientPair q (fun k => b ≫ π k) i j := by
  refine ⟨pullback f b, pullback.snd f b, hc.pullback f b inferInstance,
    pullback.fst f b, ?_, ?_⟩
  · rw [← hf i, ← Category.assoc, pullback.condition, Category.assoc]
  · rw [← hf j, ← Category.assoc, pullback.condition, Category.assoc]

/-- The regular-epi reconstruction conclusion is stable under arbitrary change
of parameters. -/
theorem quotient_matching_pullback [Fintype I] [Nonempty I]
    (hc : RegularCoverCalculus (C := C))
    (q : (i : I) → X ⟶ Y i) (hq : ∀ i, IsRegularEpi (q i))
    (hglue : LocalGluing (fun i => kernel (q i)))
    {M : C} (π : (i : I) → M ⟶ Y i) (f : X ⟶ M)
    (hf : ∀ i, f ≫ π i = q i)
    (hmono : ∀ {T : C} (a b : T ⟶ M), (∀ i, a ≫ π i = b ≫ π i) → a = b)
    (hmatch : ∀ i j, QuotientPair q π i j) {T : C} (b : T ⟶ M) :
    IsRegularEpi (pullback.snd f b) :=
  hc.pullback f b (quotient_matching_isRegularEpi hc q hq hglue π f hf hmono hmatch)

end CategoryTheory.GeneralizedEquivalence
