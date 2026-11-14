import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Setoid.Basic

/-!
# Categorical CRT with regular-epimorphic local witnesses

Source: user-provided argument, Theorem A of Categorical CRT: exact gluing and
energy (14 November 2026); terminology and regular-category motivation from
Hoefnagel, Characterizations of majority categories, §4–5,
https://arxiv.org/abs/1902.06920.

Relations are represented by their equivalence relations on generalized points,
stable under precomposition. This encompasses internal equivalence relations.
Composition uses a regular-epimorphic cover, not an assumed global section.
The two regular-epimorphism stability hypotheses below are structural regular-
category hypotheses, not mathematical CRT or arithmetic assumptions.
The RH consumer is gluing arithmetic quotient constraints before energy bounds.
-/

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- The cover calculus used by regular logic. Both properties hold for the
regular epimorphisms of a regular category. -/
structure RegularCoverCalculus : Prop where
  comp : ∀ {A B D : C} (p : A ⟶ B) (q : B ⟶ D),
    IsRegularEpi p → IsRegularEpi q → IsRegularEpi (p ≫ q)
  pullback : ∀ {A B D : C} (p : A ⟶ D) (f : B ⟶ D),
    IsRegularEpi p → IsRegularEpi (pullback.snd p f)

/-- An equivalence relation on generalized points, stable under restriction.
For an internal equivalence relation, membership means factorization through
its representing relation object. -/
structure GeneralizedEquivalence (X : C) where
  rel : (T : C) → Setoid (T ⟶ X)
  precomp : ∀ {T U : C} (p : U ⟶ T) {a b : T ⟶ X},
    rel T a b → rel U (p ≫ a) (p ≫ b)

namespace GeneralizedEquivalence

variable {X : C} {I : Type w}

/-- Actual binary compatibility, witnessed locally over a regular epimorphism. -/
def LocalComp (R S : GeneralizedEquivalence X) {T : C} (a b : T ⟶ X) : Prop :=
  ∃ (U : C) (p : U ⟶ T), IsRegularEpi p ∧
    ∃ z : U ⟶ X, R.rel U (p ≫ a) z ∧ S.rel U z (p ≫ b)

/-- A solution over a regular-epimorphic cover of the parameter object. -/
def LocalSolution (R : I → GeneralizedEquivalence X) (F : Finset I)
    {T : C} (a : I → (T ⟶ X)) : Prop :=
  ∃ (U : C) (p : U ⟶ T), IsRegularEpi p ∧
    ∃ z : U ⟶ X, ∀ i ∈ F, (R i).rel U z (p ≫ a i)

def LocalCompatible (R : I → GeneralizedEquivalence X) (F : Finset I)
    {T : C} (a : I → (T ⟶ X)) : Prop :=
  ∀ i ∈ F, ∀ j ∈ F, LocalComp (R i) (R j) (a i) (a j)

def HasLocalFiniteCRT (R : I → GeneralizedEquivalence X) : Prop :=
  ∀ F : Finset I, F.Nonempty → ∀ (T : C) (a : I → (T ⟶ X)),
    LocalCompatible R F a → LocalSolution R F a

/-- The exact local composition/intersection law, at every parameter object. -/
def LocalGluing (R : I → GeneralizedEquivalence X) : Prop :=
  ∀ F : Finset I, F.Nonempty → ∀ j, j ∉ F → ∀ (T : C) (a b : T ⟶ X),
    (∀ i ∈ F, LocalComp (R i) (R j) a b) ↔
      ∃ (U : C) (p : U ⟶ T), IsRegularEpi p ∧ ∃ z : U ⟶ X,
        (∀ i ∈ F, (R i).rel U (p ≫ a) z) ∧ (R j).rel U z (p ≫ b)

theorem localComp_self (R S : GeneralizedEquivalence X) {T : C} (a : T ⟶ X) :
    LocalComp R S a a := by
  refine ⟨T, 𝟙 T, inferInstance, a, ?_, ?_⟩ <;> simp

theorem localComp_swap {R S : GeneralizedEquivalence X} {T : C} {a b : T ⟶ X}
    (h : LocalComp R S a b) : LocalComp S R b a := by
  obtain ⟨U, p, hp, z, hzR, hzS⟩ := h
  exact ⟨U, p, hp, z, (S.rel U).symm hzS, (R.rel U).symm hzR⟩

theorem localComp_precomp (hc : RegularCoverCalculus (C := C))
    {R S : GeneralizedEquivalence X} {T V : C} {a b : T ⟶ X}
    (h : LocalComp R S a b) (f : V ⟶ T) :
    LocalComp R S (f ≫ a) (f ≫ b) := by
  obtain ⟨U, p, hp, z, hzR, hzS⟩ := h
  refine ⟨pullback p f, pullback.snd p f, hc.pullback p f hp,
    pullback.fst p f ≫ z, ?_, ?_⟩
  · have hh := R.precomp (pullback.fst p f) hzR
    simpa only [← Category.assoc, pullback.condition] using hh
  · have hh := S.precomp (pullback.fst p f) hzS
    simpa only [← Category.assoc, pullback.condition] using hh

theorem localComp_left_trans {R S : GeneralizedEquivalence X}
    {T : C} {x a b : T ⟶ X} (hx : R.rel T x a)
    (h : LocalComp R S a b) : LocalComp R S x b := by
  obtain ⟨U, p, hp, z, hzR, hzS⟩ := h
  exact ⟨U, p, hp, z, (R.rel U).trans (R.precomp p hx) hzR, hzS⟩

/-- The sufficiency proof combines witnesses by pullback and composition of
covers; it does not assume any regular epimorphism splits. -/
theorem hasLocalFiniteCRT_of_localGluing (hc : RegularCoverCalculus (C := C))
    {R : I → GeneralizedEquivalence X} (h : LocalGluing R) :
    HasLocalFiniteCRT R := by
  classical
  intro F
  induction F using Finset.induction_on with
  | empty => simp
  | @insert j F hj ih =>
    intro hF T a ha
    by_cases hne : F.Nonempty
    · obtain ⟨U, p, hp, x, hx⟩ := ih hne T a (by
        intro i hi k hk
        exact ha i (Finset.mem_insert_of_mem hi) k (Finset.mem_insert_of_mem hk))
      have hpair : ∀ i ∈ F, LocalComp (R i) (R j) x (p ≫ a j) := by
        intro i hi
        exact localComp_left_trans (hx i hi)
          (localComp_precomp hc (ha i (Finset.mem_insert_of_mem hi) j (by simp)) p)
      obtain ⟨V, q, hq, z, hz, hzj⟩ := (h F hne j hj U x (p ≫ a j)).mp hpair
      refine ⟨V, q ≫ p, hc.comp q p hq hp, z, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simpa only [Category.assoc] using hzj
      · have hxi := (R i).precomp q (hx i hi)
        have hzi := ((R i).rel V).trans (((R i).rel V).symm (hz i hi)) hxi
        simpa only [Category.assoc] using hzi
    · have hF0 : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst F
      refine ⟨T, 𝟙 T, inferInstance, a j, ?_⟩
      intro i hi
      have hij : i = j := by simpa using hi
      subst i
      simp

/-- Necessity uses the same old target for each previous constraint. -/
theorem localGluing_of_hasLocalFiniteCRT
    {R : I → GeneralizedEquivalence X} (h : HasLocalFiniteCRT R) :
    LocalGluing R := by
  classical
  intro F hF j hj T a b
  constructor
  · intro hp
    let target : I → (T ⟶ X) := fun i => if i = j then b else a
    have ht : LocalCompatible R (insert j F) target := by
      intro i hi k hk
      by_cases hij : i = j
      · subst i
        by_cases hkj : k = j
        · subst k
          simpa [target] using localComp_self (R j) (R j) b
        · have hkF : k ∈ F := (Finset.mem_insert.mp hk).resolve_left hkj
          simpa [target, hkj] using localComp_swap (hp k hkF)
      · have hiF : i ∈ F := (Finset.mem_insert.mp hi).resolve_left hij
        by_cases hkj : k = j
        · subst k
          simpa [target, hij] using hp i hiF
        · simpa [target, hij, hkj] using localComp_self (R i) (R k) a
    obtain ⟨U, p, hp, z, hz⟩ := h (insert j F) (Finset.insert_nonempty j F) T target ht
    refine ⟨U, p, hp, z, ?_, ?_⟩
    · intro i hi
      have hij : i ≠ j := by intro hh; subst i; exact hj hi
      exact ((R i).rel U).symm (by simpa [target, hij] using hz i (Finset.mem_insert_of_mem hi))
    · simpa [target] using hz j (by simp)
  · rintro ⟨U, p, hp, z, hz, hzj⟩ i hi
    exact ⟨U, p, hp, z, hz i hi, hzj⟩

/-- Categorical family CRT: exact local gluing is necessary and sufficient. -/
theorem hasLocalFiniteCRT_iff_localGluing (hc : RegularCoverCalculus (C := C))
    (R : I → GeneralizedEquivalence X) :
    HasLocalFiniteCRT R ↔ LocalGluing R :=
  ⟨localGluing_of_hasLocalFiniteCRT, hasLocalFiniteCRT_of_localGluing hc⟩

/-- Kernel relations of quotient maps give generalized equivalence relations. -/
def kernel {Y : C} (q : X ⟶ Y) : GeneralizedEquivalence X where
  rel T := ⟨fun a b => a ≫ q = b ≫ q,
    ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩⟩
  precomp := by
    intro T U p a b h
    simpa only [Category.assoc] using congrArg (fun k => p ≫ k) h

end GeneralizedEquivalence
end CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasPullbacks C] (X : C)

/-- A conventional internal equivalence-relation diagram. Joint monicity says
that its two projections represent a subobject of the binary product. -/
structure InternalEquivalencePresentation where
  object : C
  left : object ⟶ X
  right : object ⟶ X
  joint_monic : ∀ {T : C} (f g : T ⟶ object),
    f ≫ left = g ≫ left → f ≫ right = g ≫ right → f = g
  diagonal : X ⟶ object
  diagonal_left : diagonal ≫ left = 𝟙 X
  diagonal_right : diagonal ≫ right = 𝟙 X
  swap : object ⟶ object
  swap_left : swap ≫ left = right
  swap_right : swap ≫ right = left
  trans : pullback right left ⟶ object
  trans_left : trans ≫ left = pullback.fst right left ≫ left
  trans_right : trans ≫ right = pullback.snd right left ≫ right

namespace InternalEquivalencePresentation

variable {X}

/-- Membership of generalized points in an internal relation. -/
def Holds (R : InternalEquivalencePresentation X) {T : C} (a b : T ⟶ X) : Prop :=
  ∃ z : T ⟶ R.object, z ≫ R.left = a ∧ z ≫ R.right = b

def toGeneralized (R : InternalEquivalencePresentation X) : GeneralizedEquivalence X where
  rel T :=
    { r := R.Holds
      iseqv := by
        refine ⟨?_, ?_, ?_⟩
        · intro a
          exact ⟨a ≫ R.diagonal, by simp [Category.assoc, R.diagonal_left],
            by simp [Category.assoc, R.diagonal_right]⟩
        · rintro a b ⟨z, hzl, hzr⟩
          exact ⟨z ≫ R.swap, by simpa only [Category.assoc, R.swap_left] using hzr,
            by simpa only [Category.assoc, R.swap_right] using hzl⟩
        · rintro a b c ⟨z, hzl, hzr⟩ ⟨w, hwl, hwr⟩
          let t := pullback.lift z w (hzr.trans hwl.symm)
          refine ⟨t ≫ R.trans, ?_, ?_⟩
          · dsimp [t]
            rw [Category.assoc, R.trans_left, ← Category.assoc, pullback.lift_fst]
            exact hzl
          · dsimp [t]
            rw [Category.assoc, R.trans_right, ← Category.assoc, pullback.lift_snd]
            exact hwr }
  precomp := by
    intro T U p a b h
    obtain ⟨z, hzl, hzr⟩ := h
    exact ⟨p ≫ z, by simpa only [Category.assoc] using congrArg (fun k => p ≫ k) hzl,
      by simpa only [Category.assoc] using congrArg (fun k => p ≫ k) hzr⟩

/-- The exact local CRT applies to actual internal equivalence-relation
presentations. No quotient objects or effective equivalence relations are needed. -/
theorem finite_crt_iff_gluing (hc : RegularCoverCalculus (C := C))
    {I : Type w} (R : I → InternalEquivalencePresentation X) :
    GeneralizedEquivalence.HasLocalFiniteCRT (fun i => (R i).toGeneralized) ↔
    GeneralizedEquivalence.LocalGluing (fun i => (R i).toGeneralized) :=
  GeneralizedEquivalence.hasLocalFiniteCRT_iff_localGluing hc _

end InternalEquivalencePresentation
end CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- Equality on a kernel pair is equality on every generalized pair in its kernel. -/
theorem equal_of_kernelPair {X Y Z T : C} {f : X ⟶ Y} {g : X ⟶ Z}
    (h : pullback.fst f f ≫ g = pullback.snd f f ≫ g)
    (a b : T ⟶ X) (hab : a ≫ f = b ≫ f) : a ≫ g = b ≫ g := by
  have hh := congrArg (fun k => pullback.lift a b hab ≫ k) h
  simpa only [← Category.assoc, pullback.lift_fst, pullback.lift_snd] using hh

/-- In the stable regular-cover calculus, a right factor of a regular
 epimorphism is a regular epimorphism. This turns local lifting into quotient
reconstruction without choosing sections. -/
theorem isRegularEpi_of_cover_factor (hc : RegularCoverCalculus (C := C))
    {U X Y : C} (p : U ⟶ Y) [IsRegularEpi p] (z : U ⟶ X) (f : X ⟶ Y)
    (hf : z ≫ f = p) : IsRegularEpi f := by
  letI : Epi f := epi_of_epi_fac hf
  apply IsRegularEpi.of_epi_of_exists
  intro Z g hg
  have hw : (IsRegularEpi.left p ≫ z) ≫ f =
      (IsRegularEpi.right p ≫ z) ≫ f := by
    simpa only [Category.assoc, hf] using IsRegularEpi.w p
  have hzg : IsRegularEpi.left p ≫ (z ≫ g) =
      IsRegularEpi.right p ≫ (z ≫ g) := by
    simpa only [Category.assoc] using
      equal_of_kernelPair hg (IsRegularEpi.left p ≫ z) (IsRegularEpi.right p ≫ z) hw
  let d : Y ⟶ Z := IsRegularEpi.desc p (z ≫ g) hzg
  have hd : p ≫ d = z ≫ g := IsRegularEpi.fac p (z ≫ g) hzg
  refine ⟨d, ?_⟩
  let e := pullback.snd p f
  have he : IsRegularEpi e := hc.pullback p f inferInstance
  letI : IsRegularEpi e := he
  apply (cancel_epi e).mp
  have hk : (pullback.fst p f ≫ z) ≫ f = e ≫ f := by
    rw [Category.assoc, hf]
    exact pullback.condition
  have hkg := equal_of_kernelPair hg (pullback.fst p f ≫ z) e hk
  calc
    e ≫ (f ≫ d) = (pullback.fst p f ≫ p) ≫ d := by
      rw [← Category.assoc, ← pullback.condition]
    _ = pullback.fst p f ≫ (z ≫ g) := by rw [Category.assoc, hd]
    _ = e ≫ g := by simpa only [Category.assoc] using hkg

end CategoryTheory

namespace CategoryTheory.GeneralizedEquivalence

universe u' v'

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D] {X : C} {I : Type w}

/-- A regular-epimorphism-preserving functor transports every finite local
solution whenever it transports relation membership. For a regular functor,
the latter is obtained by applying the functor to the internal relation diagram.
This lemma concerns actual witnesses; it makes no global lifting assumption. -/
theorem localSolution_map (F : C ⥤ D)
    (hcover : ∀ {U T : C} (p : U ⟶ T), IsRegularEpi p → IsRegularEpi (F.map p))
    {R : I → GeneralizedEquivalence X} {S : I → GeneralizedEquivalence (F.obj X)}
    (hrel : ∀ i (T : C) (a b : T ⟶ X), (R i).rel T a b →
      (S i).rel (F.obj T) (F.map a) (F.map b))
    {J : Finset I} {T : C} {a : I → (T ⟶ X)} (h : LocalSolution R J a) :
    LocalSolution S J (fun i => F.map (a i)) := by
  obtain ⟨U, p, hp, z, hz⟩ := h
  refine ⟨F.obj U, F.map p, hcover p hp, F.map z, ?_⟩
  intro i hi
  simpa only [F.map_comp] using hrel i U z (p ≫ a i) (hz i hi)

/-- The same functoriality for the binary compatibility witnesses. -/
theorem localComp_map (F : C ⥤ D)
    (hcover : ∀ {U T : C} (p : U ⟶ T), IsRegularEpi p → IsRegularEpi (F.map p))
    {R S : GeneralizedEquivalence X} {R' S' : GeneralizedEquivalence (F.obj X)}
    (hR : ∀ (T : C) (a b : T ⟶ X), R.rel T a b →
      R'.rel (F.obj T) (F.map a) (F.map b))
    (hS : ∀ (T : C) (a b : T ⟶ X), S.rel T a b →
      S'.rel (F.obj T) (F.map a) (F.map b))
    {T : C} {a b : T ⟶ X} (h : LocalComp R S a b) :
    LocalComp R' S' (F.map a) (F.map b) := by
  obtain ⟨U, p, hp, z, hzR, hzS⟩ := h
  refine ⟨F.obj U, F.map p, hcover p hp, F.map z, ?_, ?_⟩
  · simpa only [F.map_comp] using hR U (p ≫ a) z hzR
  · simpa only [F.map_comp] using hS U z (p ≫ b) hzS

end CategoryTheory.GeneralizedEquivalence

namespace CategoryTheory.GeneralizedEquivalence

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {X : C} {I : Type w}

/-- Prefix-specific local gluing adjoins one constraint. Iteration only needs
these identities for the chosen prefixes, rather than the hereditary criterion. -/
theorem local_extend_solution [DecidableEq I] (hc : RegularCoverCalculus (C := C))
    {R : I → GeneralizedEquivalence X} {J : Finset I} {j : I}
    (step : ∀ (T : C) (a b : T ⟶ X),
      (∀ i ∈ J, LocalComp (R i) (R j) a b) →
        ∃ (U : C) (p : U ⟶ T), IsRegularEpi p ∧ ∃ z : U ⟶ X,
          (∀ i ∈ J, (R i).rel U (p ≫ a) z) ∧ (R j).rel U z (p ≫ b))
    {T : C} {a : I → (T ⟶ X)} (hx : LocalSolution R J a)
    (ha : ∀ i ∈ J, LocalComp (R i) (R j) (a i) (a j)) :
    LocalSolution R (insert j J) a := by
  classical
  obtain ⟨U, p, hp, x, hx⟩ := hx
  have hpair : ∀ i ∈ J, LocalComp (R i) (R j) x (p ≫ a j) := by
    intro i hi
    exact localComp_left_trans (hx i hi) (localComp_precomp hc (ha i hi) p)
  obtain ⟨V, q, hq, z, hz, hzj⟩ := step U x (p ≫ a j) hpair
  refine ⟨V, q ≫ p, hc.comp q p hq hp, z, ?_⟩
  intro i hi
  rcases Finset.mem_insert.mp hi with hij | hi
  · subst i
    simpa only [Category.assoc] using hzj
  · have hxi := (R i).precomp q (hx i hi)
    have hzi := ((R i).rel V).trans (((R i).rel V).symm (hz i hi)) hxi
    simpa only [Category.assoc] using hzi

end CategoryTheory.GeneralizedEquivalence
