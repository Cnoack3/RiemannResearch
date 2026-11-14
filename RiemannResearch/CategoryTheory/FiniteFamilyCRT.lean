import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Exact finite Chinese remainder criterion for a family

Source: user-provided argument, "Categorical CRT: exact gluing and energy",
14 November 2026, Theorems A and B. Related statement/terminology:
Cornish (1977), On the Chinese remainder theorem of H. Draškovičová;
Hoefnagel (2019), Characterizations of majority categories, §4–5,
https://arxiv.org/abs/1902.06920.

This module proves the set-level family criterion and quotient reconstruction.
The criterion uses actual binary solvability, without replacing it by a join.
Its RH consumer is the finite compatibility step before any uniform energy bound.
-/

namespace Setoid

variable {X I : Type*}

/-- Composition in the order `x R z S y`. -/
def crtComp (R S : Setoid X) (x y : X) : Prop :=
  ∃ z, R x z ∧ S z y

/-- Targets are compatible exactly when each pair has a common representative. -/
def CRTCompatible (R : I → Setoid X) (F : Finset I) (a : I → X) : Prop :=
  ∀ i ∈ F, ∀ j ∈ F, crtComp (R i) (R j) (a i) (a j)

/-- The hereditary finite CRT property, for nonempty finite systems. -/
def HasFiniteCRT (R : I → Setoid X) : Prop :=
  ∀ F : Finset I, F.Nonempty → ∀ a : I → X,
    CRTCompatible R F a → ∃ z, ∀ i ∈ F, R i z (a i)

/-- The family-local distributivity law for composition and finite intersections. -/
def CRTGluing (R : I → Setoid X) : Prop :=
  ∀ (F : Finset I), F.Nonempty → ∀ j, j ∉ F → ∀ x y,
    (∀ i ∈ F, crtComp (R i) (R j) x y) ↔
      ∃ z, (∀ i ∈ F, R i x z) ∧ R j z y

theorem hasFiniteCRT_of_crtGluing {R : I → Setoid X} (h : CRTGluing R) :
    HasFiniteCRT R := by
  classical
  intro F
  induction F using Finset.induction_on with
  | empty => simp
  | @insert j F hj ih =>
    intro hF a ha
    by_cases hne : F.Nonempty
    · obtain ⟨x, hx⟩ := ih hne a (by
        intro i hi k hk
        exact ha i (Finset.mem_insert_of_mem hi) k (Finset.mem_insert_of_mem hk))
      have hpair : ∀ i ∈ F, crtComp (R i) (R j) x (a j) := by
        intro i hi
        obtain ⟨z, hiz, hzj⟩ := ha i (Finset.mem_insert_of_mem hi) j (by simp)
        exact ⟨z, (R i).trans (hx i hi) hiz, hzj⟩
      obtain ⟨z, hz, hzj⟩ := (h F hne j hj x (a j)).mp hpair
      refine ⟨z, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hzj
      · exact (R i).trans ((R i).symm (hz i hi)) (hx i hi)
    · have hF0 : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst F
      refine ⟨a j, ?_⟩
      intro i hi
      have hij : i = j := by simpa using hi
      subst i
      exact (R j).refl _

theorem crtGluing_of_hasFiniteCRT {R : I → Setoid X} (h : HasFiniteCRT R) :
    CRTGluing R := by
  classical
  intro F hF j hj x y
  constructor
  · intro hp
    let a : I → X := fun i => if i = j then y else x
    have ha : CRTCompatible R (insert j F) a := by
      intro i hi k hk
      by_cases hij : i = j
      · subst i
        by_cases hkj : k = j
        · subst k
          exact ⟨y, by simp [a], by simp [a]⟩
        · have hkF : k ∈ F := (Finset.mem_insert.mp hk).resolve_left hkj
          obtain ⟨z, hxz, hzy⟩ := hp k hkF
          exact ⟨z, by simpa [a] using (R j).symm hzy,
            by simpa [a, hkj] using (R k).symm hxz⟩
      · have hiF : i ∈ F := (Finset.mem_insert.mp hi).resolve_left hij
        by_cases hkj : k = j
        · subst k
          simpa [a, hij] using hp i hiF
        · exact ⟨x, by simp [a, hij], by simp [a, hkj]⟩
    obtain ⟨z, hz⟩ := h (insert j F) (Finset.insert_nonempty j F) a ha
    refine ⟨z, ?_, ?_⟩
    · intro i hi
      have hij : i ≠ j := by intro hh; subst i; exact hj hi
      exact (R i).symm (by simpa [a, hij] using hz i (Finset.mem_insert_of_mem hi))
    · simpa [a] using hz j (by simp)
  · rintro ⟨z, hz, hzy⟩ i hi
    exact ⟨z, hz i hi, hzy⟩

/-- Exact, necessary and sufficient criterion; no global distributive-lattice
or congruence-permutability assumption is imposed. -/
theorem hasFiniteCRT_iff_crtGluing (R : I → Setoid X) :
    HasFiniteCRT R ↔ CRTGluing R :=
  ⟨crtGluing_of_hasFiniteCRT, hasFiniteCRT_of_crtGluing⟩

/-- Every actual solution is pairwise compatible. -/
theorem crtCompatible_of_solution {R : I → Setoid X} {F : Finset I}
    {a : I → X} {z : X} (hz : ∀ i ∈ F, R i z (a i)) :
    CRTCompatible R F a := by
  intro i hi j hj
  exact ⟨z, (R i).symm (hz i hi), hz j hj⟩

/-- Solutions differ precisely by the common kernel relation. -/
theorem solution_iff_common_relation {R : I → Setoid X} {F : Finset I}
    {a : I → X} {x y : X} (hx : ∀ i ∈ F, R i x (a i)) :
    (∀ i ∈ F, R i y (a i)) ↔ (∀ i ∈ F, R i y x) := by
  constructor
  · intro hy i hi
    exact (R i).trans (hy i hi) ((R i).symm (hx i hi))
  · intro hy i hi
    exact (R i).trans (hy i hi) (hx i hi)

/-- A common-kernel quotient for a finite family. -/
def crtKernel (R : I → Setoid X) (F : Finset I) : Setoid X where
  r x y := ∀ i ∈ F, R i x y
  iseqv := ⟨fun x i _hi => (R i).refl x,
    fun h i hi => (R i).symm (h i hi),
    fun h k i hi => (R i).trans (h i hi) (k i hi)⟩

end Setoid



namespace Setoid

variable {X I : Type*}

/-- Matching quotient data use the actual binary images. -/
def CRTMatching (R : I → Setoid X) :=
  {b : (i : I) → Quotient (R i) //
    ∀ i j, ∃ x : X, Quotient.mk (R i) x = b i ∧ Quotient.mk (R j) x = b j}

/-- The intersection equivalence relation for all indices. -/
def crtAllKernel (R : I → Setoid X) : Setoid X where
  r x y := ∀ i, R i x y
  iseqv := ⟨fun x i => (R i).refl x,
    fun h i => (R i).symm (h i),
    fun h k i => (R i).trans (h i) (k i)⟩

/-- Canonical reconstruction map modulo the common kernel. -/
def crtQuotientMap (R : I → Setoid X) : Quotient (crtAllKernel R) → CRTMatching R :=
  Quotient.lift
    (fun x => ⟨fun i => Quotient.mk (R i) x, fun i j => ⟨x, rfl, rfl⟩⟩)
    (by
      intro x y h
      apply Subtype.ext
      funext i
      exact Quotient.sound (h i))

theorem crtQuotientMap_injective (R : I → Setoid X) :
    Function.Injective (crtQuotientMap R) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      intro h
      apply Quotient.sound
      intro i
      exact Quotient.exact (congrArg (fun b : CRTMatching R => b.1 i) h)

theorem crtQuotientMap_surjective [Fintype I] [Nonempty I]
    {R : I → Setoid X} (h : HasFiniteCRT R) :
    Function.Surjective (crtQuotientMap R) := by
  classical
  intro b
  let a : I → X := fun i => Quotient.out (b.1 i)
  have ha : CRTCompatible R Finset.univ a := by
    intro i _ j _
    obtain ⟨z, hi, hj⟩ := b.2 i j
    refine ⟨z, ?_, ?_⟩
    · exact Quotient.exact ((Quotient.out_eq (b.1 i)).trans hi.symm)
    · exact Quotient.exact (hj.trans (Quotient.out_eq (b.1 j)).symm)
  obtain ⟨z, hz⟩ := h Finset.univ Finset.univ_nonempty a ha
  refine ⟨Quotient.mk _ z, ?_⟩
  apply Subtype.ext
  funext i
  exact (Quotient.sound (hz i (Finset.mem_univ i))).trans (Quotient.out_eq (b.1 i))

/-- The finite matching object is exactly the common-kernel quotient. -/
noncomputable def crtQuotientEquiv [Fintype I] [Nonempty I]
    {R : I → Setoid X} (h : CRTGluing R) :
    Quotient (crtAllKernel R) ≃ CRTMatching R :=
  Equiv.ofBijective (crtQuotientMap R)
    ⟨crtQuotientMap_injective R,
      crtQuotientMap_surjective (hasFiniteCRT_of_crtGluing h)⟩

/-- A trivial common kernel upgrades reconstruction to uniqueness in the source. -/
theorem existsUnique_solution [Fintype I] [Nonempty I]
    {R : I → Setoid X} (h : CRTGluing R)
    (hsep : ∀ x y, (∀ i, R i x y) → x = y)
    (a : I → X) (ha : CRTCompatible R Finset.univ a) :
    ∃! x, ∀ i, R i x (a i) := by
  obtain ⟨x, hx⟩ := hasFiniteCRT_of_crtGluing h Finset.univ Finset.univ_nonempty a ha
  refine ⟨x, fun i => hx i (Finset.mem_univ i), ?_⟩
  intro y hy
  apply hsep y x
  intro i
  exact (R i).trans (hy i) ((R i).symm (hx i (Finset.mem_univ i)))

end Setoid

namespace Setoid

variable {X I : Type*}

/-- Permutation is an equality of actual composites. -/
def CRTPermutes (R S : Setoid X) : Prop :=
  ∀ x y, crtComp R S x y ↔ crtComp S R x y

/-- Permuting equivalence relations have an equivalence relation as composite. -/
def crtCompositeSetoid (R S : Setoid X) (h : CRTPermutes R S) : Setoid X where
  r := crtComp R S
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact ⟨x, R.refl x, S.refl x⟩
    · intro x y hxy
      obtain ⟨z, hxz, hzy⟩ := hxy
      exact (h y x).mpr ⟨z, S.symm hzy, R.symm hxz⟩
    · intro x y z hxy hyz
      obtain ⟨a, hxa, hay⟩ := hxy
      obtain ⟨b, hyb, hbz⟩ := hyz
      obtain ⟨c, hac, hcb⟩ := (h a b).mpr ⟨y, hay, hyb⟩
      exact ⟨c, R.trans hxa hac, S.trans hcb hbz⟩

theorem crtCompositeSetoid_eq_sup (R S : Setoid X) (h : CRTPermutes R S) :
    crtCompositeSetoid R S h = R ⊔ S := by
  apply le_antisymm
  · intro x y hxy
    obtain ⟨z, hxz, hzy⟩ := hxy
    exact (R ⊔ S).trans ((show R ≤ R ⊔ S from le_sup_left) hxz)
      ((show S ≤ R ⊔ S from le_sup_right) hzy)
  · apply sup_le
    · intro x y hxy
      exact ⟨y, hxy, S.refl y⟩
    · intro x y hxy
      exact ⟨x, R.refl x, hxy⟩

/-- The familiar join-compatibility formulation is valid under permutation. -/
theorem crtComp_iff_sup (R S : Setoid X) (h : CRTPermutes R S) (x y : X) :
    crtComp R S x y ↔ (R ⊔ S) x y := by
  change (crtCompositeSetoid R S h) x y ↔ (R ⊔ S) x y
  rw [crtCompositeSetoid_eq_sup]

/-- Only the indicated distributivity identities and permutations are needed;
no ambient arithmetical-category assumption is required. -/
theorem crtGluing_of_distributive_permutable (R : I → Setoid X)
    (hp : ∀ i j, CRTPermutes (R i) (R j))
    (hm : ∀ (F : Finset I), F.Nonempty → ∀ j, j ∉ F →
      CRTPermutes (crtKernel R F) (R j))
    (hd : ∀ (F : Finset I), F.Nonempty → ∀ j, j ∉ F →
      crtKernel R F ⊔ R j = crtKernel (fun i => R i ⊔ R j) F) :
    CRTGluing R := by
  intro F hF j hj x y
  have hmeet := crtComp_iff_sup (crtKernel R F) (R j) (hm F hF j hj) x y
  rw [hd F hF j hj] at hmeet
  constructor
  · intro hh
    apply hmeet.mpr
    intro i hi
    exact (crtComp_iff_sup (R i) (R j) (hp i j) x y).mp (hh i hi)
  · intro hh i hi
    exact (crtComp_iff_sup (R i) (R j) (hp i j) x y).mpr (hmeet.mp hh i hi)

end Setoid

namespace Setoid

variable {X I : Type*}

/-- Reduction of the first residue to the overlap quotient. -/
def crtOverlapLeft (R S : Setoid X) : Quotient R → Quotient (R ⊔ S) :=
  Quotient.lift (fun x => Quotient.mk (R ⊔ S) x)
    (fun _ _ h => Quotient.sound ((show R ≤ R ⊔ S from le_sup_left) h))

/-- Reduction of the second residue to the overlap quotient. -/
def crtOverlapRight (R S : Setoid X) : Quotient S → Quotient (R ⊔ S) :=
  Quotient.lift (fun x => Quotient.mk (R ⊔ S) x)
    (fun _ _ h => Quotient.sound ((show S ≤ R ⊔ S from le_sup_right) h))

/-- Under permutation, agreement in the overlap is actual binary solvability. -/
theorem crt_overlap_eq_iff_pair (R S : Setoid X) (hp : CRTPermutes R S)
    (a : Quotient R) (b : Quotient S) :
    crtOverlapLeft R S a = crtOverlapRight R S b ↔
      ∃ z : X, Quotient.mk R z = a ∧ Quotient.mk S z = b := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      constructor
      · intro h
        have hs : (R ⊔ S) a b := Quotient.exact h
        obtain ⟨z, haz, hzb⟩ := (crtComp_iff_sup R S hp a b).mpr hs
        exact ⟨z, Quotient.sound (R.symm haz), Quotient.sound hzb⟩
      · rintro ⟨z, hza, hzb⟩
        have hR : R a z := R.symm (Quotient.exact hza)
        have hS : S z b := Quotient.exact hzb
        exact Quotient.sound ((crtComp_iff_sup R S hp a b).mp ⟨z, hR, hS⟩)

/-- Equalizer of the two overlap-reduction families. -/
def CRTOverlapMatching (R : I → Setoid X) :=
  {b : (i : I) → Quotient (R i) //
    ∀ i j, crtOverlapLeft (R i) (R j) (b i) = crtOverlapRight (R i) (R j) (b j)}

/-- Binary-image matching and overlap matching agree for permuting relations. -/
def crtMatchingEquivOverlap (R : I → Setoid X) (hp : ∀ i j, CRTPermutes (R i) (R j)) :
    CRTMatching R ≃ CRTOverlapMatching R where
  toFun b := ⟨b.1, fun i j => (crt_overlap_eq_iff_pair (R i) (R j) (hp i j) _ _).mpr (b.2 i j)⟩
  invFun b := ⟨b.1, fun i j => (crt_overlap_eq_iff_pair (R i) (R j) (hp i j) _ _).mp (b.2 i j)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Quotient/equalizer CRT with explicit actual-gluing and permutation assumptions. -/
noncomputable def crtQuotientOverlapEquiv [Fintype I] [Nonempty I]
    {R : I → Setoid X} (h : CRTGluing R) (hp : ∀ i j, CRTPermutes (R i) (R j)) :
    Quotient (crtAllKernel R) ≃ CRTOverlapMatching R :=
  (crtQuotientEquiv h).trans (crtMatchingEquivOverlap R hp)

end Setoid

namespace Setoid

variable {X I : Type*}

/-- For a prescribed order, only the current prefix's gluing identity is
needed to adjoin its next constraint. -/
theorem crt_extend_solution [DecidableEq I] {R : I → Setoid X} {F : Finset I} {j : I}
    (step : ∀ x y, (∀ i ∈ F, crtComp (R i) (R j) x y) →
      ∃ z, (∀ i ∈ F, R i x z) ∧ R j z y)
    {a : I → X} {x : X} (hx : ∀ i ∈ F, R i x (a i))
    (ha : ∀ i ∈ F, crtComp (R i) (R j) (a i) (a j)) :
    ∃ z, ∀ i ∈ insert j F, R i z (a i) := by
  classical
  have hp : ∀ i ∈ F, crtComp (R i) (R j) x (a j) := by
    intro i hi
    obtain ⟨z, hzi, hzj⟩ := ha i hi
    exact ⟨z, (R i).trans (hx i hi) hzi, hzj⟩
  obtain ⟨z, hz, hzj⟩ := step x (a j) hp
  refine ⟨z, ?_⟩
  intro i hi
  rcases Finset.mem_insert.mp hi with hij | hi
  · subst i
    exact hzj
  · exact (R i).trans ((R i).symm (hz i hi)) (hx i hi)

end Setoid
