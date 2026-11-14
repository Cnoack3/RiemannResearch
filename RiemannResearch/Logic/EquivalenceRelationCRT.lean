import Mathlib.Data.Finset.Basic
import Mathlib.Data.Setoid.Basic

/-!
# Exact finite gluing for a specified family of equivalence relations

Source: user-provided Categorical_CRT_Exact_Gluing_and_Energy_2026-11-14.md,
Theorems A and B. The note supplies the family-local relation criterion and
its induction proof. This module proves the set-based version, not the
regular-category internal-relations theorem. Ambient distributivity and
permutability are not assumed.

The RH consumer is finite arithmetic reconstruction: compatibility must be
established before applying compact or Hilbert-energy gluing. Background:
M. Hoefnagel, Characterizations of majority categories (2019),
https://arxiv.org/abs/1902.06920, Sections 4--5 (categorical terminology).
-/

namespace RiemannResearch.Logic.FamilyCRT
variable {ι X : Type*}

/-- Every pair of residue constraints has a common representative. -/
def PairwiseCompatible (R : ι → Setoid X) (F : Finset ι) (a : ι → X) : Prop :=
  ∀ i ∈ F, ∀ j ∈ F, ∃ z, (R i).r z (a i) ∧ (R j).r z (a j)

/-- CRT for every nonempty finite subfamily. -/
def HereditaryCRT (R : ι → Setoid X) : Prop :=
  ∀ F : Finset ι, F.Nonempty → ∀ a : ι → X,
    PairwiseCompatible R F a → ∃ z, ∀ i ∈ F, (R i).r z (a i)

/-- The nontrivial inclusion in finite-meet distribution over relational composition. -/
def MeetComposition (R : ι → Setoid X) : Prop :=
  ∀ F : Finset ι, F.Nonempty → ∀ j, j ∉ F → ∀ x y : X,
    (∀ i ∈ F, ∃ z, (R i).r x z ∧ (R j).r z y) →
    ∃ z, (∀ i ∈ F, (R i).r x z) ∧ (R j).r z y

theorem hereditaryCRT_of_meetComposition (R : ι → Setoid X)
    (h : MeetComposition R) : HereditaryCRT R := by
  classical
  intro F
  induction F using Finset.induction_on with
  | empty => simp
  | @insert j F hj ih =>
    intro _ a ha
    by_cases hF : F.Nonempty
    · obtain ⟨x, hx⟩ := ih hF a (fun i hi k hk =>
        ha i (Finset.mem_insert_of_mem hi) k (Finset.mem_insert_of_mem hk))
      obtain ⟨z, hxz, hzj⟩ := h F hF j hj x (a j) (by
        intro i hi
        obtain ⟨t, hti, htj⟩ :=
          ha i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_self _ _)
        exact ⟨t, (R i).iseqv.trans (hx i hi) ((R i).iseqv.symm hti), htj⟩)
      refine ⟨z, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hzj
      · exact (R i).iseqv.trans ((R i).iseqv.symm (hxz i hi)) (hx i hi)
    · have hFe : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
      subst F
      refine ⟨a j, ?_⟩
      intro i hi
      have : i = j := by simpa using hi
      subst i
      exact (R j).iseqv.refl _

theorem meetComposition_of_hereditaryCRT (R : ι → Setoid X)
    (h : HereditaryCRT R) : MeetComposition R := by
  classical
  intro F hF j hj x y hxy
  let a : ι → X := fun i => if i = j then y else x
  have hai (i : ι) (hi : i ∈ F) : a i = x := by
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    simp [a, hij]
  have haj : a j = y := by simp [a]
  have hc : PairwiseCompatible R (insert j F) a := by
    intro i hi k hk
    by_cases hij : i = j
    · subst i
      by_cases hkj : k = j
      · subst k
        exact ⟨y, by simpa only [haj] using (R j).iseqv.refl y,
          by simpa only [haj] using (R j).iseqv.refl y⟩
      · have hkF := (Finset.mem_insert.mp hk).resolve_left hkj
        obtain ⟨z, hxz, hzy⟩ := hxy k hkF
        exact ⟨z, by simpa only [haj] using hzy,
          by simpa only [hai k hkF] using (R k).iseqv.symm hxz⟩
    · have hiF := (Finset.mem_insert.mp hi).resolve_left hij
      by_cases hkj : k = j
      · subst k
        obtain ⟨z, hxz, hzy⟩ := hxy i hiF
        exact ⟨z, by simpa only [hai i hiF] using (R i).iseqv.symm hxz,
          by simpa only [haj] using hzy⟩
      · have hkF := (Finset.mem_insert.mp hk).resolve_left hkj
        exact ⟨x, by simpa only [hai i hiF] using (R i).iseqv.refl x,
          by simpa only [hai k hkF] using (R k).iseqv.refl x⟩
  obtain ⟨z, hz⟩ := h (insert j F) (Finset.insert_nonempty _ _) a hc
  refine ⟨z, ?_, ?_⟩
  · intro i hi
    have hh := hz i (Finset.mem_insert_of_mem hi)
    rw [hai i hi] at hh
    exact (R i).iseqv.symm hh
  · simpa only [haj] using hz j (Finset.mem_insert_self _ _)

/-- The exact family-local CRT criterion, for equivalence relations on a type. -/
theorem hereditaryCRT_iff_meetComposition (R : ι → Setoid X) :
    HereditaryCRT R ↔ MeetComposition R :=
  ⟨meetComposition_of_hereditaryCRT R, hereditaryCRT_of_meetComposition R⟩

theorem meet_composition_iff (R : ι → Setoid X) (h : MeetComposition R)
    (F : Finset ι) (hF : F.Nonempty) (j : ι) (hj : j ∉ F) (x y : X) :
    (∃ z, (∀ i ∈ F, (R i).r x z) ∧ (R j).r z y) ↔
      (∀ i ∈ F, ∃ z, (R i).r x z ∧ (R j).r z y) := by
  constructor
  · rintro ⟨z, hz, hzy⟩ i hi
    exact ⟨z, hz i hi, hzy⟩
  · exact h F hF j hj x y

/-- Every solution class is exactly one class of the intersection relation. -/
theorem solution_iff_intersection (R : ι → Setoid X) (F : Finset ι)
    (a : ι → X) {x : X} (hx : ∀ i ∈ F, (R i).r x (a i)) (y : X) :
    (∀ i ∈ F, (R i).r y (a i)) ↔ (∀ i ∈ F, (R i).r y x) := by
  exact ⟨fun hy i hi => (R i).iseqv.trans (hy i hi) ((R i).iseqv.symm (hx i hi)),
    fun hy i hi => (R i).iseqv.trans (hy i hi) (hx i hi)⟩

/-- The kernel family of actual quotient/observation maps. -/
def kernelFamily {Y : ι → Type*} (q : ∀ i, X → Y i) : ι → Setoid X :=
  fun i => Setoid.ker (q i)

/-- The matching-object surjectivity assertion in sets, with actual binary images. -/
theorem exists_joint_of_pairwise {Y : ι → Type*} (q : ∀ i, X → Y i)
    (hq : ∀ i, Function.Surjective (q i)) (h : HereditaryCRT (kernelFamily q))
    (F : Finset ι) (hF : F.Nonempty) (b : ∀ i, Y i)
    (hb : ∀ i ∈ F, ∀ j ∈ F, ∃ z, q i z = b i ∧ q j z = b j) :
    ∃ z, ∀ i ∈ F, q i z = b i := by
  classical
  choose a ha using fun i => hq i (b i)
  have hc : PairwiseCompatible (kernelFamily q) F a := by
    intro i hi j hj
    obtain ⟨z, hzi, hzj⟩ := hb i hi j hj
    exact ⟨z, hzi.trans (ha i).symm, hzj.trans (ha j).symm⟩
  obtain ⟨z, hz⟩ := h F hF a hc
  exact ⟨z, fun i hi => (hz i hi).trans (ha i)⟩

end RiemannResearch.Logic.FamilyCRT
