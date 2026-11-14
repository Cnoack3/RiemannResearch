import RiemannResearch.CategoryTheory.LocalFamilyCRT
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Functorial transport of internal CRT witnesses

Source: user-provided argument, categorical CRT functoriality (14 November 2026).
A pullback-preserving functor transports an actual internal equivalence diagram
to a generalized-point equivalence relation. If it also preserves regular
 epimorphisms, it transports all binary compatibility and finite solution
witnesses. The theorem is explicit about those structural preservation data.
-/

open CategoryTheory CategoryTheory.Limits

universe u v u' v' w

namespace CategoryTheory.InternalEquivalencePresentation

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {D : Type u'} [Category.{v'} D] [HasPullbacks D] {X : C}

/-- The generalized-point relation of the transported internal diagram. Only
the pullback defining transitivity must be preserved for this construction. -/
noncomputable def mapRelation (F : C ⥤ D) (R : InternalEquivalencePresentation X)
    [PreservesLimit (cospan R.right R.left) F] : GeneralizedEquivalence (F.obj X) where
  rel T :=
    { r := fun a b => ∃ z : T ⟶ F.obj R.object,
        z ≫ F.map R.left = a ∧ z ≫ F.map R.right = b
      iseqv := by
        refine ⟨?_, ?_, ?_⟩
        · intro a
          refine ⟨a ≫ F.map R.diagonal, ?_, ?_⟩
          · rw [Category.assoc, ← F.map_comp, R.diagonal_left, F.map_id, Category.comp_id]
          · rw [Category.assoc, ← F.map_comp, R.diagonal_right, F.map_id, Category.comp_id]
        · rintro a b ⟨z, hzl, hzr⟩
          refine ⟨z ≫ F.map R.swap, ?_, ?_⟩
          · rw [Category.assoc, ← F.map_comp, R.swap_left]
            exact hzr
          · rw [Category.assoc, ← F.map_comp, R.swap_right]
            exact hzl
        · rintro a b c ⟨z, hzl, hzr⟩ ⟨w, hwl, hwr⟩
          let t := pullback.lift z w (hzr.trans hwl.symm) ≫
            (PreservesPullback.iso F R.right R.left).inv
          refine ⟨t ≫ F.map R.trans, ?_, ?_⟩
          · calc
              (t ≫ F.map R.trans) ≫ F.map R.left = t ≫ F.map (R.trans ≫ R.left) := by
                rw [F.map_comp, Category.assoc]
              _ = t ≫ (F.map (pullback.fst R.right R.left) ≫ F.map R.left) := by
                rw [R.trans_left, F.map_comp]
              _ = z ≫ F.map R.left := by
                dsimp [t]
                rw [Category.assoc, PreservesPullback.iso_inv_fst_assoc,
                  ← Category.assoc, pullback.lift_fst]
              _ = a := hzl
          · calc
              (t ≫ F.map R.trans) ≫ F.map R.right = t ≫ F.map (R.trans ≫ R.right) := by
                rw [F.map_comp, Category.assoc]
              _ = t ≫ (F.map (pullback.snd R.right R.left) ≫ F.map R.right) := by
                rw [R.trans_right, F.map_comp]
              _ = w ≫ F.map R.right := by
                dsimp [t]
                rw [Category.assoc, PreservesPullback.iso_inv_snd_assoc,
                  ← Category.assoc, pullback.lift_snd]
              _ = c := hwr }
  precomp := by
    intro T U p a b h
    obtain ⟨z, hzl, hzr⟩ := h
    exact ⟨p ≫ z, by simpa only [Category.assoc] using congrArg (fun k => p ≫ k) hzl,
      by simpa only [Category.assoc] using congrArg (fun k => p ≫ k) hzr⟩

/-- Membership in the internal relation transports directly, with its witness. -/
theorem holds_map (F : C ⥤ D) (R : InternalEquivalencePresentation X)
    [PreservesLimit (cospan R.right R.left) F]
    {T : C} {a b : T ⟶ X} (h : R.Holds a b) :
    (R.mapRelation F).rel (F.obj T) (F.map a) (F.map b) := by
  obtain ⟨z, hzl, hzr⟩ := h
  refine ⟨F.map z, ?_, ?_⟩
  · rw [← F.map_comp, hzl]
  · rw [← F.map_comp, hzr]

/-- Regular functors preserve the supplied CRT solution, with no additional
relation-preservation assumption beyond the mapped internal diagrams. -/
theorem localSolution_map_internal (F : C ⥤ D)
    (hcover : ∀ {U T : C} (p : U ⟶ T), IsRegularEpi p → IsRegularEpi (F.map p))
    {I : Type w} (R : I → InternalEquivalencePresentation X)
    [∀ i, PreservesLimit (cospan (R i).right (R i).left) F]
    {J : Finset I} {T : C} {a : I → (T ⟶ X)}
    (h : GeneralizedEquivalence.LocalSolution (fun i => (R i).toGeneralized) J a) :
    GeneralizedEquivalence.LocalSolution (fun i => (R i).mapRelation F) J
      (fun i => F.map (a i)) :=
  GeneralizedEquivalence.localSolution_map F hcover
    (fun i _ _ _ h => holds_map F (R i) h) h

/-- Binary compatibility transports through the same regular functor. -/
theorem localComp_map_internal (F : C ⥤ D)
    (hcover : ∀ {U T : C} (p : U ⟶ T), IsRegularEpi p → IsRegularEpi (F.map p))
    (R S : InternalEquivalencePresentation X)
    [PreservesLimit (cospan R.right R.left) F]
    [PreservesLimit (cospan S.right S.left) F]
    {T : C} {a b : T ⟶ X}
    (h : GeneralizedEquivalence.LocalComp R.toGeneralized S.toGeneralized a b) :
    GeneralizedEquivalence.LocalComp (R.mapRelation F) (S.mapRelation F)
      (F.map a) (F.map b) :=
  GeneralizedEquivalence.localComp_map F hcover
    (fun _ _ _ h => holds_map F R h) (fun _ _ _ h => holds_map F S h) h

end CategoryTheory.InternalEquivalencePresentation
