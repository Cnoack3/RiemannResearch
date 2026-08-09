/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Transporting index-multiplication identities across isomorphisms
-/

open CategoryTheory

universe u v

namespace RiemannResearch.CategoryTheory

/-- Conjugating a pair of morphisms by source and target isomorphisms preserves
a composition identity given by multiplication by a natural number. -/
theorem isoConjugate_comp_eq_nsmul_id
    {C : Type u} [Category.{v} C] [Preadditive C]
    {X X' Y Y' : C} (iX : X ≅ X') (iY : Y ≅ Y')
    (r : X' ⟶ Y') (c : Y' ⟶ X') (n : ℕ)
    (h : r ≫ c = n • 𝟙 X') :
    (iX.hom ≫ r ≫ iY.inv) ≫
      (iY.hom ≫ c ≫ iX.inv) = n • 𝟙 X := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc r c iX.inv, h]
  rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul]
  simp

end RiemannResearch.CategoryTheory
