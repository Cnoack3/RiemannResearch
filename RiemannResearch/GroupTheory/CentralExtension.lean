/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.GroupTheory.IsPerfect

/-!
# Perfect central extensions do not split

A section of a group homomorphism with central kernel identifies the source
with the direct product of the kernel and the target. A perfect group cannot
have a nontrivial commutative direct factor. Consequently, a perfect central
extension with nontrivial kernel admits no group-homomorphic section.
-/

namespace RiemannResearch.GroupTheory

/-- A perfect group admits no homomorphism with nontrivial image in a
commutative group. -/
theorem not_isPerfect_of_nontrivial_hom_to_commutative
    {E A : Type*} [Group E] [CommGroup A]
    (f : E →* A) {x : E} (hx : f x ≠ 1) :
    ¬ Group.IsPerfect E := by
  intro hperfect
  have hcomm : ⁅f.range, f.range⁆ = (⊥ : Subgroup A) := by
    apply le_antisymm
    · exact (Subgroup.commutator_mono le_top le_top).trans_eq
        (commutator_eq_bot A)
    · exact bot_le
  have hrange : f.range = (⊥ : Subgroup A) := by
    calc
      f.range = Subgroup.map f ⊤ := MonoidHom.range_eq_map f
      _ = Subgroup.map f (commutator E) := by
        rw [hperfect.commutator_eq_top]
      _ = ⁅Subgroup.map f ⊤, Subgroup.map f ⊤⁆ := by
        change Subgroup.map f ⁅(⊤ : Subgroup E), ⊤⁆ =
          ⁅Subgroup.map f ⊤, Subgroup.map f ⊤⁆
        exact Subgroup.map_commutator _ _ _
      _ = ⁅f.range, f.range⁆ := by
        rw [MonoidHom.range_eq_map]
      _ = ⊥ := hcomm
  apply hx
  apply Subgroup.mem_bot.mp
  rw [← hrange]
  exact ⟨x, rfl⟩

/-- A group is not perfect if it has a direct factor that is both nontrivial
and commutative. -/
theorem not_isPerfect_of_mulEquiv_prod_nontrivial_commutative
    {E A P : Type*} [Group E] [CommGroup A] [Nontrivial A] [Group P]
    (e : E ≃* A × P) :
    ¬ Group.IsPerfect E := by
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  let f : E →* A := (MonoidHom.fst A P).comp e.toMonoidHom
  apply not_isPerfect_of_nontrivial_hom_to_commutative
    f (x := e.symm (a, 1))
  simpa [f] using ha

/-- A section of a homomorphism with central kernel gives the usual direct
product description of the source. -/
noncomputable def centralSplitMulEquiv
    {E P : Type*} [Group E] [Group P]
    (π : E →* P) (s : P →* E)
    (hs : Function.RightInverse s π)
    (hcentral : π.ker ≤ Subgroup.center E) :
    π.ker × P ≃* E := by
  let f : π.ker × P →* E :=
    { toFun := fun x => (x.1 : E) * s x.2
      map_one' := by simp
      map_mul' := by
        intro x y
        have hc : s x.2 * (y.1 : E) = (y.1 : E) * s x.2 :=
          Subgroup.mem_center_iff.mp (hcentral y.1.2) (s x.2)
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul]
        calc
          ((x.1 : E) * (y.1 : E)) * (s x.2 * s y.2) =
              (x.1 : E) * ((y.1 : E) * s x.2) * s y.2 := by
                simp [mul_assoc]
          _ = (x.1 : E) * (s x.2 * (y.1 : E)) * s y.2 := by
                rw [hc]
          _ = ((x.1 : E) * s x.2) * ((y.1 : E) * s y.2) := by
                simp [mul_assoc] }
  apply MulEquiv.ofBijective f
  constructor
  · intro x y hxy
    change (x.1 : E) * s x.2 = (y.1 : E) * s y.2 at hxy
    have hp : x.2 = y.2 := by
      have hmap := congrArg π hxy
      rw [map_mul, map_mul, MonoidHom.mem_ker.mp x.1.2,
        MonoidHom.mem_ker.mp y.1.2, one_mul, one_mul,
        hs x.2, hs y.2] at hmap
      exact hmap
    apply Prod.ext
    · apply Subtype.ext
      rw [hp] at hxy
      exact mul_right_cancel hxy
    · exact hp
  · intro e
    refine ⟨(⟨e * (s (π e))⁻¹, ?_⟩, π e), ?_⟩
    · apply MonoidHom.mem_ker.mpr
      rw [map_mul, map_inv, hs (π e), mul_inv_cancel]
    · simp [f]

/-- A perfect group cannot be a split central extension with nontrivial
kernel. Thus a derived-subgroup certificate proving the total lift perfect is
also a nonsplitting certificate. -/
theorem no_section_of_isPerfect_of_nontrivial_central_ker
    {E P : Type*} [Group E] [Group P] [Group.IsPerfect E]
    (π : E →* P) [Nontrivial π.ker]
    (hcentral : π.ker ≤ Subgroup.center E)
    (s : P →* E) :
    ¬ Function.RightInverse s π := by
  intro hs
  let commKer : CommGroup π.ker :=
    { (inferInstance : Group π.ker) with
      mul_comm := by
        intro x y
        apply Subtype.ext
        exact (Subgroup.mem_center_iff.mp (hcentral x.2) (y : E)).symm }
  exact @not_isPerfect_of_mulEquiv_prod_nontrivial_commutative
    E π.ker P inferInstance commKer inferInstance inferInstance
    (centralSplitMulEquiv π s hs hcentral).symm inferInstance

end RiemannResearch.GroupTheory
