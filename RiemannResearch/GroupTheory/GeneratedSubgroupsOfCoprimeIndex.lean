/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.FrobeniusNumber

/-!
# Generation from coprime subgroup indices

A family of subgroups whose indices have gcd one generates the whole group.
This is the finite-index argument used in the generating-gauge-cover step of
the E8 Serre II program. The proof works for arbitrary groups because Mathlib's
subgroup index is cardinal-valued in the finite case and zero otherwise.
-/

namespace RiemannResearch.GroupTheory

/-- If the gcd of the indices of a family of subgroups is one, their supremum
is the whole group. -/
theorem iSup_eq_top_of_setGcd_indices
    {G I : Type*} [Group G] (H : I → Subgroup G)
    (hgcd : Nat.setGcd (Set.range fun i => (H i).index) = 1) :
    iSup H = ⊤ := by
  apply Subgroup.index_eq_one.mp
  apply Nat.dvd_one.mp
  rw [← hgcd, Nat.dvd_setGcd_iff]
  intro n hn
  obtain ⟨i, rfl⟩ := hn
  have hle : H i ≤ iSup H := le_iSup H i
  refine ⟨(H i).relIndex (iSup H), ?_⟩
  simpa [Nat.mul_comm] using (Subgroup.relIndex_mul_index hle).symm

/-- Under a surjective group homomorphism, the full inverse images of a
nonempty generating family again generate the whole source group. The
nonempty hypothesis ensures that the common kernel lies in the generated
inverse images. -/
theorem iSup_comap_eq_top_of_surjective
    {G Q I : Type*} [Group G] [Group Q] [Nonempty I]
    (f : G →* Q) (hf : Function.Surjective f)
    (H : I → Subgroup Q) (hgen : iSup H = ⊤) :
    iSup (fun i => (H i).comap f) = ⊤ := by
  let K : Subgroup G := iSup (fun i => (H i).comap f)
  have hker : f.ker ≤ K := by
    intro x hx
    let i : I := Classical.choice inferInstance
    apply le_iSup (fun i => (H i).comap f) i
    change f x ∈ H i
    rw [show f x = 1 by exact hx]
    exact (H i).one_mem
  have hmap : K.map f = ⊤ := by
    change (iSup (fun i => (H i).comap f)).map f = ⊤
    rw [Subgroup.map_iSup]
    simpa only [Subgroup.map_comap_eq_self_of_surjective hf] using hgen
  have hcomap : (K.map f).comap f = K :=
    Subgroup.comap_map_eq_self hker
  rw [hmap, Subgroup.comap_top] at hcomap
  exact hcomap.symm

end RiemannResearch.GroupTheory
