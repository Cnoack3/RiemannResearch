/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
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

end RiemannResearch.GroupTheory
