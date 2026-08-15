/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Abel

/-!
# A two-subgroup Chinese remainder theorem

For additive subgroups (H,K \le A), this module constructs
`A → A ⧸ H × A ⧸ K → A ⧸ (H ⊔ K)` and proves the expected
kernel, exactness, and surjectivity statements.

Source: user-provided argument. The formulation is the standard generalized
Chinese remainder theorem for two subgroups of an abelian group.
-/

namespace RiemannResearch.GroupTheory.AddSubgroupCRT

variable {A : Type*} [AddCommGroup A]

/-- The simultaneous quotient, or modular, map. -/
def diagonal (H K : AddSubgroup A) :
    A →+ (A ⧸ H) × (A ⧸ K) :=
  (QuotientAddGroup.mk' H).prod (QuotientAddGroup.mk' K)

/-- The map from the first quotient to the common overlap quotient. -/
def leftToSup (H K : AddSubgroup A) :
    A ⧸ H →+ A ⧸ (H ⊔ K) :=
  QuotientAddGroup.map H (H ⊔ K) (AddMonoidHom.id A) (by
    intro x hx
    exact (le_sup_left : H ≤ H ⊔ K) hx)

/-- The map from the second quotient to the common overlap quotient. -/
def rightToSup (H K : AddSubgroup A) :
    A ⧸ K →+ A ⧸ (H ⊔ K) :=
  QuotientAddGroup.map K (H ⊔ K) (AddMonoidHom.id A) (by
    intro x hx
    exact (le_sup_right : K ≤ H ⊔ K) hx)

/-- The overlap-difference map `([x], [y]) ↦ [x - y]`. -/
def difference (H K : AddSubgroup A) :
    (A ⧸ H) × (A ⧸ K) →+ A ⧸ (H ⊔ K) :=
  (leftToSup H K).comp (AddMonoidHom.fst _ _) -
    (rightToSup H K).comp (AddMonoidHom.snd _ _)

@[simp] theorem diagonal_apply (H K : AddSubgroup A) (x : A) :
    diagonal H K x =
      (QuotientAddGroup.mk x, QuotientAddGroup.mk x) := by
  rfl

@[simp] theorem leftToSup_mk (H K : AddSubgroup A) (x : A) :
    leftToSup H K (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk x := by
  rfl

@[simp] theorem rightToSup_mk (H K : AddSubgroup A) (x : A) :
    rightToSup H K (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk x := by
  rfl

@[simp] theorem difference_mk_mk
    (H K : AddSubgroup A) (x y : A) :
    difference H K
        (QuotientAddGroup.mk x, QuotientAddGroup.mk y) =
      QuotientAddGroup.mk (x - y) := by
  rfl

/-- A residue pair is in the image of the diagonal map exactly when its
overlap difference vanishes. This is exactness at the middle term. -/
theorem exists_diagonal_eq_iff
    (H K : AddSubgroup A)
    (z : (A ⧸ H) × (A ⧸ K)) :
    (∃ t, diagonal H K t = z) ↔ difference H K z = 0 := by
  rcases z with ⟨u, v⟩
  refine QuotientAddGroup.induction_on u ?_
  intro x
  refine QuotientAddGroup.induction_on v ?_
  intro y
  constructor
  · rintro ⟨t, ht⟩
    have htH : t - x ∈ H := by
      rw [← QuotientAddGroup.eq_iff_sub_mem]
      exact congrArg Prod.fst ht
    have htK : t - y ∈ K := by
      rw [← QuotientAddGroup.eq_iff_sub_mem]
      exact congrArg Prod.snd ht
    rw [difference_mk_mk, QuotientAddGroup.eq_zero_iff]
    have hxy : x - y = -(t - x) + (t - y) := by
      abel
    rw [hxy]
    exact AddSubgroup.add_mem_sup (H.neg_mem htH) htK
  · intro hxy
    rw [difference_mk_mk, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_sup] at hxy
    rcases hxy with ⟨h, hh, k, hk, hhk⟩
    refine ⟨x - h, ?_⟩
    apply Prod.ext
    · change
        (QuotientAddGroup.mk (x - h) : A ⧸ H) =
          QuotientAddGroup.mk x
      rw [QuotientAddGroup.eq_iff_sub_mem]
      have : (x - h) - x = -h := by
        abel
      rw [this]
      exact H.neg_mem hh
    · change
        (QuotientAddGroup.mk (x - h) : A ⧸ K) =
          QuotientAddGroup.mk y
      rw [QuotientAddGroup.eq_iff_sub_mem]
      have heq : (x - h) - y = k := by
        calc
          (x - h) - y = (x - y) - h := by abel
          _ = (h + k) - h := by rw [hhk]
          _ = k := by abel
      rw [heq]
      exact hk

/-- The kernel of the simultaneous quotient map is the intersection. -/
theorem diagonal_ker (H K : AddSubgroup A) :
    (diagonal H K).ker = H ⊓ K := by
  ext x
  simp [diagonal, QuotientAddGroup.eq_zero_iff]

/-- The simultaneous quotient map is injective exactly when the two
subgroups have trivial intersection. -/
theorem diagonal_injective_iff (H K : AddSubgroup A) :
    Function.Injective (diagonal H K) ↔ H ⊓ K = ⊥ := by
  constructor
  · intro hinj
    calc
      H ⊓ K = (diagonal H K).ker :=
        (diagonal_ker H K).symm
      _ = ⊥ :=
        (AddMonoidHom.ker_eq_bot_iff _).2 hinj
  · intro h
    apply (AddMonoidHom.ker_eq_bot_iff _).1
    rw [diagonal_ker, h]

/-- Every overlap class is a difference of two residue classes. -/
theorem difference_surjective (H K : AddSubgroup A) :
    Function.Surjective (difference H K) := by
  intro z
  refine QuotientAddGroup.induction_on z ?_
  intro x
  refine ⟨(QuotientAddGroup.mk x, QuotientAddGroup.mk 0), ?_⟩
  simpa using difference_mk_mk H K x 0

end RiemannResearch.GroupTheory.AddSubgroupCRT
