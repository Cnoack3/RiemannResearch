/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.E8.ConcreteRootSystem

/-!
# Classification of the concrete E₈ root vectors

The doubled-coordinate E₈ roots have exactly two possible shapes: two nonzero
coordinates equal to `±2`, or eight coordinates equal to `±1` with even
minus parity.  This module proves both directions of that classification and
constructs the corresponding root parameter structurally.  The decoder avoids
an exhaustive search through all 240 roots and is used by the incidence and
reflection-closure developments.

Source for the two standard coordinate shapes: N. Bourbaki,
*Lie Groups and Lie Algebras*, Chapters 4--6, Planche VII.  The equivalence
with the repository's parameter types is proved directly below.
-/

namespace RiemannResearch
namespace E8
namespace ConcreteRootSystem

set_option maxRecDepth 100000

/-- Indices of the nonzero coordinates of an integer-shaped vector. -/
def integerSupport (v : Vector) : Finset (Fin 8) :=
  Finset.univ.filter fun i => v i ≠ 0

/-- Boolean signs recovered from a half-shaped vector. -/
def halfSigns (v : Vector) : Fin 8 → Bool :=
  fun i => decide (v i = -1)

/-- The shape of a doubled integer root. -/
def IsIntegerVector (v : Vector) : Prop :=
  (integerSupport v).card = 2 ∧
    ∀ i, v i = 0 ∨ v i = 2 ∨ v i = -2

/-- The shape of a doubled half-integral root. -/
def IsHalfVector (v : Vector) : Prop :=
  (∀ i, v i = 1 ∨ v i = -1) ∧
    minusCount (halfSigns v) % 2 = 0

/-- A vector has one of the two concrete E₈ root shapes. -/
def IsConcreteRootVector (v : Vector) : Prop :=
  IsIntegerVector v ∨ IsHalfVector v

instance isIntegerVectorDecidable (v : Vector) :
    Decidable (IsIntegerVector v) := by
  unfold IsIntegerVector
  letI : Decidable (∀ i : Fin 8,
      v i = 0 ∨ v i = 2 ∨ v i = -2) :=
    Fintype.decidableForallFintype
  infer_instance

instance isHalfVectorDecidable (v : Vector) :
    Decidable (IsHalfVector v) := by
  unfold IsHalfVector
  letI : Decidable (∀ i : Fin 8, v i = 1 ∨ v i = -1) :=
    Fintype.decidableForallFintype
  infer_instance

instance isConcreteRootVectorDecidable (v : Vector) :
    Decidable (IsConcreteRootVector v) := by
  unfold IsConcreteRootVector
  infer_instance

set_option maxHeartbeats 5000000 in
-- Finite verification of the two root-vector shapes.
private theorem rootVector_isConcreteRootVector_finite :
    ∀ r : Root, IsConcreteRootVector (rootVector r) := by
  decide

/-- Every enumerated root has one of the two concrete vector shapes. -/
theorem rootVector_isConcreteRootVector (r : Root) :
    IsConcreteRootVector (rootVector r) :=
  rootVector_isConcreteRootVector_finite r

private theorem integerVector_has_parameter
    (v : Vector) (h : IsIntegerVector v) :
    ∃ p : IntegerRootParam, integerRootVector p = v := by
  classical
  have build :
      ∀ (a b : Fin 8), a < b →
        integerSupport v = {a, b} →
        ∃ p : IntegerRootParam, integerRootVector p = v := by
    intro a b hab hs
    have ha_mem : a ∈ integerSupport v := by
      rw [hs]
      simp
    have hb_mem : b ∈ integerSupport v := by
      rw [hs]
      simp
    have hva_ne : v a ≠ 0 := by
      simpa [integerSupport] using ha_mem
    have hvb_ne : v b ≠ 0 := by
      simpa [integerSupport] using hb_mem
    have hva : v a = 2 ∨ v a = -2 :=
      (h.2 a).resolve_left hva_ne
    have hvb : v b = 2 ∨ v b = -2 :=
      (h.2 b).resolve_left hvb_ne
    let ba : Bool := decide (v a = -2)
    let bb : Bool := decide (v b = -2)
    have hba : signed 2 ba = v a := by
      rcases hva with hva | hva
      · simp [ba, signed, hva]
      · simp [ba, signed, hva]
    have hbb : signed 2 bb = v b := by
      rcases hvb with hvb | hvb
      · simp [bb, signed, hvb]
      · simp [bb, signed, hvb]
    let p : IntegerRootParam :=
      ⟨((a, b), (ba, bb)), hab⟩
    refine ⟨p, ?_⟩
    funext k
    by_cases hka : k = a
    · subst k
      simpa [p, integerRootVector] using hba
    by_cases hkb : k = b
    · subst k
      have hba_ne : b ≠ a := ne_of_gt hab
      simpa [p, integerRootVector, hba_ne] using hbb
    · have hvk : v k = 0 := by
        by_contra hvk_ne
        have hk_mem : k ∈ integerSupport v := by
          simp [integerSupport, hvk_ne]
        rw [hs] at hk_mem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk_mem
        exact hk_mem.elim hka hkb
      simp [p, integerRootVector, hka, hkb, hvk]
  obtain ⟨i, j, hij, hs⟩ := Finset.card_eq_two.mp h.1
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact build i j hijlt hs
  · exact build j i hjilt (hs.trans (Finset.pair_comm i j))

private theorem halfVector_has_parameter
    (v : Vector) (h : IsHalfVector v) :
    ∃ p : HalfRootParam, halfRootVector p = v := by
  let p : HalfRootParam :=
    ⟨halfSigns v, h.2⟩
  refine ⟨p, ?_⟩
  funext i
  rcases h.1 i with hi | hi
  · simp [p, halfRootVector, halfSigns, signed, hi]
  · simp [p, halfRootVector, halfSigns, signed, hi]

/-- A vector has a concrete root shape exactly when it is represented by a
root parameter. -/
theorem isConcreteRootVector_iff (v : Vector) :
    IsConcreteRootVector v ↔
      ∃ r : Root, rootVector r = v := by
  constructor
  · rintro (hI | hH)
    · obtain ⟨p, hp⟩ := integerVector_has_parameter v hI
      exact ⟨Sum.inl p, by simpa [rootVector] using hp⟩
    · obtain ⟨p, hp⟩ := halfVector_has_parameter v hH
      exact ⟨Sum.inr p, by simpa [rootVector] using hp⟩
  · rintro ⟨r, rfl⟩
    exact rootVector_isConcreteRootVector r

/-- A concrete root-shaped vector has a unique root parameter. -/
theorem existsUnique_rootVector_eq_of_isConcrete
    {v : Vector} (hv : IsConcreteRootVector v) :
    ∃! r : Root, rootVector r = v := by
  obtain ⟨r, hr⟩ := (isConcreteRootVector_iff v).mp hv
  refine ⟨r, hr, ?_⟩
  intro s hs
  exact rootVector_injective (hs.trans hr.symm)

end ConcreteRootSystem
end E8
end RiemannResearch
