/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.NumberTheory.FrobeniusNumber

/-!
# Rational point fields and indices

This module provides a small abstract interface for comparing the fields over
which geometric objects have rational points. An arbitrary type Extension
indexes field extensions of a fixed base field. The predicates isFinite and
hasPoint, and the function degree, supply the field-theoretic semantics.

The index is the gcd, via Nat.setGcd, of the degrees of all finite point
fields. Equality of point predicates therefore gives equality of the complete
finite degree spectra and of their indices.
-/

namespace RiemannResearch.AlgebraicGeometry

/-- The set of extension indices over which the object has a rational point. -/
def pointFields {Extension : Type*} (hasPoint : Extension → Prop) :
    Set Extension :=
  {L | hasPoint L}

/-- The finite extension indices over which the object has a rational point. -/
def finitePointFields {Extension : Type*} (isFinite : Extension → Prop)
    (hasPoint : Extension → Prop) : Set Extension :=
  {L | isFinite L ∧ hasPoint L}

/-- The degrees of all finite extensions over which the object has a point. -/
def finitePointDegrees {Extension : Type*} (isFinite : Extension → Prop)
    (degree : Extension → ℕ) (hasPoint : Extension → Prop) : Set ℕ :=
  degree '' finitePointFields isFinite hasPoint

/-- The gcd of the degrees of all finite point fields.

When Extension indexes all field extensions and degree L = [L : k], this is
the usual splitting-field description of the index.
-/
noncomputable def pointFieldIndex {Extension : Type*}
    (isFinite : Extension → Prop) (degree : Extension → ℕ)
    (hasPoint : Extension → Prop) : ℕ :=
  Nat.setGcd (finitePointDegrees isFinite degree hasPoint)

/-- Pointwise equivalence gives equality of all point fields. -/
theorem pointFields_eq {Extension : Type*}
    {X Y : Extension → Prop} (h : ∀ L, X L ↔ Y L) :
    pointFields X = pointFields Y := by
  ext L
  exact h L

/-- Pointwise equivalence gives equality of all finite point fields. -/
theorem finitePointFields_eq {Extension : Type*}
    (isFinite : Extension → Prop) {X Y : Extension → Prop}
    (h : ∀ L, X L ↔ Y L) :
    finitePointFields isFinite X = finitePointFields isFinite Y := by
  ext L
  exact and_congr Iff.rfl (h L)

/-- Pointwise equivalence gives equality of all finite point-field degrees. -/
theorem finitePointDegrees_eq {Extension : Type*}
    (isFinite : Extension → Prop) (degree : Extension → ℕ)
    {X Y : Extension → Prop} (h : ∀ L, X L ↔ Y L) :
    finitePointDegrees isFinite degree X =
      finitePointDegrees isFinite degree Y := by
  unfold finitePointDegrees
  rw [finitePointFields_eq isFinite h]

/-- Pointwise equivalence gives equality of point-field indices. -/
theorem pointFieldIndex_eq {Extension : Type*}
    (isFinite : Extension → Prop) (degree : Extension → ℕ)
    {X Y : Extension → Prop} (h : ∀ L, X L ↔ Y L) :
    pointFieldIndex isFinite degree X =
      pointFieldIndex isFinite degree Y := by
  unfold pointFieldIndex
  rw [finitePointDegrees_eq isFinite degree h]

/-- Two degree sets have the same gcd when each is divisibility-cofinal in the
other. -/
theorem setGcd_eq_of_dvd_cofinal {s t : Set ℕ}
    (hst : ∀ n ∈ s, ∃ m ∈ t, m ∣ n)
    (hts : ∀ n ∈ t, ∃ m ∈ s, m ∣ n) :
    Nat.setGcd s = Nat.setGcd t := by
  apply Nat.dvd_antisymm
  · rw [Nat.dvd_setGcd_iff]
    intro n hn
    obtain ⟨m, hm, hmn⟩ := hts n hn
    exact (Nat.setGcd_dvd_of_mem hm).trans hmn
  · rw [Nat.dvd_setGcd_iff]
    intro n hn
    obtain ⟨m, hm, hmn⟩ := hst n hn
    exact (Nat.setGcd_dvd_of_mem hm).trans hmn

/-- A subset has the same gcd as a larger degree set if every degree in the
larger set is divisible by one in the subset. -/
theorem setGcd_eq_of_subset_of_exists_dvd {closed splitting : Set ℕ}
    (hsub : closed ⊆ splitting)
    (hdesc : ∀ n ∈ splitting, ∃ m ∈ closed, m ∣ n) :
    Nat.setGcd closed = Nat.setGcd splitting := by
  apply setGcd_eq_of_dvd_cofinal
  · intro n hn
    exact ⟨n, hsub hn, dvd_rfl⟩
  · exact hdesc

/-- Comparison of the traditional closed-point index with the point-field
index.

The first hypothesis sends a closed point to its residue point field. The
second sends a point over a finite extension to its closed image, whose degree
divides the extension degree.
-/
theorem closedPointIndex_eq_pointFieldIndex
    {Extension : Type*}
    (isFinite : Extension → Prop) (degree : Extension → ℕ)
    (hasPoint : Extension → Prop) (closedPointDegrees : Set ℕ)
    (residueFieldGivesPoint :
      closedPointDegrees ⊆ finitePointDegrees isFinite degree hasPoint)
    (pointDescendsToClosedPoint :
      ∀ n ∈ finitePointDegrees isFinite degree hasPoint,
        ∃ m ∈ closedPointDegrees, m ∣ n) :
    Nat.setGcd closedPointDegrees =
      pointFieldIndex isFinite degree hasPoint := by
  unfold pointFieldIndex
  exact setGcd_eq_of_subset_of_exists_dvd
    residueFieldGivesPoint pointDescendsToClosedPoint

/-- Fixed-locus extraction of rational points.

If every point of X has a limit in the fixed locus, the fixed locus is a
coproduct of copies of Y, and one fixed component includes into X, then X and
Y have points over exactly the same extensions.
-/
theorem point_iff_of_fixedLocus_coproduct
    {Extension Component : Type*}
    (hasPointX hasPointY hasFixedPoint : Extension → Prop)
    (limit : ∀ L, hasPointX L → hasFixedPoint L)
    (fixedPoint_iff :
      ∀ L, hasFixedPoint L ↔ ∃ _ : Component, hasPointY L)
    (includeFixedComponent : ∀ L, hasPointY L → hasPointX L) :
    ∀ L, hasPointX L ↔ hasPointY L := by
  intro L
  constructor
  · intro hx
    obtain ⟨_, hy⟩ := (fixedPoint_iff L).mp (limit L hx)
    exact hy
  · exact includeFixedComponent L

end RiemannResearch.AlgebraicGeometry
