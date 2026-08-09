/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.AlgebraicGeometry.PointFieldIndexOne

/-!
# Degree-one zero cycles from splitting fields

This module separates two logically different steps in restriction arguments
for nonabelian pointed sets.

* A DegreeOneSplittingCycle is a finite integer combination of degrees of
  extensions over which a chosen class is neutral, with total degree one.
* CoprimeRestrictionDetectsBasepoint is the additional descent statement
  saying that point-field index one forces the original class to be the
  distinguished point.

The first step is purely numerical. The second is not a consequence of gcd
one for an arbitrary pointed set and remains a load-bearing hypothesis in
applications to Serre's Conjecture II.
-/

namespace RiemannResearch.AlgebraicGeometry

/-- A class is neutral over an extension when its supplied restriction equals
the supplied local neutral class. -/
def IsNeutralOver
    {X Extension : Type*} (Y : Extension → Type*)
    (neutral : ∀ L, Y L) (restrict : ∀ L, X → Y L)
    (x : X) (L : Extension) : Prop :=
  restrict L x = neutral L

/-- The gcd of the degrees of all finite extensions neutralizing x is one.

For actual scalar extension on torsors, this is the point-field-index
formulation of a degree-one zero-cycle conclusion. -/
def HasCoprimeNeutralizingExtensions
    {X Extension : Type*} (isFinite : Extension → Prop)
    (degree : Extension → ℕ) (Y : Extension → Type*)
    (neutral : ∀ L, Y L) (restrict : ∀ L, X → Y L)
    (x : X) : Prop :=
  pointFieldIndex isFinite degree
    (IsNeutralOver Y neutral restrict x) = 1

/-- A finite zero-cycle of total degree one supported on extensions over
which x is neutral. Integer coefficients allow the usual Bézout
combination of splitting degrees. -/
structure DegreeOneSplittingCycle
    {X Extension : Type*} (isFinite : Extension → Prop)
    (degree : Extension → ℕ) (Y : Extension → Type*)
    (neutral : ∀ L, Y L) (restrict : ∀ L, X → Y L)
    (x : X) where
  cardinality : ℕ
  extension : Fin cardinality → Extension
  coefficient : Fin cardinality → ℤ
  finite : ∀ i, isFinite (extension i)
  locally_neutral : ∀ i, IsNeutralOver Y neutral restrict x (extension i)
  degree_one :
    ∑ i, coefficient i * (degree (extension i) : ℤ) = 1

/-- A degree-one splitting cycle forces the gcd of all finite neutralizing
extension degrees to equal one. -/
theorem hasCoprimeNeutralizingExtensions_of_degreeOneSplittingCycle
    {X Extension : Type*} (isFinite : Extension → Prop)
    (degree : Extension → ℕ) (Y : Extension → Type*)
    (neutral : ∀ L, Y L) (restrict : ∀ L, X → Y L)
    {x : X}
    (cycle : DegreeOneSplittingCycle isFinite degree Y neutral restrict x) :
    HasCoprimeNeutralizingExtensions isFinite degree Y neutral restrict x := by
  unfold HasCoprimeNeutralizingExtensions pointFieldIndex
  apply Nat.dvd_one.mp
  have hdiv : ∀ i, Nat.setGcd
      (finitePointDegrees isFinite degree
        (IsNeutralOver Y neutral restrict x)) ∣
      degree (cycle.extension i) := by
    intro i
    apply Nat.setGcd_dvd_of_mem
    exact ⟨cycle.extension i,
      ⟨cycle.finite i, cycle.locally_neutral i⟩, rfl⟩
  have hdivz : (Nat.setGcd
      (finitePointDegrees isFinite degree
        (IsNeutralOver Y neutral restrict x)) : ℤ) ∣
      (1 : ℤ) := by
    rw [← cycle.degree_one]
    apply Finset.dvd_sum
    intro i _
    have hi : (Nat.setGcd
        (finitePointDegrees isFinite degree
          (IsNeutralOver Y neutral restrict x)) : ℤ) ∣
        (degree (cycle.extension i) : ℤ) := by
      exact_mod_cast hdiv i
    exact dvd_mul_of_dvd_right hi _
  exact_mod_cast hdivz

/-- The open descent principle needed after obtaining coprime neutralizing
extensions: point-field index one detects the global basepoint. -/
def CoprimeRestrictionDetectsBasepoint
    {X Extension : Type*} (x₀ : X)
    (isFinite : Extension → Prop) (degree : Extension → ℕ)
    (Y : Extension → Type*) (neutral : ∀ L, Y L)
    (restrict : ∀ L, X → Y L) : Prop :=
  ∀ x, HasCoprimeNeutralizingExtensions
    isFinite degree Y neutral restrict x → x = x₀

/-- A degree-one splitting cycle gives the global basepoint once coprime
restriction detects that basepoint. -/
theorem eq_basepoint_of_degreeOneSplittingCycle
    {X Extension : Type*} (x₀ : X)
    (isFinite : Extension → Prop) (degree : Extension → ℕ)
    (Y : Extension → Type*) (neutral : ∀ L, Y L)
    (restrict : ∀ L, X → Y L)
    (hdescent : CoprimeRestrictionDetectsBasepoint
      x₀ isFinite degree Y neutral restrict)
    {x : X}
    (cycle : DegreeOneSplittingCycle isFinite degree Y neutral restrict x) :
    x = x₀ :=
  hdescent x
    (hasCoprimeNeutralizingExtensions_of_degreeOneSplittingCycle
      isFinite degree Y neutral restrict cycle)

/-- Degree-one splitting cycles for every class, together with coprime
restriction descent, make the global pointed set a subsingleton. -/
theorem subsingleton_of_degreeOneSplittingCycles_of_coprimeRestriction
    {X Extension : Type*} (x₀ : X)
    (isFinite : Extension → Prop) (degree : Extension → ℕ)
    (Y : Extension → Type*) (neutral : ∀ L, Y L)
    (restrict : ∀ L, X → Y L)
    (hcycles : ∀ x, Nonempty (DegreeOneSplittingCycle
      isFinite degree Y neutral restrict x))
    (hdescent : CoprimeRestrictionDetectsBasepoint
      x₀ isFinite degree Y neutral restrict) :
    Subsingleton X := by
  constructor
  intro x y
  obtain ⟨hx⟩ := hcycles x
  obtain ⟨hy⟩ := hcycles y
  rw [eq_basepoint_of_degreeOneSplittingCycle x₀ isFinite degree
        Y neutral restrict hdescent hx,
      eq_basepoint_of_degreeOneSplittingCycle x₀ isFinite degree
        Y neutral restrict hdescent hy]

/-- If every class has a degree-one splitting cycle, then coprime-restriction
basepoint detection is equivalent to the whole pointed set being a
subsingleton.

Thus, after the zero-cycle input is supplied, the detection principle is not
a weaker substitute for global neutrality. -/
theorem coprimeRestrictionDetectsBasepoint_iff_subsingleton_of_degreeOneSplittingCycles
    {X Extension : Type*} (x₀ : X)
    (isFinite : Extension → Prop) (degree : Extension → ℕ)
    (Y : Extension → Type*) (neutral : ∀ L, Y L)
    (restrict : ∀ L, X → Y L)
    (hcycles : ∀ x, Nonempty (DegreeOneSplittingCycle
      isFinite degree Y neutral restrict x)) :
    CoprimeRestrictionDetectsBasepoint x₀ isFinite degree Y neutral restrict
      ↔ Subsingleton X := by
  constructor
  · intro hdescent
    exact subsingleton_of_degreeOneSplittingCycles_of_coprimeRestriction
      x₀ isFinite degree Y neutral restrict hcycles hdescent
  · intro hsub x _
    exact @Subsingleton.elim X hsub x x₀

end RiemannResearch.AlgebraicGeometry
