/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.PointFields

/-!
# Coprime point-field degrees

This module packages the index-one step used by the E8 Serre II splitting-field
packets. Once actual finite point fields of coprime degrees are constructed,
their degrees force the point-field index to equal one.
-/

namespace RiemannResearch.AlgebraicGeometry

/-- Two coprime finite point-field degrees force the point-field index to be
one. -/
theorem pointFieldIndex_eq_one_of_two_point_degrees
    {Extension : Type*}
    (isFinite : Extension → Prop) (degree : Extension → ℕ)
    (hasPoint : Extension → Prop) {d₁ d₂ : ℕ}
    (h₁ : d₁ ∈ finitePointDegrees isFinite degree hasPoint)
    (h₂ : d₂ ∈ finitePointDegrees isFinite degree hasPoint)
    (hcoprime : Nat.gcd d₁ d₂ = 1) :
    pointFieldIndex isFinite degree hasPoint = 1 := by
  unfold pointFieldIndex
  apply Nat.dvd_one.mp
  rw [← hcoprime]
  exact Nat.dvd_gcd
    (Nat.setGcd_dvd_of_mem h₁)
    (Nat.setGcd_dvd_of_mem h₂)

/-- Three finite point-field degrees with gcd one force the point-field index
to be one. -/
theorem pointFieldIndex_eq_one_of_three_point_degrees
    {Extension : Type*}
    (isFinite : Extension → Prop) (degree : Extension → ℕ)
    (hasPoint : Extension → Prop) {d₁ d₂ d₃ : ℕ}
    (h₁ : d₁ ∈ finitePointDegrees isFinite degree hasPoint)
    (h₂ : d₂ ∈ finitePointDegrees isFinite degree hasPoint)
    (h₃ : d₃ ∈ finitePointDegrees isFinite degree hasPoint)
    (hgcd : Nat.gcd (Nat.gcd d₁ d₂) d₃ = 1) :
    pointFieldIndex isFinite degree hasPoint = 1 := by
  unfold pointFieldIndex
  apply Nat.dvd_one.mp
  rw [← hgcd]
  exact Nat.dvd_gcd
    (Nat.dvd_gcd
      (Nat.setGcd_dvd_of_mem h₁)
      (Nat.setGcd_dvd_of_mem h₂))
    (Nat.setGcd_dvd_of_mem h₃)

end RiemannResearch.AlgebraicGeometry
