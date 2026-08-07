/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.PrincipalIdealDomain
import RiemannResearch.Logic.PointedKernel

/-!
# Coprime restriction--corestriction

This module isolates the elementary abelian argument behind coprime-degree
descent. It deliberately assumes additive restriction and corestriction maps;
it does not assert that such maps exist for nonabelian cohomology.
-/

namespace RiemannResearch.GroupTheory

/-- Two restriction maps with coprime index formulas jointly detect zero.

This is the precise abelian Bézout step used by the degree-five/degree-six
two-gauge audit. The statement does not apply to pointed nonabelian H¹.
-/
theorem eq_zero_of_coprime_restrictions
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (resM : A →+ B) (resN : A →+ C)
    (corM : B →+ A) (corN : C →+ A)
    {m n : ℕ}
    (hM : ∀ x, corM (resM x) = m • x)
    (hN : ∀ x, corN (resN x) = n • x)
    (hcop : m.Coprime n)
    {x : A} (hxM : resM x = 0) (hxN : resN x = 0) : x = 0 := by
  apply (nsmul_eq_zero_iff_of_coprime hcop).mp
  constructor
  · rw [← hM x, hxM, map_zero]
  · rw [← hN x, hxN, map_zero]

/-- A finite family of annihilating degrees with gcd one detects zero.

This is the abstract additive core of Lemma 6.36, “Abelian Bezout descent,”
in the E8 Serre II manuscript. The integer-valued Finset gcd hypothesis
produces an integral Bezout combination. As in the two-map theorem above,
the result applies only after restriction--corestriction has supplied the
displayed annihilator equations in an additive commutative group.
-/
theorem eq_zero_of_gcd_one_annihilators
    {ι A : Type*} [AddCommGroup A]
    (s : Finset ι) (degree : ι → ℕ)
    (hgcd : s.gcd (fun i => (degree i : ℤ)) = 1)
    {x : A} (hkill : ∀ i ∈ s, degree i • x = 0) : x = 0 := by
  classical
  obtain ⟨coefficient, hcoefficient⟩ :=
    Finset.gcd_eq_sum_mul s (fun i => (degree i : ℤ))
  have hbezout : ∑ i ∈ s, coefficient i * (degree i : ℤ) = 1 := by
    calc
      ∑ i ∈ s, coefficient i * (degree i : ℤ) =
          ∑ i ∈ s, (degree i : ℤ) * coefficient i := by
            apply Finset.sum_congr rfl
            intro i hi
            exact mul_comm _ _
      _ = s.gcd (fun i => (degree i : ℤ)) := hcoefficient.symm
      _ = 1 := hgcd
  let zsmulHom : ℤ →+ A :=
    { toFun := fun n => n • x
      map_zero' := zero_zsmul x
      map_add' := fun m n => add_zsmul x m n }
  have hz : (∑ i ∈ s, coefficient i * (degree i : ℤ)) • x = 0 := by
    change zsmulHom (∑ i ∈ s, coefficient i * (degree i : ℤ)) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    change (coefficient i * (degree i : ℤ)) • x = 0
    rw [mul_zsmul]
    have hd : (degree i : ℤ) • x = 0 := by
      simpa using hkill i hi
    rw [hd, smul_zero]
  simpa [hbezout] using hz

/-- A finite family of additive restriction maps with gcd-one index formulas
jointly detects zero. -/
theorem eq_zero_of_gcd_one_restrictions
    {ι A : Type*} [AddCommGroup A]
    (B : ι → Type*) [∀ i, AddCommGroup (B i)]
    (s : Finset ι) (degree : ι → ℕ)
    (res : ∀ i, A →+ B i) (cor : ∀ i, B i →+ A)
    (hindex : ∀ i x, cor i (res i x) = degree i • x)
    (hgcd : s.gcd (fun i => (degree i : ℤ)) = 1)
    {x : A} (hres : ∀ i ∈ s, res i x = 0) :
    x = 0 := by
  apply eq_zero_of_gcd_one_annihilators s degree hgcd
  intro i hi
  rw [← hindex i x, hres i hi, map_zero]

/-- The joint additive restriction map has trivial pointed kernel when its
restriction--corestriction degrees have gcd one. -/
theorem hasTrivialKernel_restrictionFamily_of_gcd_one
    {ι A : Type*} [AddCommGroup A]
    (B : ι → Type*) [∀ i, AddCommGroup (B i)]
    (s : Finset ι) (degree : ι → ℕ)
    (res : ∀ i, A →+ B i) (cor : ∀ i, B i →+ A)
    (hindex : ∀ i x, cor i (res i x) = degree i • x)
    (hgcd : s.gcd (fun i => (degree i : ℤ)) = 1) :
    RiemannResearch.Logic.HasTrivialKernel
      (0 : A) (fun i : ↥s => (0 : B i.1))
      (fun x i => res i.1 x) := by
  intro x
  constructor
  · intro hx
    apply eq_zero_of_gcd_one_restrictions
      B s degree res cor hindex hgcd
    intro i hi
    exact congrFun hx ⟨i, hi⟩
  · rintro rfl
    funext i
    exact map_zero (res i.1)

end RiemannResearch.GroupTheory
