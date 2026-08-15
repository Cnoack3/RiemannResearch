/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.LinearAlgebra.RootSystem.D4ZornOctonion

/-!
# Base change for the split Zorn octonion

The split Zorn formulas are integral polynomial formulas. This module records
their exact compatibility with every morphism of commutative rings. It is the
all-commutative-algebra layer needed before the related-triples point functor
can be represented by a coordinate Hopf algebra.

No representability or Spin group-scheme comparison is asserted here.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn

universe u v w

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]

/-- Coordinatewise base change of a split Zorn octonion. -/
def map (f : R →+* S) : Octonion R →+ Octonion S where
  toFun x := fun i => f (x i)
  map_zero' := by
    ext i
    simp
  map_add' x y := by
    ext i
    simp

@[simp] theorem map_apply (f : R →+* S) (x : Octonion R) (i : Fin 8) :
    map f x i = f (x i) :=
  rfl

@[simp] theorem map_id :
    map (RingHom.id R) = AddMonoidHom.id (Octonion R) := by
  ext x i
  rfl

theorem map_comp (f : R →+* S) (g : S →+* T) :
    map (g.comp f) = (map g).comp (map f) := by
  ext x i
  rfl

@[simp] theorem map_mul (f : R →+* S) (x y : Octonion R) :
    map f (mul R x y) = mul S (map f x) (map f y) := by
  ext i
  fin_cases i <;> simp [map, mul]

@[simp] theorem map_norm (f : R →+* S) (x : Octonion R) :
    f (norm R x) = norm S (map f x) := by
  simp [map, norm]

@[simp] theorem map_conjugate (f : R →+* S) (x : Octonion R) :
    map f (conjugate R x) = conjugate S (map f x) := by
  ext i
  fin_cases i <;> simp [map, conjugate]

@[simp] theorem map_paraMul (f : R →+* S) (x y : Octonion R) :
    map f (paraMul R x y) = paraMul S (map f x) (map f y) := by
  simp [paraMul]

@[simp] theorem map_normPolar (f : R →+* S) (x y : Octonion R) :
    f (normPolar R x y) = normPolar S (map f x) (map f y) := by
  simp [normPolar]

@[simp] theorem map_trialityTensor
    (f : R →+* S) (x y z : Octonion R) :
    f (trialityTensor R x y z) =
      trialityTensor S (map f x) (map f y) (map f z) := by
  simp [trialityTensor]

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn
