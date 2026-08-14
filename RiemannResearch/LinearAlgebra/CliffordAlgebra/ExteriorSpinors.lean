/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.QuadraticForm.Dual
import Mathlib.RepresentationTheory.Basic

/-!
# Exterior Fock spinors for a hyperbolic quadratic space

For a module `U`, this file constructs the creation-annihilation action of
the Clifford algebra of the hyperbolic quadratic form on
`U* × U` on the exterior algebra `Λ U`.

The construction is fully algebraic. Creation is left exterior
multiplication and annihilation is Mathlib's Clifford contraction on the
zero-form Clifford algebra, which is the exterior algebra. The canonical
anticommutation relations imply the Clifford relation, hence the universal
property supplies an algebra homomorphism

`Cl(U* × U) → End(Λ U)`.

The file also proves directly that generators exchange exterior parity and
therefore that the even Clifford algebra acts on the even and odd exterior
pieces separately. It does not prove finite-rank formulas or that the two
restricted actions jointly identify the even Clifford algebra with a product
of endomorphism algebras.
-/

namespace RiemannResearch.LinearAlgebra.CliffordEven

open CliffordAlgebra

universe uK uU uA uV

section RestrictAction

variable {K : Type uK} [CommSemiring K]
variable {A : Type uA} [Semiring A] [Algebra K A]
variable {V : Type uV} [AddCommMonoid V] [Module K V]

/-- Restrict an algebra action to an invariant submodule. -/
def restrictAlgAction (ρ : A →ₐ[K] Module.End K V)
    (P : Submodule K V)
    (hP : ∀ (a : A) {x : V}, x ∈ P → ρ a x ∈ P) :
    A →ₐ[K] Module.End K P where
  toFun a :=
    { toFun := fun x => ⟨ρ a x, hP a x.property⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact (ρ a).map_add x y
      map_smul' := by
        intro r x
        apply Subtype.ext
        exact (ρ a).map_smul r x }
  map_one' := by
    ext x
    exact DFunLike.congr_fun ρ.map_one (x : V)
  map_mul' a b := by
    ext x
    exact DFunLike.congr_fun (ρ.map_mul a b) (x : V)
  map_zero' := by
    ext x
    exact DFunLike.congr_fun ρ.map_zero (x : V)
  map_add' a b := by
    ext x
    exact DFunLike.congr_fun (ρ.map_add a b) (x : V)
  commutes' r := by
    ext x
    exact DFunLike.congr_fun (ρ.commutes r) (x : V)

end RestrictAction

section ExteriorFock

variable {K : Type uK} [CommRing K]
variable {U : Type uU} [AddCommGroup U] [Module K U]

/-- The exterior-algebra Fock space attached to `U`. -/
abbrev ExteriorFockSpace := ExteriorAlgebra K U

/-- The even exterior-parity piece of the Fock space. -/
abbrev ExteriorFockEven :=
  ↥(CliffordAlgebra.evenOdd (0 : QuadraticForm K U) 0)

/-- The odd exterior-parity piece of the Fock space. -/
abbrev ExteriorFockOdd :=
  ↥(CliffordAlgebra.evenOdd (0 : QuadraticForm K U) 1)

/-- Exterior multiplication by a vector, linear in that vector. -/
def exteriorCreation :
    U →ₗ[K] Module.End K (ExteriorFockSpace (K := K) (U := U)) where
  toFun v := LinearMap.mulLeft K (ExteriorAlgebra.ι K v)
  map_add' v w := by
    ext x
    change
      ExteriorAlgebra.ι K (v + w) * x =
        ExteriorAlgebra.ι K v * x + ExteriorAlgebra.ι K w * x
    rw [map_add, add_mul]
  map_smul' a v := by
    ext x
    change
      ExteriorAlgebra.ι K (a • v) * x =
        a • (ExteriorAlgebra.ι K v * x)
    rw [map_smul]
    exact Algebra.smul_mul_assoc a _ x

/-- Contraction by a dual vector, linear in that vector. -/
def exteriorAnnihilation :
    Module.Dual K U →ₗ[K]
      Module.End K (ExteriorFockSpace (K := K) (U := U)) :=
  CliffordAlgebra.contractLeft

/-- Creation by one vector squares to zero. -/
theorem exteriorCreation_sq (v : U) :
    exteriorCreation (K := K) (U := U) v *
        exteriorCreation (K := K) (U := U) v = 0 := by
  ext z
  change ExteriorAlgebra.ι K v * (ExteriorAlgebra.ι K v * z) = 0
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

/-- Annihilation by one dual vector squares to zero. -/
theorem exteriorAnnihilation_sq (d : Module.Dual K U) :
    exteriorAnnihilation (K := K) (U := U) d *
        exteriorAnnihilation (K := K) (U := U) d = 0 := by
  ext z
  exact CliffordAlgebra.contractLeft_contractLeft d z

/-- Creation operators anticommute. -/
theorem exteriorCreation_anticommute (v w : U) :
    exteriorCreation (K := K) (U := U) v *
          exteriorCreation (K := K) (U := U) w +
        exteriorCreation (K := K) (U := U) w *
          exteriorCreation (K := K) (U := U) v = 0 := by
  ext z
  change
    ExteriorAlgebra.ι K v * (ExteriorAlgebra.ι K w * z) +
        ExteriorAlgebra.ι K w * (ExteriorAlgebra.ι K v * z) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul,
    ExteriorAlgebra.ι_add_mul_swap, zero_mul]

/-- Annihilation operators anticommute. -/
theorem exteriorAnnihilation_anticommute
    (d e : Module.Dual K U) :
    exteriorAnnihilation (K := K) (U := U) d *
          exteriorAnnihilation (K := K) (U := U) e +
        exteriorAnnihilation (K := K) (U := U) e *
          exteriorAnnihilation (K := K) (U := U) d = 0 := by
  ext z
  change
    CliffordAlgebra.contractLeft d
          (CliffordAlgebra.contractLeft e z) +
        CliffordAlgebra.contractLeft e
          (CliffordAlgebra.contractLeft d z) = 0
  rw [CliffordAlgebra.contractLeft_comm]
  exact neg_add_cancel _

/-- The mixed creation-annihilation anticommutator is evaluation. -/
theorem exteriorAnnihilation_creation_anticommutator
    (d : Module.Dual K U) (v : U) :
    exteriorAnnihilation (K := K) (U := U) d *
          exteriorCreation (K := K) (U := U) v +
        exteriorCreation (K := K) (U := U) v *
          exteriorAnnihilation (K := K) (U := U) d =
      algebraMap K
        (Module.End K (ExteriorFockSpace (K := K) (U := U))) (d v) := by
  ext z
  change
    CliffordAlgebra.contractLeft d (ExteriorAlgebra.ι K v * z) +
        ExteriorAlgebra.ι K v * CliffordAlgebra.contractLeft d z =
      (algebraMap K
        (Module.End K (ExteriorFockSpace (K := K) (U := U))) (d v)) z
  rw [CliffordAlgebra.contractLeft_ι_mul]
  simp [Algebra.smul_def]

/-- The hyperbolic Clifford generator: annihilation plus creation. -/
def exteriorFockGenerator :
    (Module.Dual K U × U) →ₗ[K]
      Module.End K (ExteriorFockSpace (K := K) (U := U)) :=
  LinearMap.coprod exteriorAnnihilation exteriorCreation

@[simp]
theorem exteriorFockGenerator_apply
    (x : Module.Dual K U × U)
    (z : ExteriorFockSpace (K := K) (U := U)) :
    exteriorFockGenerator (K := K) (U := U) x z =
      CliffordAlgebra.contractLeft x.1 z +
        ExteriorAlgebra.ι K x.2 * z :=
  rfl

/-- The creation-annihilation generator satisfies the hyperbolic Clifford
relation. -/
theorem exteriorFockGenerator_sq (x : Module.Dual K U × U) :
    exteriorFockGenerator (K := K) (U := U) x *
        exteriorFockGenerator (K := K) (U := U) x =
      algebraMap K
        (Module.End K (ExteriorFockSpace (K := K) (U := U)))
        (QuadraticForm.dualProd K U x) := by
  ext z
  simp only [Module.End.mul_apply, exteriorFockGenerator_apply,
    QuadraticForm.dualProd_apply]
  rw [map_add, mul_add, CliffordAlgebra.contractLeft_contractLeft,
    CliffordAlgebra.contractLeft_ι_mul, ← mul_assoc,
    ExteriorAlgebra.ι_sq_zero]
  simp [Algebra.smul_def]

/-- The canonical Fock action of the Clifford algebra of `U* × U`. -/
def exteriorCliffordAction :
    CliffordAlgebra (QuadraticForm.dualProd K U) →ₐ[K]
      Module.End K (ExteriorFockSpace (K := K) (U := U)) :=
  CliffordAlgebra.lift (QuadraticForm.dualProd K U)
    ⟨exteriorFockGenerator,
      exteriorFockGenerator_sq⟩

@[simp]
theorem exteriorCliffordAction_ι (x : Module.Dual K U × U) :
    exteriorCliffordAction (K := K) (U := U)
        (CliffordAlgebra.ι (QuadraticForm.dualProd K U) x) =
      exteriorFockGenerator (K := K) (U := U) x := by
  simpa only [exteriorCliffordAction] using
    (CliffordAlgebra.lift_ι_apply
      (exteriorFockGenerator (K := K) (U := U))
      (exteriorFockGenerator_sq (K := K) (U := U)) x)

section Parity

theorem exteriorIota_mul_mem_evenOdd
    (v : U) {n : ZMod 2}
    {z : ExteriorFockSpace (K := K) (U := U)}
    (hz : z ∈ CliffordAlgebra.evenOdd
      (0 : QuadraticForm K U) n) :
    ExteriorAlgebra.ι K v * z ∈
      CliffordAlgebra.evenOdd (0 : QuadraticForm K U) (1 + n) := by
  apply CliffordAlgebra.evenOdd_mul_le
    (0 : QuadraticForm K U) 1 n
  exact Submodule.mul_mem_mul
    (CliffordAlgebra.ι_mem_evenOdd_one
      (0 : QuadraticForm K U) v) hz

theorem exteriorIota_mul_mem_odd_of_mem_even
    (v : U) {z : ExteriorFockSpace (K := K) (U := U)}
    (hz : z ∈ CliffordAlgebra.evenOdd
      (0 : QuadraticForm K U) 0) :
    ExteriorAlgebra.ι K v * z ∈
      CliffordAlgebra.evenOdd (0 : QuadraticForm K U) 1 := by
  simpa using exteriorIota_mul_mem_evenOdd v hz

theorem exteriorIota_mul_mem_even_of_mem_odd
    (v : U) {z : ExteriorFockSpace (K := K) (U := U)}
    (hz : z ∈ CliffordAlgebra.evenOdd
      (0 : QuadraticForm K U) 1) :
    ExteriorAlgebra.ι K v * z ∈
      CliffordAlgebra.evenOdd (0 : QuadraticForm K U) 0 := by
  have h : (1 + 1 : ZMod 2) = 0 := by decide
  rw [← h]
  exact exteriorIota_mul_mem_evenOdd v hz

/-- Contraction exchanges even exterior parity for odd parity. -/
theorem contractLeft_mem_odd_of_mem_even
    (d : Module.Dual K U)
    {z : ExteriorFockSpace (K := K) (U := U)}
    (hz : z ∈ CliffordAlgebra.evenOdd
      (0 : QuadraticForm K U) 0) :
    CliffordAlgebra.contractLeft d z ∈
      CliffordAlgebra.evenOdd (0 : QuadraticForm K U) 1 := by
  induction z, hz using
      CliffordAlgebra.even_induction (0 : QuadraticForm K U) with
  | algebraMap r =>
      rw [CliffordAlgebra.contractLeft_algebraMap]
      exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
      rw [mul_assoc, CliffordAlgebra.contractLeft_ι_mul]
      apply Submodule.sub_mem
      · exact Submodule.smul_mem _ (d m₁)
          (exteriorIota_mul_mem_odd_of_mem_even m₂ hx)
      · apply exteriorIota_mul_mem_odd_of_mem_even
        rw [CliffordAlgebra.contractLeft_ι_mul]
        apply Submodule.sub_mem
        · exact Submodule.smul_mem _ (d m₂) hx
        · exact exteriorIota_mul_mem_even_of_mem_odd m₂ ih

/-- Contraction exchanges odd exterior parity for even parity. -/
theorem contractLeft_mem_even_of_mem_odd
    (d : Module.Dual K U)
    {z : ExteriorFockSpace (K := K) (U := U)}
    (hz : z ∈ CliffordAlgebra.evenOdd
      (0 : QuadraticForm K U) 1) :
    CliffordAlgebra.contractLeft d z ∈
      CliffordAlgebra.evenOdd (0 : QuadraticForm K U) 0 := by
  induction z, hz using
      CliffordAlgebra.odd_induction (0 : QuadraticForm K U) with
  | ι v =>
      rw [CliffordAlgebra.contractLeft_ι]
      rw [← CliffordAlgebra.even_toSubmodule]
      exact
        (CliffordAlgebra.even
          (0 : QuadraticForm K U)).algebraMap_mem (d v)
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
      rw [mul_assoc, CliffordAlgebra.contractLeft_ι_mul]
      apply Submodule.sub_mem
      · exact Submodule.smul_mem _ (d m₁)
          (exteriorIota_mul_mem_even_of_mem_odd m₂ hx)
      · apply exteriorIota_mul_mem_even_of_mem_odd
        rw [CliffordAlgebra.contractLeft_ι_mul]
        apply Submodule.sub_mem
        · exact Submodule.smul_mem _ (d m₂) hx
        · exact exteriorIota_mul_mem_odd_of_mem_even m₂ ih

/-- Every hyperbolic Clifford generator sends even Fock parity to odd. -/
theorem exteriorFockGenerator_mem_odd_of_mem_even
    (x : Module.Dual K U × U)
    {z : ExteriorFockSpace (K := K) (U := U)}
    (hz : z ∈ CliffordAlgebra.evenOdd
      (0 : QuadraticForm K U) 0) :
    exteriorFockGenerator (K := K) (U := U) x z ∈
      CliffordAlgebra.evenOdd (0 : QuadraticForm K U) 1 :=
  Submodule.add_mem _
    (contractLeft_mem_odd_of_mem_even x.1 hz)
    (exteriorIota_mul_mem_odd_of_mem_even x.2 hz)

/-- Every hyperbolic Clifford generator sends odd Fock parity to even. -/
theorem exteriorFockGenerator_mem_even_of_mem_odd
    (x : Module.Dual K U × U)
    {z : ExteriorFockSpace (K := K) (U := U)}
    (hz : z ∈ CliffordAlgebra.evenOdd
      (0 : QuadraticForm K U) 1) :
    exteriorFockGenerator (K := K) (U := U) x z ∈
      CliffordAlgebra.evenOdd (0 : QuadraticForm K U) 0 :=
  Submodule.add_mem _
    (contractLeft_mem_even_of_mem_odd x.1 hz)
    (exteriorIota_mul_mem_even_of_mem_odd x.2 hz)

/-- The even hyperbolic Clifford algebra preserves even exterior parity. -/
theorem exteriorCliffordAction_mem_even
    (a : CliffordAlgebra.even (QuadraticForm.dualProd K U))
    {z : ExteriorFockSpace (K := K) (U := U)}
    (hz : z ∈ CliffordAlgebra.evenOdd
      (0 : QuadraticForm K U) 0) :
    exteriorCliffordAction (K := K) (U := U) a z ∈
      CliffordAlgebra.evenOdd (0 : QuadraticForm K U) 0 := by
  induction a.1, a.2 using
      CliffordAlgebra.even_induction
        (QuadraticForm.dualProd K U) with
  | algebraMap r =>
      rw [(exteriorCliffordAction (K := K) (U := U)).commutes r]
      change r • z ∈ CliffordAlgebra.evenOdd
        (0 : QuadraticForm K U) 0
      exact Submodule.smul_mem _ r hz
  | add x y hx hy ihx ihy =>
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
      rw [map_mul, map_mul, Module.End.mul_apply,
        Module.End.mul_apply, exteriorCliffordAction_ι,
        exteriorCliffordAction_ι]
      exact exteriorFockGenerator_mem_even_of_mem_odd m₁
        (exteriorFockGenerator_mem_odd_of_mem_even m₂ ih)

/-- The even hyperbolic Clifford algebra preserves odd exterior parity. -/
theorem exteriorCliffordAction_mem_odd
    (a : CliffordAlgebra.even (QuadraticForm.dualProd K U))
    {z : ExteriorFockSpace (K := K) (U := U)}
    (hz : z ∈ CliffordAlgebra.evenOdd
      (0 : QuadraticForm K U) 1) :
    exteriorCliffordAction (K := K) (U := U) a z ∈
      CliffordAlgebra.evenOdd (0 : QuadraticForm K U) 1 := by
  induction a.1, a.2 using
      CliffordAlgebra.even_induction
        (QuadraticForm.dualProd K U) with
  | algebraMap r =>
      rw [(exteriorCliffordAction (K := K) (U := U)).commutes r]
      change r • z ∈ CliffordAlgebra.evenOdd
        (0 : QuadraticForm K U) 1
      exact Submodule.smul_mem _ r hz
  | add x y hx hy ihx ihy =>
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
      rw [map_mul, map_mul, Module.End.mul_apply,
        Module.End.mul_apply, exteriorCliffordAction_ι,
        exteriorCliffordAction_ι]
      exact exteriorFockGenerator_mem_odd_of_mem_even m₁
        (exteriorFockGenerator_mem_even_of_mem_odd m₂ ih)

/-- The constructed action of the even Clifford algebra on even Fock
parity. -/
def exteriorFockEvenAction :
    CliffordAlgebra.even (QuadraticForm.dualProd K U) →ₐ[K]
      Module.End K (ExteriorFockEven (K := K) (U := U)) :=
  restrictAlgAction
    ((exteriorCliffordAction (K := K) (U := U)).comp
      (CliffordAlgebra.even (QuadraticForm.dualProd K U)).val)
    (CliffordAlgebra.evenOdd (0 : QuadraticForm K U) 0)
    (by
      intro a z hz
      exact exteriorCliffordAction_mem_even a hz)

/-- The constructed action of the even Clifford algebra on odd Fock
parity. -/
def exteriorFockOddAction :
    CliffordAlgebra.even (QuadraticForm.dualProd K U) →ₐ[K]
      Module.End K (ExteriorFockOdd (K := K) (U := U)) :=
  restrictAlgAction
    ((exteriorCliffordAction (K := K) (U := U)).comp
      (CliffordAlgebra.even (QuadraticForm.dualProd K U)).val)
    (CliffordAlgebra.evenOdd (0 : QuadraticForm K U) 1)
    (by
      intro a z hz
      exact exteriorCliffordAction_mem_odd a hz)

@[simp]
theorem coe_exteriorFockEvenAction_apply
    (a : CliffordAlgebra.even (QuadraticForm.dualProd K U))
    (z : ExteriorFockEven (K := K) (U := U)) :
    ((exteriorFockEvenAction (K := K) (U := U) a z :
        ExteriorFockEven (K := K) (U := U)) :
      ExteriorFockSpace (K := K) (U := U)) =
      exteriorCliffordAction (K := K) (U := U) a z :=
  rfl

@[simp]
theorem coe_exteriorFockOddAction_apply
    (a : CliffordAlgebra.even (QuadraticForm.dualProd K U))
    (z : ExteriorFockOdd (K := K) (U := U)) :
    ((exteriorFockOddAction (K := K) (U := U) a z :
        ExteriorFockOdd (K := K) (U := U)) :
      ExteriorFockSpace (K := K) (U := U)) =
      exteriorCliffordAction (K := K) (U := U) a z :=
  rfl

end Parity

end ExteriorFock

end RiemannResearch.LinearAlgebra.CliffordEven
