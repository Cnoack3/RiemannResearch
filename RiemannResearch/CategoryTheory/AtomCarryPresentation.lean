import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.BigOperators.Module

/-!
# Finite presentations and the atom/carry CRT

A finite presentation is a linear synthesis map from a finite-dimensional
coefficient space into a fixed vector space. Morphisms preserve the represented
vector. The intended RH application uses the spans of residue atoms and their
floor carries; no inner product or infinite convergence assertion is involved.

Source: user-provided categorical atom/carry CRT argument (2026-11-17).
The coefficient transformation is the transpose of the displayed generator
transformation: `(x,y) ↦ (x + U y, -y)`, where `U` synthesizes the prime-power
coefficients of the mixed-conductor generators.
-/

noncomputable section
open scoped BigOperators
open CategoryTheory

universe u v w
namespace RiemannResearch.CategoryTheory.AtomCarryPresentation

variable (R : Type u) [Field R] (H : Type v) [AddCommGroup H] [Module R H]

/-- A finite linear presentation of vectors in a fixed ambient space. -/
structure Presentation where
  Coeff : Type w
  [addCommGroup : AddCommGroup Coeff]
  [moduleStruct : Module R Coeff]
  [finite : Module.Finite R Coeff]
  synthesis : Coeff →ₗ[R] H

attribute [instance] Presentation.addCommGroup Presentation.moduleStruct Presentation.finite

variable {R H}

/-- Coordinate changes must preserve actual synthesis, including dependencies. -/
@[ext]
structure PresentationHom (X Y : Presentation.{u, v, w} R H) where
  map : X.Coeff →ₗ[R] Y.Coeff
  preserves : Y.synthesis.comp map = X.synthesis

instance : Category (Presentation.{u, v, w} R H) where
  Hom := PresentationHom
  id X := ⟨LinearMap.id, by ext x; rfl⟩
  comp f g := ⟨g.map.comp f.map, by
    ext x
    calc
      _ = _ := congrArg (fun L => L (f.map x)) g.preserves
      _ = _ := congrArg (fun L => L x) f.preserves⟩
  id_comp f := by ext x; rfl
  comp_id f := by ext x; rfl
  assoc f g h := by ext x; rfl

/-- Maps into an injective synthesis presentation are determined by their source synthesis. -/
theorem subsingleton_hom_of_injective (X Y : Presentation.{u, v, w} R H)
    (hY : Function.Injective Y.synthesis) : Subsingleton (X ⟶ Y) := by
  constructor
  intro f g
  apply PresentationHom.ext
  apply LinearMap.ext
  intro x
  apply hY
  exact (DFunLike.congr_fun f.preserves x).trans (DFunLike.congr_fun g.preserves x).symm

variable {P M : Type w}
variable [AddCommGroup P] [Module R P]
variable [AddCommGroup M] [Module R M]

/-- Bundle a finite-dimensional synthesis map as a presentation. -/
def ofSynthesis [Module.Finite R P] (S : P →ₗ[R] H) : Presentation.{u, v, w} R H where
  Coeff := P
  synthesis := S

/-- Any invertible coordinate change gives an isomorphism over the ambient space. -/
def coordinateIso [Module.Finite R P] [Module.Finite R M] (S : P →ₗ[R] H) (e : M ≃ₗ[R] P) :
    ofSynthesis (S.comp e.toLinearMap) ≅ ofSynthesis S where
  hom := ⟨e.toLinearMap, rfl⟩
  inv := ⟨e.symm.toLinearMap, by
    apply LinearMap.ext
    intro x
    change S (e (e.symm x)) = S x
    exact congrArg S (e.apply_symm_apply x)⟩
  hom_inv_id := by
    apply PresentationHom.ext
    apply LinearMap.ext
    intro x
    change e.symm (e x) = x
    exact e.symm_apply_apply x
  inv_hom_id := by
    apply PresentationHom.ext
    apply LinearMap.ext
    intro x
    change e (e.symm x) = x
    exact e.apply_symm_apply x

/-- The coefficient-side CRT involution. On generator columns the matrix is
`[[I,0],[Uᵀ,-I]]`; on coefficient columns it is `[[I,U],[0,-I]]`. -/
def crtEquiv (U : M →ₗ[R] P) : (P × M) ≃ₗ[R] (P × M) where
  toFun z := (z.1 + U z.2, -z.2)
  invFun z := (z.1 + U z.2, -z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' z z' := by ext <;> simp [add_assoc, add_left_comm, add_comm]
  map_smul' a z := by ext <;> simp [smul_add]

@[simp]
theorem crtEquiv_apply (U : M →ₗ[R] P) (z : P × M) :
    crtEquiv U z = (z.1 + U z.2, -z.2) := rfl

@[simp]
theorem crtEquiv_involutive (U : M →ₗ[R] P) (z : P × M) :
    crtEquiv U (crtEquiv U z) = z := by ext <;> simp

/-- Carry synthesis obtained from an exact finite CRT identity. -/
def carrySynthesis (prime : P →ₗ[R] H) (mixed : M →ₗ[R] H)
    (U : M →ₗ[R] P) : M →ₗ[R] H := prime.comp U - mixed

@[simp]
theorem carrySynthesis_apply (prime : P →ₗ[R] H) (mixed : M →ₗ[R] H)
    (U : M →ₗ[R] P) (y : M) :
    carrySynthesis prime mixed U y = prime (U y) - mixed y := rfl

/-- The exact synthesis identity underlying the categorical CRT. -/
theorem crt_synthesis (prime : P →ₗ[R] H) (mixed : M →ₗ[R] H)
    (U : M →ₗ[R] P) :
    (prime.coprod mixed).comp (crtEquiv U).toLinearMap =
      prime.coprod (carrySynthesis prime mixed U) := by
  apply LinearMap.ext
  intro z
  change prime (z.1 + U z.2) + mixed (-z.2) =
    prime z.1 + (prime (U z.2) - mixed z.2)
  simp [sub_eq_add_neg, add_assoc]

/-- Finite CRT is an isomorphism of presentations, not merely equality of spans. -/
def crtIso [Module.Finite R P] [Module.Finite R M] (prime : P →ₗ[R] H) (mixed : M →ₗ[R] H)
    (U : M →ₗ[R] P) :
    ofSynthesis (prime.coprod mixed) ≅
      ofSynthesis (prime.coprod (carrySynthesis prime mixed U)) where
  hom := ⟨(crtEquiv U).toLinearMap, by
    rw [← crt_synthesis]
    apply LinearMap.ext
    intro z
    change (prime.coprod mixed) (crtEquiv U (crtEquiv U z)) = (prime.coprod mixed) z
    exact congrArg (prime.coprod mixed) (crtEquiv_involutive U z)⟩
  inv := ⟨(crtEquiv U).toLinearMap, crt_synthesis prime mixed U⟩
  hom_inv_id := by
    apply PresentationHom.ext
    apply LinearMap.ext
    intro z
    change crtEquiv U (crtEquiv U z) = z
    exact crtEquiv_involutive U z
  inv_hom_id := by
    apply PresentationHom.ext
    apply LinearMap.ext
    intro z
    change crtEquiv U (crtEquiv U z) = z
    exact crtEquiv_involutive U z

/-- An invertible finite CRT transform preserves the full synthesis range. -/
theorem crt_range (prime : P →ₗ[R] H) (mixed : M →ₗ[R] H)
    (U : M →ₗ[R] P) :
    LinearMap.range (prime.coprod mixed) =
      LinearMap.range (prime.coprod (carrySynthesis prime mixed U)) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨crtEquiv U z, ?_⟩
    have h := congrArg (fun L => L (crtEquiv U z)) (crt_synthesis prime mixed U)
    simpa using h.symm
  · rintro ⟨z, rfl⟩
    refine ⟨crtEquiv U z, ?_⟩
    exact congrArg (fun L => L z) (crt_synthesis prime mixed U)

/-- Independence of the original synthesis is preserved by the CRT transform. -/
theorem crt_injective (prime : P →ₗ[R] H) (mixed : M →ₗ[R] H)
    (U : M →ₗ[R] P) (h : Function.Injective (prime.coprod mixed)) :
    Function.Injective (prime.coprod (carrySynthesis prime mixed U)) := by
  rw [← crt_synthesis]
  exact h.comp (crtEquiv U).injective

/-- Algebraic directness of prime-power and carry ranges. This does not assert
orthogonality in either of the physical Hilbert-space measures. -/
theorem crt_disjoint (prime : P →ₗ[R] H) (mixed : M →ₗ[R] H)
    (U : M →ₗ[R] P) (h : Function.Injective (prime.coprod mixed)) :
    Disjoint (LinearMap.range prime) (LinearMap.range (carrySynthesis prime mixed U)) := by
  rw [disjoint_iff]
  apply le_antisymm
  · intro z hz
    obtain ⟨x, hx⟩ := hz.1
    obtain ⟨y, hy⟩ := hz.2
    have heq : (prime.coprod (carrySynthesis prime mixed U)) (x, 0) =
        (prime.coprod (carrySynthesis prime mixed U)) (0, y) := by
      simpa using hx.trans hy.symm
    have hp := congrArg Prod.fst (crt_injective prime mixed U h heq)
    have hx0 : x = 0 := hp
    simp only [Submodule.mem_bot]
    rw [← hx, hx0, map_zero]
  · exact bot_le

/-- Coefficient-side transpose of a finite generator matrix. -/
def coefficientSynthesis {I J : Type w} [Fintype I] [Fintype J]
    (U : J → I → R) : (J → R) →ₗ[R] (I → R) where
  toFun b i := ∑ j, b j * U j i
  map_add' b c := by ext i; simp [add_mul, Finset.sum_add_distrib]
  map_smul' a b := by ext i; simp [Finset.mul_sum, mul_assoc]

/-- The abstract carry synthesis is exactly synthesis of the individual carries. -/
theorem family_carrySynthesis {I J : Type w} [Fintype I] [Fintype J]
    (prime : I → H) (mixed : J → H) (U : J → I → R) :
    carrySynthesis (Fintype.linearCombination R prime) (Fintype.linearCombination R mixed)
        (coefficientSynthesis U) =
      Fintype.linearCombination R (fun j => Fintype.linearCombination R prime (U j) - mixed j) := by
  apply LinearMap.ext
  intro b
  change (∑ i, (∑ j, b j * U j i) • prime i) - (∑ j, b j • mixed j) =
    ∑ j, b j • ((∑ i, U j i • prime i) - mixed j)
  simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

/-- Independence of a combined finite family gives injective pair synthesis. -/
theorem family_coprod_injective {I J : Type w} [Fintype I] [Fintype J]
    (prime : I → H) (mixed : J → H)
    (h : LinearIndependent R (Sum.elim prime mixed)) :
    Function.Injective ((Fintype.linearCombination R prime).coprod
      (Fintype.linearCombination R mixed)) := by
  intro x y hxy
  have heq : Sum.elim x.1 x.2 = Sum.elim y.1 y.2 := by
    apply h.fintypeLinearCombination_injective
    simpa [Fintype.sum_sum_type, Fintype.linearCombination_apply] using hxy
  apply Prod.ext
  · funext i
    exact congrFun heq (Sum.inl i)
  · funext j
    exact congrFun heq (Sum.inr j)

/-- The finite atom/carry CRT preserves the combined algebraic span. -/
theorem family_crt_span {I J : Type w} [Fintype I] [Fintype J]
    (prime : I → H) (mixed : J → H) (U : J → I → R) :
    Submodule.span R (Set.range prime) ⊔ Submodule.span R (Set.range mixed) =
      Submodule.span R (Set.range prime) ⊔
        Submodule.span R
          (Set.range (fun j => Fintype.linearCombination R prime (U j) - mixed j)) := by
  have h := crt_range (Fintype.linearCombination R prime) (Fintype.linearCombination R mixed)
    (coefficientSynthesis U)
  simpa only [family_carrySynthesis, LinearMap.range_coprod,
    Fintype.range_linearCombination] using h

/-- Prime-power generators and their canonical mixed carries form an algebraic
internal direct sum whenever the original combined atom family is independent. -/
theorem family_crt_disjoint {I J : Type w} [Fintype I] [Fintype J]
    (prime : I → H) (mixed : J → H) (U : J → I → R)
    (h : LinearIndependent R (Sum.elim prime mixed)) :
    Disjoint (Submodule.span R (Set.range prime))
      (Submodule.span R
        (Set.range (fun j => Fintype.linearCombination R prime (U j) - mixed j))) := by
  have hd := crt_disjoint (Fintype.linearCombination R prime) (Fintype.linearCombination R mixed)
    (coefficientSynthesis U) (family_coprod_injective prime mixed h)
  simpa only [family_carrySynthesis, Fintype.range_linearCombination] using hd

end RiemannResearch.CategoryTheory.AtomCarryPresentation
