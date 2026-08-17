/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.LinearAlgebra.RootSystem.D4ZornPointFunctor

/-!
# Semilinear descent data for split-Zorn related triples

The universal split-Zorn related-triple group is functorial under arbitrary
commutative-ring morphisms, and scalar extension commutes with its corrected
S₃ diagram action. Consequently a group acting on the coefficient ring,
together with a homomorphism to the D4 diagram group, acts semilinearly on
related triples.

For an extension `L/K`, this construction applies to the group of
`K`-algebra automorphisms of `L`. In the finite Galois case, diagram maps
with cyclic image of order three and with full S₃ image give the pointwise
descent data relevant to the trialitarian forms `³D₄` and `⁶D₄`,
respectively.

The fixed subgroup is constructed explicitly. This is a pointwise descent
statement; no representability of that fixed subgroup and no effective
descent of the coordinate Hopf algebra are asserted here.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn

universe u v w

noncomputable section

/-- Scalar extension along a ring equivalence is an equivalence of universal
related-triple groups. -/
def universalRelatedTripleBaseChangeEquiv
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    universalRelatedTripleGroup R ≃*
      universalRelatedTripleGroup S where
  toFun := universalRelatedTripleBaseChange e.toRingHom
  invFun := universalRelatedTripleBaseChange e.symm.toRingHom
  left_inv g := by
    change ((universalRelatedTripleBaseChange e.symm.toRingHom).comp
        (universalRelatedTripleBaseChange e.toRingHom)) g = g
    rw [← universalRelatedTripleBaseChange_comp]
    simpa using DFunLike.congr_fun universalRelatedTripleBaseChange_id g
  right_inv g := by
    change ((universalRelatedTripleBaseChange e.toRingHom).comp
        (universalRelatedTripleBaseChange e.symm.toRingHom)) g = g
    rw [← universalRelatedTripleBaseChange_comp]
    simpa using DFunLike.congr_fun universalRelatedTripleBaseChange_id g
  map_mul' g h :=
    (universalRelatedTripleBaseChange e.toRingHom).map_mul g h

@[simp] theorem universalRelatedTripleBaseChangeEquiv_apply
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (g : universalRelatedTripleGroup R) :
    universalRelatedTripleBaseChangeEquiv e g =
      universalRelatedTripleBaseChange e.toRingHom g :=
  rfl

/-- Ring automorphisms act on universal related triples by scalar extension. -/
def universalRelatedTripleScalarAction
    (R : Type u) [CommRing R] :
    (R ≃+* R) →* MulAut (universalRelatedTripleGroup R) where
  toFun e := universalRelatedTripleBaseChangeEquiv e
  map_one' := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    exact matrixTupleMap_id g.1
  map_mul' e f := by
    apply MulEquiv.ext
    intro g
    change universalRelatedTripleBaseChange (e * f).toRingHom g =
      ((universalRelatedTripleBaseChange e.toRingHom).comp
        (universalRelatedTripleBaseChange f.toRingHom)) g
    rw [← universalRelatedTripleBaseChange_comp]
    have h : (e * f).toRingHom =
        e.toRingHom.comp f.toRingHom := by
      ext x
      exact RingAut.mul_apply e f x
    rw [h]

/-- Coefficient automorphisms commute with the integral D4 diagram action. -/
theorem universalRelatedTripleScalarAction_commute_outer
    (R : Type u) [CommRing R] (e : R ≃+* R)
    (σ : DiagramSymmetry) :
    Commute (universalRelatedTripleScalarAction R e)
      (universalRelatedTripleOuterAction R σ) := by
  apply MulEquiv.ext
  intro g
  exact universalRelatedTripleBaseChange_relabel e.toRingHom σ g

/-- The semilinear action obtained by combining coefficient automorphisms with
an S₃-valued diagram cocycle. -/
def universalRelatedTripleSemilinearAction
    {Γ : Type v} [Group Γ] (R : Type u) [CommRing R]
    (scalar : Γ →* (R ≃+* R))
    (diagram : Γ →* DiagramSymmetry) :
    Γ →* MulAut (universalRelatedTripleGroup R) where
  toFun γ :=
    universalRelatedTripleOuterAction R (diagram γ) *
      universalRelatedTripleScalarAction R (scalar γ)
  map_one' := by
    have hd : diagram 1 = 1 := diagram.map_one
    have hs : scalar 1 = 1 := scalar.map_one
    calc
      universalRelatedTripleOuterAction R (diagram 1) *
          universalRelatedTripleScalarAction R (scalar 1)
        = universalRelatedTripleOuterAction R 1 *
            universalRelatedTripleScalarAction R 1 := by rw [hd, hs]
      _ = 1 * 1 := congrArg₂ (· * ·)
        (universalRelatedTripleOuterAction R).map_one
        (universalRelatedTripleScalarAction R).map_one
      _ = 1 := one_mul 1
  map_mul' γ δ := by
    have hd : diagram (γ * δ) = diagram γ * diagram δ :=
      diagram.map_mul γ δ
    have hs : scalar (γ * δ) = scalar γ * scalar δ :=
      scalar.map_mul γ δ
    rw [hd, hs, (universalRelatedTripleOuterAction R).map_mul,
      (universalRelatedTripleScalarAction R).map_mul]
    let Aγ := universalRelatedTripleOuterAction R (diagram γ)
    let Aδ := universalRelatedTripleOuterAction R (diagram δ)
    let Bγ := universalRelatedTripleScalarAction R (scalar γ)
    let Bδ := universalRelatedTripleScalarAction R (scalar δ)
    change (Aγ * Aδ) * (Bγ * Bδ) =
      (Aγ * Bγ) * (Aδ * Bδ)
    calc
      (Aγ * Aδ) * (Bγ * Bδ) = Aγ * (Aδ * Bγ) * Bδ := by
        simp only [mul_assoc]
      _ = Aγ * (Bγ * Aδ) * Bδ := by
        rw [(universalRelatedTripleScalarAction_commute_outer
          R (scalar γ) (diagram δ)).eq]
      _ = (Aγ * Bγ) * (Aδ * Bδ) := by
        simp only [mul_assoc]

@[simp] theorem universalRelatedTripleSemilinearAction_apply
    {Γ : Type v} [Group Γ] (R : Type u) [CommRing R]
    (scalar : Γ →* (R ≃+* R))
    (diagram : Γ →* DiagramSymmetry)
    (γ : Γ) (g : universalRelatedTripleGroup R) :
    universalRelatedTripleSemilinearAction R scalar diagram γ g =
      universalRelatedTripleOuterAction R (diagram γ)
        (universalRelatedTripleBaseChange
          (scalar γ).toRingHom g) :=
  rfl

/-- The fixed subgroup of a semilinear, diagram-twisted related-triple action.

For a Galois action and an S₃-valued diagram map this is the pointwise
descended candidate. Representability and effective Hopf descent are separate
questions. -/
def universalRelatedTripleSemilinearFixedSubgroup
    {Γ : Type v} [Group Γ] (R : Type u) [CommRing R]
    (scalar : Γ →* (R ≃+* R))
    (diagram : Γ →* DiagramSymmetry) :
    Subgroup (universalRelatedTripleGroup R) where
  carrier := {g | ∀ γ,
    universalRelatedTripleSemilinearAction R scalar diagram γ g = g}
  one_mem' γ :=
    (universalRelatedTripleSemilinearAction R scalar diagram γ).map_one
  mul_mem' {g h} hg hh γ := by
    rw [(universalRelatedTripleSemilinearAction R scalar diagram γ).map_mul,
      hg γ, hh γ]
  inv_mem' {g} hg γ := by
    rw [(universalRelatedTripleSemilinearAction R scalar diagram γ).map_inv,
      hg γ]

@[simp] theorem mem_universalRelatedTripleSemilinearFixedSubgroup
    {Γ : Type v} [Group Γ] (R : Type u) [CommRing R]
    (scalar : Γ →* (R ≃+* R))
    (diagram : Γ →* DiagramSymmetry)
    (g : universalRelatedTripleGroup R) :
    g ∈ universalRelatedTripleSemilinearFixedSubgroup R scalar diagram ↔
      ∀ γ, universalRelatedTripleOuterAction R (diagram γ)
        (universalRelatedTripleBaseChange (scalar γ).toRingHom g) = g := by
  rfl

/-- Forgetting algebra structure sends algebra automorphisms to ring
automorphisms. -/
def relatedTripleAlgebraAutToRingAut
    (K : Type w) (L : Type u) [CommSemiring K] [CommSemiring L]
    [Algebra K L] :
    (L ≃ₐ[K] L) →* (L ≃+* L) where
  toFun σ := σ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The twisted semilinear action for the full group of `K`-algebra
automorphisms of `L`. In the finite Galois case this is the usual Galois
group. -/
def universalRelatedTripleAlgebraAutSemilinearAction
    (K : Type w) (L : Type u) [CommRing K] [CommRing L]
    [Algebra K L]
    (diagram : (L ≃ₐ[K] L) →* DiagramSymmetry) :
    (L ≃ₐ[K] L) →* MulAut (universalRelatedTripleGroup L) :=
  universalRelatedTripleSemilinearAction L
    (relatedTripleAlgebraAutToRingAut K L) diagram

end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality.Zorn
