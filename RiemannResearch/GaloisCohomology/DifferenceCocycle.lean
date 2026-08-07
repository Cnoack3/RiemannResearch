/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.NonabelianH1

/-!
# Difference cocycles for two group representations

For two homomorphisms into a coefficient group, with the source acting by
conjugation through the first homomorphism, their pointwise difference is a
nonabelian one-cocycle. Its class is neutral exactly when the homomorphisms are
conjugate. This is the formal cohomological argument used in the manuscript's
finite two-gauge countermodel.
-/

namespace RiemannResearch.GaloisCohomology

/-- The difference of two homomorphisms, viewed as a nonabelian cocycle for
the conjugation action through the first homomorphism. -/
def differenceCocycle
    {Γ A : Type*} [Group Γ] [Group A] [MulDistribMulAction Γ A]
    (ρX ρY : Γ →* A)
    (hact : ∀ (σ : Γ) (a : A),
      σ • a = ρX σ * a * (ρX σ)⁻¹) :
    NonabelianCocycle Γ A where
  toFun := fun σ => ρY σ * (ρX σ)⁻¹
  map_mul' := by
    intro σ τ
    rw [map_mul, map_mul, hact]
    simp [mul_assoc]

/-- The difference cocycle is a coboundary exactly when the two
homomorphisms are conjugate in the coefficient group. -/
theorem differenceCocycle_isCoboundary_iff
    {Γ A : Type*} [Group Γ] [Group A] [MulDistribMulAction Γ A]
    (ρX ρY : Γ →* A)
    (hact : ∀ (σ : Γ) (a : A),
      σ • a = ρX σ * a * (ρX σ)⁻¹) :
    (differenceCocycle ρX ρY hact).IsCoboundary ↔
      ∃ g : A, ∀ σ : Γ, ρY σ = g⁻¹ * ρX σ * g := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    intro σ
    have hσ := congrArg (fun a : NonabelianCocycle Γ A => a σ) hg
    dsimp [differenceCocycle, NonabelianCocycle.gauge,
      NonabelianCocycle.trivial] at hσ
    rw [hact] at hσ
    have hσ' := congrArg (fun a : A => a * ρX σ) hσ
    simpa [mul_assoc] using hσ'
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    ext σ
    dsimp [differenceCocycle, NonabelianCocycle.gauge,
      NonabelianCocycle.trivial]
    rw [hact, hg]
    simp [mul_assoc]

/-- The represented difference class is neutral exactly when the two
homomorphisms are conjugate. -/
theorem differenceCocycle_class_eq_neutral_iff
    {Γ A : Type*} [Group Γ] [Group A] [MulDistribMulAction Γ A]
    (ρX ρY : Γ →* A)
    (hact : ∀ (σ : Γ) (a : A),
      σ • a = ρX σ * a * (ρX σ)⁻¹) :
    NonabelianH1.classOf (differenceCocycle ρX ρY hact) =
        (NonabelianH1.neutral : NonabelianH1 Γ A) ↔
      ∃ g : A, ∀ σ : Γ, ρY σ = g⁻¹ * ρX σ * g := by
  rw [NonabelianH1.classOf_eq_neutral_iff_isCoboundary]
  exact differenceCocycle_isCoboundary_iff ρX ρY hact

/-- After restriction to a subgroup, the difference cocycle is a coboundary
exactly when the restricted homomorphisms are conjugate. -/
theorem restrict_differenceCocycle_isCoboundary_iff
    {Γ A : Type*} [Group Γ] [Group A] [MulDistribMulAction Γ A]
    (ρX ρY : Γ →* A)
    (hact : ∀ (σ : Γ) (a : A),
      σ • a = ρX σ * a * (ρX σ)⁻¹)
    (S : Subgroup Γ) :
    ((differenceCocycle ρX ρY hact).restrict S).IsCoboundary ↔
      ∃ g : A, ∀ σ : S, ρY σ = g⁻¹ * ρX σ * g := by
  let ρXS : S →* A := ρX.comp S.subtype
  let ρYS : S →* A := ρY.comp S.subtype
  have hactS : ∀ (σ : S) (a : A),
      σ • a = ρXS σ * a * (ρXS σ)⁻¹ := by
    intro σ a
    exact hact σ.1 a
  change (differenceCocycle ρXS ρYS hactS).IsCoboundary ↔
    ∃ g : A, ∀ σ : S, ρYS σ = g⁻¹ * ρXS σ * g
  exact differenceCocycle_isCoboundary_iff ρXS ρYS hactS


/-- Two local simultaneous conjugacies and the absence of a global
conjugacy produce an honest nonneutral nonabelian H¹ class whose two
restrictions are neutral.  This is the generic deduction used after the
finite A11 Burnside certificate in PDF Proposition 6.26. -/
theorem differenceCocycle_twoGaugeCounterexample
    {Γ A : Type*} [Group Γ] [Group A] [MulDistribMulAction Γ A]
    (ρX ρY : Γ →* A)
    (hact : ∀ (σ : Γ) (a : A),
      σ • a = ρX σ * a * (ρX σ)⁻¹)
    (S T : Subgroup Γ)
    (not_global : ¬ ∃ g : A, ∀ σ : Γ,
      ρY σ = g⁻¹ * ρX σ * g)
    (localS : ∃ g : A, ∀ σ : S,
      ρY σ = g⁻¹ * ρX σ * g)
    (localT : ∃ g : A, ∀ σ : T,
      ρY σ = g⁻¹ * ρX σ * g) :
    NonabelianH1.classOf (differenceCocycle ρX ρY hact) ≠
        (NonabelianH1.neutral : NonabelianH1 Γ A) ∧
      NonabelianH1.restrict S
          (NonabelianH1.classOf (differenceCocycle ρX ρY hact)) =
        (NonabelianH1.neutral : NonabelianH1 S A) ∧
      NonabelianH1.restrict T
          (NonabelianH1.classOf (differenceCocycle ρX ρY hact)) =
        (NonabelianH1.neutral : NonabelianH1 T A) := by
  constructor
  · intro hneutral
    exact not_global
      ((differenceCocycle_class_eq_neutral_iff ρX ρY hact).1 hneutral)
  constructor
  · rw [NonabelianH1.restrict_classOf,
      NonabelianH1.classOf_eq_neutral_iff_isCoboundary,
      restrict_differenceCocycle_isCoboundary_iff]
    exact localS
  · rw [NonabelianH1.restrict_classOf,
      NonabelianH1.classOf_eq_neutral_iff_isCoboundary,
      restrict_differenceCocycle_isCoboundary_iff]
    exact localT

end RiemannResearch.GaloisCohomology
