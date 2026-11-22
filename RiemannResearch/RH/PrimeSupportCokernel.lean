import RiemannResearch.RH.MixedConductorPrimeSupport
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Cokernels of the prime-support stages in the ambient Pareto space

The inclusions of the support stages induce continuous maps of ambient quotients.
The quotient by the full mixed closure receives a cocone from this diagram.
Its value on a class is computed using the same ambient representative at every stage.

For diagrams and cocones see E. Riehl, *Category Theory in Context*, Chapter 3.
-/

noncomputable section

open CategoryTheory Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis

open CoefficientStabilization

/-- The closed support stage in the ambient Hilbert space, via the inclusion of the mixed space. -/
abbrev ambientSupport (n : ℕ) : Submodule ℝ ThresholdHilbert :=
  (supportSpace n).map mixedClosure.subtype

section Quotients

variable {E : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The continuous quotient transition for an inclusion of denominators. -/
def supportQuotientTransition {A B : Submodule ℝ E} (h : A ≤ B) :
    (E ⧸ A) →L[ℝ] (E ⧸ B) :=
  A.liftQL B.mkQL fun _ hx => (Submodule.Quotient.mk_eq_zero B).mpr (h hx)

/-- Ambient quotients of an increasing sequence form a diagram in real topological modules. -/
def supportQuotientFunctor (S : ℕ → Submodule ℝ E) (hS : Monotone S) :
    ℕ ⥤ TopModuleCat ℝ where
  obj n := TopModuleCat.of ℝ (E ⧸ S n)
  map f := TopModuleCat.ofHom (supportQuotientTransition (hS (leOfHom f)))
  map_id i := by
    apply ConcreteCategory.hom_ext
    intro q
    obtain ⟨x, rfl⟩ := (S i).mkQ_surjective q
    rfl
  map_comp {i j k} f g := by
    apply ConcreteCategory.hom_ext
    intro q
    obtain ⟨x, rfl⟩ := (S i).mkQ_surjective q
    rfl

end Quotients

/-- The continuous quotient maps from all prime-support stages to the full mixed quotient. -/
def supportQuotientCocone :
    Limits.Cocone (supportQuotientFunctor ambientSupport
      (fun _ _ h => Submodule.map_mono (supportSpace_mono h))) := by
  let build (E : Type) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
      [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] (S : ℕ → Submodule ℝ E)
      (mono : Monotone S) (M : Submodule ℝ E) (hM : ∀ n, S n ≤ M) :
      Limits.Cocone (supportQuotientFunctor S mono) := {
    pt := TopModuleCat.of ℝ (E ⧸ M)
    ι := {
      app := fun n => TopModuleCat.ofHom (supportQuotientTransition (hM n))
      naturality := by
        intro i j f
        apply ConcreteCategory.hom_ext
        intro q
        obtain ⟨x, rfl⟩ := (S i).mkQ_surjective q
        rfl } }
  exact build ThresholdHilbert ambientSupport
    (fun _ _ h => Submodule.map_mono (supportSpace_mono h)) mixedClosure
    (by rintro _ _ ⟨m, _, rfl⟩; exact m.property)

end RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis
