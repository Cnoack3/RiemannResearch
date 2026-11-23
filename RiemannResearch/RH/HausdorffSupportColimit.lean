import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Limits.IsLimit
import RiemannResearch.RH.PrimeSupportParityDescent

/-!
# The Hausdorff colimit of the ambient prime-support quotients

At each stage the denominator is closed, so each quotient defines a Hausdorff
topological real module. The continuous descent theorem identifies the colimit
of this diagram in the full subcategory of Hausdorff modules with the ambient
quotient by the closed mixed space.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis

open CoefficientStabilization

/-- Hausdorffness as an object property of real topological modules. -/
abbrev hausdorffTopModule : ObjectProperty (TopModuleCat.{0} ℝ) :=
  fun X => T2Space X

/-- Each support denominator is closed also in the ambient Hilbert space. -/
theorem ambientSupport_isClosed (n : ℕ) : IsClosed (ambientSupport n : Set ThresholdHilbert) := by
  have hM : IsClosed (mixedClosure : Set ThresholdHilbert) := isClosed_closure
  have hS : IsClosed (supportSpace n : Set mixedClosure) := isClosed_closure
  exact hM.isClosedMap_subtype_val _ hS

/-- The ambient prime-support diagram with its Hausdorff structures. -/
def hausdorffSupportTower : ℕ ⥤ hausdorffTopModule.FullSubcategory :=
  hausdorffTopModule.lift
    (supportQuotientFunctor ambientSupport (fun _ _ h => Submodule.map_mono (supportSpace_mono h)))
    (fun n => by
      let : IsClosed (ambientSupport n : Set ThresholdHilbert) := ambientSupport_isClosed n
      change T2Space (ThresholdHilbert ⧸ ambientSupport n)
      infer_instance)

/-- The cocone whose vertex is the Hausdorff quotient by the mixed closure. -/
def hausdorffSupportCocone : Cocone hausdorffSupportTower where
  pt := ⟨supportQuotientCocone.pt, by
    let : IsClosed (mixedClosure : Set ThresholdHilbert) := isClosed_closure
    change T2Space (ThresholdHilbert ⧸ mixedClosure)
    infer_instance⟩
  ι :=
    { app := fun n => ObjectProperty.homMk (supportQuotientCocone.ι.app n)
      naturality := by
        intro i j f
        apply hausdorffTopModule.ι.map_injective
        exact supportQuotientCocone.ι.naturality f }

/-- The continuous factorization through the mixed quotient is the categorical colimit
in Hausdorff real topological modules. -/
def hausdorffSupportIsColimit : IsColimit hausdorffSupportCocone := by
  apply IsColimit.ofExistsUnique
  intro s
  let : T2Space s.pt.obj := s.pt.property
  let t (n : ℕ) : (ThresholdHilbert ⧸ ambientSupport n) →L[ℝ] s.pt.obj :=
    (s.ι.app n).hom.hom
  have ht (n : ℕ) (x : ThresholdHilbert) :
      t n ((ambientSupport n).mkQ x) = t 0 ((ambientSupport 0).mkQ x) := by
    exact congrArg (fun f : hausdorffSupportTower.obj 0 ⟶ s.pt =>
      f.hom.hom ((ambientSupport 0).mkQ x)) (s.w (homOfLE (Nat.zero_le n)))
  obtain ⟨f, hf, hu⟩ := supportQuotient_hausdorff_desc t ht
  refine ⟨ObjectProperty.homMk (TopModuleCat.ofHom f), ?_, ?_⟩
  · intro n
    apply hausdorffTopModule.ι.map_injective
    apply ConcreteCategory.hom_ext
    intro q
    obtain ⟨x, rfl⟩ := (ambientSupport n).mkQ_surjective q
    exact hf n x
  · intro m hm
    apply hausdorffTopModule.ι.map_injective
    apply ConcreteCategory.ext
    apply hu m.hom.hom
    intro n x
    exact congrArg (fun g : hausdorffSupportTower.obj n ⟶ s.pt =>
      g.hom.hom ((ambientSupport n).mkQ x)) (hm n)

end RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis
