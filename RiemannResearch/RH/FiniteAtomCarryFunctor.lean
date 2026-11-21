import RiemannResearch.RH.FiniteAtomCarryRefinement
import RiemannResearch.CategoryTheory.AtomCarryPresentation
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.NatIso

/-!
# The atom and carry presentation functors

A positive period indexes its finite presentation of sequences on the natural
numbers. Divisibility maps extend both coefficient blocks by zero. The concrete
CRT change of coordinates is a natural isomorphism between the atom and carry
presentations over this entire diagram.
-/

noncomputable section
open CategoryTheory
namespace RiemannResearch.RH.FiniteAtomCarryCRT
open RiemannResearch.CategoryTheory.AtomCarryPresentation

/-- Positive periods ordered by divisibility. -/
structure ConductorStage where
  period : ℕ+

instance : Preorder ConductorStage where
  le X Y := (X.period : ℕ) ∣ (Y.period : ℕ)
  le_refl _ := dvd_refl _
  le_trans _ _ _ := dvd_trans

private abbrev stagePresentation (L : ℕ+) (b : MixedIndex L → ℕ → ℝ) :
    Presentation.{0, 0, 0} ℝ (ℕ → ℝ) :=
  ofSynthesis ((Fintype.linearCombination ℝ (primeAtom L)).coprod
    (Fintype.linearCombination ℝ b))

private def presentationFunctor
    (b : (L : ℕ+) → MixedIndex L → ℕ → ℝ)
    (hb : ∀ {L M : ℕ+} (h : (L : ℕ) ∣ (M : ℕ)) (j : MixedIndex L),
      b M (mixedEmbedding h j) = b L j)
    (hUnique : ∀ L (X : Presentation.{0, 0, 0} ℝ (ℕ → ℝ)),
      Subsingleton (X ⟶ stagePresentation L (b L))) :
    ConductorStage ⥤ Presentation.{0, 0, 0} ℝ (ℕ → ℝ) where
  obj X := stagePresentation X.period (b X.period)
  map {X Y} f := ⟨refineCoefficientsLinear (leOfHom f), by
    apply LinearMap.ext
    intro x
    exact stageSynthesis_refine (leOfHom f) _ _ (hb (leOfHom f)) x⟩
  map_id X := (hUnique X.period _).elim _ _
  map_comp {X Y Z} f g := (hUnique Z.period _).elim _ _

private theorem homToAtom (L : ℕ+) (X : Presentation.{0, 0, 0} ℝ (ℕ → ℝ)) :
    Subsingleton (X ⟶ stagePresentation L (mixedAtom L)) :=
  subsingleton_hom_of_injective _ _ (family_coprod_injective _ _ (combined_atoms_independent L))

private theorem homToCarry (L : ℕ+) (X : Presentation.{0, 0, 0} ℝ (ℕ → ℝ)) :
    Subsingleton (X ⟶ stagePresentation L (carryVector L)) :=
  ⟨fun f g => (cancel_mono (presentationIso L).inv).mp ((homToAtom L X).elim _ _)⟩

/-- The atom presentations and their zero-extension morphisms. -/
def atomPresentationFunctor : ConductorStage ⥤ Presentation.{0, 0, 0} ℝ (ℕ → ℝ) :=
  presentationFunctor (fun L => mixedAtom L) (fun _ _ => rfl) homToAtom

/-- The canonical floor-carry presentations and their zero-extension morphisms. -/
def carryPresentationFunctor : ConductorStage ⥤ Presentation.{0, 0, 0} ℝ (ℕ → ℝ) :=
  presentationFunctor (fun L => carryVector L) (fun _ _ => rfl) homToCarry

@[simp] theorem atomPresentationFunctor_map_apply {X Y : ConductorStage} (f : X ⟶ Y)
    (x : StageCoefficients X.period) :
    (atomPresentationFunctor.map f).map x = refineCoefficients (leOfHom f) x := rfl

@[simp] theorem carryPresentationFunctor_map_apply {X Y : ConductorStage} (f : X ⟶ Y)
    (x : StageCoefficients X.period) :
    (carryPresentationFunctor.map f).map x = refineCoefficients (leOfHom f) x := rfl

/-- The CRT coordinate isomorphisms commute with every conductor refinement. -/
def atomCarryRefinementIso : atomPresentationFunctor ≅ carryPresentationFunctor :=
  NatIso.ofComponents (fun X => presentationIso X.period)
    (fun {X Y} _ => (homToCarry Y.period _).elim _ _)

@[simp] theorem atomCarryRefinementIso_app (X : ConductorStage) :
    atomCarryRefinementIso.app X = presentationIso X.period := rfl

end RiemannResearch.RH.FiniteAtomCarryCRT
