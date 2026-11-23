import RiemannResearch.RH.ConductorTowerCompletions
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# Inverse limits of conductor residue rings

The cone over the nested residue rings has the historical ring of compatible
families as its vertex. Compatibility at all divisibility pairs follows from
compatibility along the ordered tower by evaluating at a common later stage.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open RiemannResearch.NumberTheory.GeneralizedCRT

namespace RiemannResearch.RH.ConductorTowerCompletions

/-- Reduction along a nested sequence of positive conductors. -/
def conductorTowerDiagram (m : ℕ → PositiveModulus)
    (hm : ∀ i j, i ≤ j → (m i).val ∣ (m j).val) : ℕᵒᵖ ⥤ CommRingCat where
  obj i := CommRingCat.of (ZMod (m i.unop).val)
  map f := CommRingCat.ofHom (ZMod.castHom (hm _ _ (leOfHom f.unop)) _)
  map_id _ := CommRingCat.hom_ext (RingHom.ext_zmod _ _)
  map_comp _ _ := CommRingCat.hom_ext (RingHom.ext_zmod _ _)

/-- A compatible family projects to its residue at each stage. -/
def conductorTowerCone (m : ℕ → PositiveModulus)
    (hm : ∀ i j, i ≤ j → (m i).val ∣ (m j).val) : Cone (conductorTowerDiagram m hm) where
  pt := CommRingCat.of (towerRing m)
  π := {
    app := fun i => CommRingCat.ofHom ((Pi.evalRingHom _ i.unop).comp (towerRing m).subtype)
    naturality := by
      intro i j f
      apply ConcreteCategory.hom_ext
      intro a
      exact (a.property j.unop i.unop (hm _ _ (leOfHom f.unop))).symm }

private theorem cone_reduction {m : ℕ → PositiveModulus}
    {hm : ∀ i j, i ≤ j → (m i).val ∣ (m j).val} (s : Cone (conductorTowerDiagram m hm))
    {i j : ℕ} (h : i ≤ j) (x : s.pt) :
    ZMod.castHom (hm _ _ h) (ZMod (m i).val) (s.π.app (Opposite.op j) x) =
      s.π.app (Opposite.op i) x :=
  ConcreteCategory.congr_hom (s.w ((homOfLE h).op)) x

/-- The ordered tower also determines the reductions at divisibility pairs
whose indices occur in the reverse order. -/
private theorem cone_compatible {m : ℕ → PositiveModulus}
    {hm : ∀ i j, i ≤ j → (m i).val ∣ (m j).val} (s : Cone (conductorTowerDiagram m hm))
    (x : s.pt) (i j : ℕ) (h : (m i).val ∣ (m j).val) :
    ZMod.castHom h (ZMod (m i).val) (s.π.app (Opposite.op j) x) = s.π.app (Opposite.op i) x := by
  let k := max i j
  have hi : i ≤ k := le_max_left _ _
  have hj : j ≤ k := le_max_right _ _
  have hcomp : (ZMod.castHom h (ZMod (m i).val)).comp
        (ZMod.castHom (hm j k hj) (ZMod (m j).val)) =
      ZMod.castHom (hm i k hi) (ZMod (m i).val) := RingHom.ext_zmod _ _
  rw [← cone_reduction s hj x]
  exact (DFunLike.congr_fun hcomp (s.π.app (Opposite.op k) x)).trans (cone_reduction s hi x)

/-- The mediating map assembles the legs of a cone into a compatible tuple. -/
private def conductorTowerLift {m : ℕ → PositiveModulus}
    {hm : ∀ i j, i ≤ j → (m i).val ∣ (m j).val} (s : Cone (conductorTowerDiagram m hm)) :
    s.pt ⟶ (conductorTowerCone m hm).pt := CommRingCat.ofHom {
  toFun x := ⟨fun i => s.π.app (Opposite.op i) x, cone_compatible s x⟩
  map_zero' := Subtype.ext (funext fun i => map_zero (s.π.app (Opposite.op i)).hom)
  map_one' := Subtype.ext (funext fun i => map_one (s.π.app (Opposite.op i)).hom)
  map_add' x y := Subtype.ext (funext fun i => map_add (s.π.app (Opposite.op i)).hom x y)
  map_mul' x y := Subtype.ext (funext fun i => map_mul (s.π.app (Opposite.op i)).hom x y) }

/-- The ring of compatible residues is the categorical inverse limit. -/
def conductorTowerIsLimit (m : ℕ → PositiveModulus)
    (hm : ∀ i j, i ≤ j → (m i).val ∣ (m j).val) : IsLimit (conductorTowerCone m hm) where
  lift := conductorTowerLift
  fac := by
    intro s j
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  uniq := by
    intro s f hf
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    funext i
    exact ConcreteCategory.congr_hom (hf (Opposite.op i)) x

/-- Every nested LCM sequence has this limiting cone. When the cutoffs are cofinal,
`lcmTowerPadicEquiv` identifies its vertex with the product of the p-adic integer rings. -/
def lcmConductorTowerIsLimit (M : ℕ → ℕ) (hM : Monotone M) :
    IsLimit (conductorTowerCone (lcmModulus M)
      (fun _ _ h => QFullDivisorProjection.lcmPeriod_nested (hM h))) :=
  conductorTowerIsLimit _ _

/-- Primorial conductors give a limiting cone on the ring identified with
the product of the residue fields by `primorialTowerEquiv`. -/
def primorialConductorTowerIsLimit :
    IsLimit (conductorTowerCone primorialModulus
      (fun _ _ h => Pareto.SquarefreeStageExhaustion.primorialPeriod_nested h)) :=
  conductorTowerIsLimit _ _

end RiemannResearch.RH.ConductorTowerCompletions
