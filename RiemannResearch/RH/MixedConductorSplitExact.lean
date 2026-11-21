import RiemannResearch.RH.MixedConductorRankOne
import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# The split exact sequence of the Pareto legal mean

The mixed inclusion and the legal mean form a split short exact sequence in
`TopModuleCat ℝ`. The screened section determines its retraction and its
biproduct coordinates. The quotient carries its usual quotient topology.

The concrete mean, kernel, and section are from `MixedConductorRankOne`.
The categorical constructions use mathlib's `ShortComplex.Splitting`.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- The inclusion of the mixed closure into the legal closure. -/
def legalMixedInclusion : mixedClosure →L[ℝ] closedSpace :=
  mixedClosure.subtypeL.codRestrict closedSpace (fun m => mixedClosure_le_closedSpace m.property)

@[simp] theorem legalPacketMean_legalMixedInclusion (m : mixedClosure) :
    legalPacketMean (legalMixedInclusion m) = 0 :=
  ((mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mp m.property).2

@[simp] theorem legalPacketMean_screenedMeanSection (a : ℝ) :
    legalPacketMean (screenedMeanSection a) = a :=
  DFunLike.congr_fun legalPacketMean_comp_screenedMeanSection a

/-- The mixed component of a legal vector `x` is `x - s (C x)`. -/
def legalMixedRetraction : closedSpace →L[ℝ] mixedClosure :=
  (closedSpace.subtypeL.comp
    (ContinuousLinearMap.id ℝ closedSpace - screenedMeanSection.comp legalPacketMean)).codRestrict
      mixedClosure (fun x => by
        apply (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mpr
        refine ⟨(x - screenedMeanSection (legalPacketMean x)).property, ?_⟩
        change legalPacketMean (x - screenedMeanSection (legalPacketMean x)) = 0
        rw [map_sub, legalPacketMean_screenedMeanSection, sub_self])

@[simp] theorem legalMixedInclusion_legalMixedRetraction (x : closedSpace) :
    legalMixedInclusion (legalMixedRetraction x) = x - screenedMeanSection (legalPacketMean x) :=
  rfl

/-- The mixed inclusion followed by the legal mean, as a short complex. -/
def legalMeanComplex : ShortComplex (TopModuleCat ℝ) :=
  ShortComplex.mk (TopModuleCat.ofHom legalMixedInclusion) (TopModuleCat.ofHom legalPacketMean)
    (by
      apply ConcreteCategory.hom_ext
      intro m
      exact legalPacketMean_legalMixedInclusion m)

/-- The screened section and mixed retraction split the mean sequence continuously. -/
def legalMeanSplitting : legalMeanComplex.Splitting where
  r := TopModuleCat.ofHom legalMixedRetraction
  s := TopModuleCat.ofHom screenedMeanSection
  f_r := by
    apply ConcreteCategory.hom_ext
    intro m
    change mixedClosure at m
    apply Subtype.ext
    change ((legalMixedInclusion m : closedSpace) : ThresholdHilbert) -
      (screenedMeanSection (legalPacketMean (legalMixedInclusion m)) : ThresholdHilbert) = _
    rw [legalPacketMean_legalMixedInclusion, map_zero]
    exact sub_zero _
  s_g := by
    apply ConcreteCategory.hom_ext
    intro a
    exact legalPacketMean_screenedMeanSection a
  id := by
    apply ConcreteCategory.hom_ext
    intro x
    change closedSpace at x
    change (x - screenedMeanSection (legalPacketMean x)) + screenedMeanSection (legalPacketMean x) = x
    exact sub_add_cancel _ _

instance legalMixedInclusion_isSplitMono : IsSplitMono (TopModuleCat.ofHom legalMixedInclusion) :=
  legalMeanSplitting.isSplitMono_f

instance legalPacketMean_isSplitEpi : IsSplitEpi (TopModuleCat.ofHom legalPacketMean) :=
  legalMeanSplitting.isSplitEpi_g

/-- Every continuous lift of a map to the scalar line has a unique mixed summand. -/
theorem legalMean_unique_mixed_lift {X : TopModuleCat.{0} ℝ}
    (f : X ⟶ legalMeanComplex.X₃) (v : X ⟶ legalMeanComplex.X₂)
    (hv : v ≫ legalMeanComplex.g = f) :
    ∃! m : X ⟶ legalMeanComplex.X₁,
      v = m ≫ legalMeanComplex.f + f ≫ legalMeanSplitting.s := by
  refine ⟨v ≫ legalMeanSplitting.r, ?_, ?_⟩
  · calc
      v = v ≫ 𝟙 _ := (Category.comp_id v).symm
      _ = v ≫ (legalMeanSplitting.r ≫ legalMeanComplex.f +
          legalMeanComplex.g ≫ legalMeanSplitting.s) := by rw [legalMeanSplitting.id]
      _ = _ := by rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, hv]
  · intro m hm
    rw [hm, Preadditive.add_comp, Category.assoc, legalMeanSplitting.f_r, Category.comp_id,
      Category.assoc, legalMeanSplitting.s_r, comp_zero, add_zero]

local instance : HasZeroObject (TopModuleCat.{0} ℝ) :=
  ⟨⟨_, (terminalIsTerminal (C := TopModuleCat.{0} ℝ)).isZero⟩⟩

local instance : HasBinaryBiproducts (TopModuleCat.{0} ℝ) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- The continuous Pareto sequence is short exact. -/
theorem legalMean_shortExact : legalMeanComplex.ShortExact :=
  legalMeanSplitting.shortExact

/-- The mixed inclusion exhibits the categorical kernel of the legal mean. -/
def legalMixedIsKernel : IsLimit (KernelFork.ofι legalMeanComplex.f legalMeanComplex.zero) :=
  legalMeanSplitting.fIsKernel

/-- The legal mean exhibits the categorical cokernel of the mixed inclusion. -/
def legalMeanIsCokernel : IsColimit (CokernelCofork.ofπ legalMeanComplex.g legalMeanComplex.zero) :=
  legalMeanSplitting.gIsCokernel

/-- The legal space in the screened coordinates determined by the splitting. -/
def legalMixedBiprodIso :
    TopModuleCat.of ℝ closedSpace ≅ TopModuleCat.of ℝ mixedClosure ⊞ TopModuleCat.of ℝ ℝ :=
  legalMeanSplitting.isoBinaryBiproduct

/-- The usual topological quotient of the legal space by the mixed inclusion is the scalar line. -/
def legalMixedQuotientIso : TopModuleCat.coker legalMeanComplex.f ≅ TopModuleCat.of ℝ ℝ :=
  (TopModuleCat.isColimitCoker legalMeanComplex.f).coconePointUniqueUpToIso legalMeanIsCokernel

/-- Under the quotient isomorphism, the usual quotient projection becomes the legal mean. -/
@[simp, reassoc] theorem legalMixedQuotientIso_π :
    TopModuleCat.cokerπ legalMeanComplex.f ≫ legalMixedQuotientIso.hom = legalMeanComplex.g :=
  (TopModuleCat.isColimitCoker legalMeanComplex.f).comp_coconePointUniqueUpToIso_hom
    legalMeanIsCokernel WalkingParallelPair.one

end RiemannResearch.RH.Pareto.PrimePowerSchur
