import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.SnakeLemma
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Topology.Algebra.Module.Basic
import RiemannResearch.RH.CenteredMeanLongExact
import RiemannResearch.RH.CenteredMeanSnake
import RiemannResearch.RH.MixedConductorPrimeSupport
import RiemannResearch.RH.PrimeSupportAlgebraDescent

/-!
# The centered snake after quotienting both rows

For any submodule `S` of the mixed space, quotient the legal and ambient mean
sequences by its images. The middle vertical map is still centering. The actual
connecting map of these new rows takes values in `(Z/S)/(M/S)`, where `Z` is
the ambient mean kernel. The third isomorphism theorem identifies this map
with the original boundary. The stage transitions commute with the connecting
maps on every scalar. The comparison with the ambient sequence includes its
kernel, its middle cokernel, and all four interior arrows.

The sign and exactness conventions are those of the module snake lemma,
Stacks Project, Tag 07JV (https://stacks.math.columbia.edu/tag/07JV).
-/

noncomputable section

open CategoryTheory

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.Stage
open CoefficientStabilization MixedConductorBasis

variable (S : Submodule ℝ mixedClosure)

abbrev legalDen := S.map legalMixedInclusion.toLinearMap
abbrev zeroDen := S.map mixedInclusion.toLinearMap
abbrev ambientDen := S.map mixedClosure.subtype

/-- The remaining part of the mixed space inside the stage's mean kernel. -/
abbrev mixedImage := mixedInMeanZero.map (zeroDen S).mkQ
abbrev Target := (meanZero ⧸ zeroDen S) ⧸ mixedImage S

def upperInclusion : (mixedClosure ⧸ S) →ₗ[ℝ] (closedSpace ⧸ legalDen S) :=
  S.mapQ (legalDen S) legalMixedInclusion.toLinearMap (fun m hm => ⟨m, hm, rfl⟩)

def upperMean : (closedSpace ⧸ legalDen S) →ₗ[ℝ] ℝ :=
  (legalDen S).liftQ legalPacketMean.toLinearMap (by
    rintro _ ⟨m, _, rfl⟩
    exact legalPacketMean_legalMixedInclusion m)

def lowerInclusion : (meanZero ⧸ zeroDen S) →ₗ[ℝ] (ThresholdHilbert ⧸ ambientDen S) :=
  (zeroDen S).mapQ (ambientDen S) meanZero.subtype (by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, hm, rfl⟩)

def lowerMean : (ThresholdHilbert ⧸ ambientDen S) →ₗ[ℝ] ℝ :=
  (ambientDen S).liftQ hilbertMeanContinuous.toLinearMap (by
    rintro _ ⟨m, _, rfl⟩
    exact (mixedInclusion m).property)

def leftVertical : (mixedClosure ⧸ S) →ₗ[ℝ] (meanZero ⧸ zeroDen S) :=
  S.mapQ (zeroDen S) mixedInclusion.toLinearMap (fun m hm => ⟨m, hm, rfl⟩)

def middleVertical :
    (closedSpace ⧸ legalDen S) →ₗ[ℝ] (ThresholdHilbert ⧸ ambientDen S) :=
  (legalDen S).mapQ (ambientDen S) centerLegal.toLinearMap (by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, hm, DFunLike.congr_fun left_square m⟩)

theorem upper_exact : Function.Exact (upperInclusion S) (upperMean S) := by
  intro q
  obtain ⟨v, rfl⟩ := (legalDen S).mkQ_surjective q
  constructor
  · intro h
    obtain ⟨m, hm⟩ := (legal_row_exact v).1 h
    exact ⟨S.mkQ m, congrArg (legalDen S).mkQ hm⟩
  · rintro ⟨a, ha⟩
    rw [← ha]
    obtain ⟨m, rfl⟩ := S.mkQ_surjective a
    exact legalPacketMean_legalMixedInclusion m

theorem lower_exact : Function.Exact (lowerInclusion S) (lowerMean S) := by
  intro q
  obtain ⟨x, rfl⟩ := (ambientDen S).mkQ_surjective q
  constructor
  · intro h
    exact ⟨(zeroDen S).mkQ ⟨x, h⟩, rfl⟩
  · rintro ⟨a, ha⟩
    rw [← ha]
    obtain ⟨z, rfl⟩ := (zeroDen S).mkQ_surjective a
    exact z.property

theorem left_comm :
    (lowerInclusion S).comp (leftVertical S) = (middleVertical S).comp (upperInclusion S) := by
  apply LinearMap.ext
  intro q
  obtain ⟨m, rfl⟩ := S.mkQ_surjective q
  exact congrArg (ambientDen S).mkQ (DFunLike.congr_fun left_square m)

theorem right_comm :
    (lowerMean S).comp (middleVertical S) = (0 : ℝ →ₗ[ℝ] ℝ).comp (upperMean S) := by
  apply LinearMap.ext
  intro q
  obtain ⟨v, rfl⟩ := (legalDen S).mkQ_surjective q
  exact center_mem v.val

private abbrev centerKernel := (center.codRestrict meanZero center_mem).toLinearMap

private theorem centerKernel_fixes (z : meanZero) : centerKernel z.val = z := by
  apply Subtype.ext
  change center z.val = z.val
  rw [center_apply, show hilbertMeanContinuous z.val = 0 from z.property, zero_smul, sub_zero]

private theorem mixedRetraction_fixes (m : mixedClosure) :
    legalMixedRetraction (legalMixedInclusion m) = m := by
  apply Subtype.ext
  have h := legalMixedInclusion_legalMixedRetraction (legalMixedInclusion m)
  rw [legalPacketMean_legalMixedInclusion, map_zero, sub_zero] at h
  exact congrArg (fun v : closedSpace => (v : ThresholdHilbert)) h

def upperRetraction : (closedSpace ⧸ legalDen S) →ₗ[ℝ] (mixedClosure ⧸ S) :=
  (legalDen S).mapQ S legalMixedRetraction.toLinearMap (by
    rintro _ ⟨m, hm, rfl⟩
    change legalMixedRetraction (legalMixedInclusion m) ∈ S
    change m ∈ S at hm
    rw [mixedRetraction_fixes]
    exact hm)

def lowerRetraction : (ThresholdHilbert ⧸ ambientDen S) →ₗ[ℝ] (meanZero ⧸ zeroDen S) :=
  (ambientDen S).mapQ (zeroDen S) centerKernel (by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, hm, (centerKernel_fixes (mixedInclusion m)).symm⟩)

def upperSection : ℝ →ₗ[ℝ] (closedSpace ⧸ legalDen S) :=
  (legalDen S).mkQ.comp screenedMeanSection.toLinearMap

def lowerSection : ℝ →ₗ[ℝ] (ThresholdHilbert ⧸ ambientDen S) :=
  (ambientDen S).mkQ.comp (ContinuousLinearMap.toSpanSingleton ℝ hilbertOne).toLinearMap

def upperRow : ShortComplex (ModuleCat ℝ) :=
  ShortComplex.moduleCatMk (upperInclusion S) (upperMean S) (upper_exact S).linearMap_comp_eq_zero

def lowerRow : ShortComplex (ModuleCat ℝ) :=
  ShortComplex.moduleCatMk (lowerInclusion S) (lowerMean S) (lower_exact S).linearMap_comp_eq_zero

def upperSplitting : (upperRow S).Splitting where
  r := ModuleCat.ofHom (upperRetraction S)
  s := ModuleCat.ofHom (upperSection S)
  f_r := by
    apply ConcreteCategory.hom_ext
    intro q
    obtain ⟨m, rfl⟩ := S.mkQ_surjective q
    exact congrArg S.mkQ (mixedRetraction_fixes m)
  s_g := by
    apply ConcreteCategory.hom_ext
    intro a
    exact legalPacketMean_screenedMeanSection a
  id := by
    apply ConcreteCategory.hom_ext
    intro q
    obtain ⟨v, rfl⟩ := (legalDen S).mkQ_surjective q
    change (legalDen S).mkQ (legalMixedInclusion (legalMixedRetraction v)) +
      (legalDen S).mkQ (screenedMeanSection (legalPacketMean v)) = (legalDen S).mkQ v
    rw [← map_add, legalMixedInclusion_legalMixedRetraction, sub_add_cancel]

def lowerSplitting : (lowerRow S).Splitting where
  r := ModuleCat.ofHom (lowerRetraction S)
  s := ModuleCat.ofHom (lowerSection S)
  f_r := by
    apply ConcreteCategory.hom_ext
    intro q
    obtain ⟨z, rfl⟩ := (zeroDen S).mkQ_surjective q
    exact congrArg (zeroDen S).mkQ (centerKernel_fixes z)
  s_g := by
    apply ConcreteCategory.hom_ext
    intro a
    change ℝ at a
    change hilbertMeanContinuous (a • hilbertOne) = a
    simp
  id := by
    apply ConcreteCategory.hom_ext
    intro q
    obtain ⟨x, rfl⟩ := (ambientDen S).mkQ_surjective q
    change (ambientDen S).mkQ (center x) +
      (ambientDen S).mkQ (hilbertMeanContinuous x • hilbertOne) = (ambientDen S).mkQ x
    rw [← map_add, center_apply, sub_add_cancel]

theorem upper_shortExact : (upperRow S).ShortExact := (upperSplitting S).shortExact
theorem lower_shortExact : (lowerRow S).ShortExact := (lowerSplitting S).shortExact

def diagram : upperRow S ⟶ lowerRow S where
  τ₁ := ModuleCat.ofHom (leftVertical S)
  τ₂ := ModuleCat.ofHom (middleVertical S)
  τ₃ := 0
  comm₁₂ := by
    apply ConcreteCategory.hom_ext
    intro q
    exact DFunLike.congr_fun (left_comm S) q
  comm₂₃ := by
    apply ConcreteCategory.hom_ext
    intro q
    exact DFunLike.congr_fun (right_comm S) q

theorem cokernel_exact : Function.Exact (leftVertical S) (mixedImage S).mkQ := by
  intro q
  change (Submodule.Quotient.mk q : Target S) = 0 ↔ ∃ a, leftVertical S a = q
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨S.mkQ ⟨z.val, hz⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨m, rfl⟩ := S.mkQ_surjective a
    exact ⟨mixedInclusion m, m.property, rfl⟩

/-- The snake map computed in the quotient diagram itself. -/
def connecting : ℝ →ₗ[ℝ] Target S :=
  SnakeLemma.δ (leftVertical S) (middleVertical S) (0 : ℝ →ₗ[ℝ] ℝ)
    (upperInclusion S) (upperMean S) (upper_exact S)
    (lowerInclusion S) (lowerMean S) (lower_exact S) (left_comm S) (right_comm S)
    (upperSection S) (funext legalPacketMean_screenedMeanSection)
    (lowerRetraction S) (by
      funext q
      obtain ⟨z, rfl⟩ := (zeroDen S).mkQ_surjective q
      exact congrArg (zeroDen S).mkQ (centerKernel_fixes z))
    LinearMap.id ((LinearMap.exact_zero_iff_surjective _ _).2 Function.surjective_id)
    (mixedImage S).mkQ (cokernel_exact S)

theorem connecting_on_lift (v : closedSpace) :
    connecting S (legalPacketMean v) =
      (mixedImage S).mkQ ((zeroDen S).mkQ ⟨center v.val, center_mem v.val⟩) := by
  unfold connecting
  apply SnakeLemma.δ_eq (y := (legalDen S).mkQ v)
  · rfl
  · rfl

/-- The third isomorphism preserves the quotient seminorm for every mixed denominator. -/
def targetIsometryEquiv : Target S ≃ₗᵢ[ℝ] BoundaryTarget :=
  Submodule.quotientQuotientLIEQuotient (zeroDen S) mixedInMeanZero (by
    rintro _ ⟨m, _, rfl⟩
    exact m.property)

/-- Cancellation of the same stage denominator from the ambient snake target. -/
def targetEquiv : Target S ≃ₗ[ℝ] BoundaryTarget :=
  (targetIsometryEquiv S).toLinearEquiv

theorem targetEquiv_connecting (a : ℝ) : targetEquiv S (connecting S a) = boundary a := by
  have h (v : closedSpace) :
      targetEquiv S (connecting S (legalPacketMean v)) = boundary (legalPacketMean v) := by
    rw [connecting_on_lift, boundary_of_lift]
    rfl
  simpa only [legalPacketMean_screenedMeanSection] using h (screenedMeanSection a)

/-- Every stage measures exactly the ambient defect, even at a nonclosed denominator. -/
theorem norm_connecting (a : ℝ) :
    ‖connecting S a‖ = |a| * ‖normalizedScreenedTwo - hilbertOne‖ := by
  calc
    _ = ‖targetIsometryEquiv S (connecting S a)‖ := ((targetIsometryEquiv S).norm_map _).symm
    _ = ‖boundary a‖ := congrArg (fun z : BoundaryTarget => ‖z‖) (targetEquiv_connecting S a)
    _ = _ := by rw [boundary_apply, norm_smul, Real.norm_eq_abs, norm_defect_class]

/-- The unit at any quotient stage detects exactly the ambient membership problem. -/
theorem connecting_one_eq_zero_iff :
    connecting S 1 = 0 ↔ hilbertOne ∈ closedSpace := by
  rw [← boundary_eq_zero_iff_one_mem]
  constructor
  · intro hz
    have h1 : boundary 1 = 0 := by rw [← targetEquiv_connecting S, hz, map_zero]
    have hdef : mixedInMeanZero.mkQ defect = 0 := by simpa [boundary_apply] using h1
    apply ContinuousLinearMap.ext
    intro a
    simp [boundary_apply, hdef]
  · intro hb
    apply (targetEquiv S).injective
    rw [targetEquiv_connecting, map_zero, hb]
    rfl

variable {S} {T : Submodule ℝ mixedClosure}

/-- Change the denominator in the ambient mean kernel. -/
def zeroTransition (h : S ≤ T) : (meanZero ⧸ zeroDen S) →ₗ[ℝ] (meanZero ⧸ zeroDen T) :=
  (zeroDen S).mapQ (zeroDen T) LinearMap.id (Submodule.map_mono h)

/-- The actual representative-preserving transition on the double quotients. -/
def targetTransition (h : S ≤ T) : Target S →ₗ[ℝ] Target T :=
  (mixedImage S).mapQ (mixedImage T) (zeroTransition h) (by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩)

theorem connecting_natural (h : S ≤ T) (a : ℝ) :
    targetTransition h (connecting S a) = connecting T a := by
  have hv (v : closedSpace) :
      targetTransition h (connecting S (legalPacketMean v)) = connecting T (legalPacketMean v) := by
    rw [connecting_on_lift, connecting_on_lift]
    rfl
  simpa only [legalPacketMean_screenedMeanSection] using hv (screenedMeanSection a)

theorem targetEquiv_transition (h : S ≤ T) (q : Target S) :
    targetEquiv T (targetTransition h q) = targetEquiv S q := by
  obtain ⟨z, rfl⟩ := (mixedImage S).mkQ_surjective q
  obtain ⟨x, rfl⟩ := (zeroDen S).mkQ_surjective z
  rfl

/-- The representative-preserving transition is transport along the two quotient isometries. -/
theorem targetTransition_eq_isometric_transport (h : S ≤ T) (q : Target S) :
    targetTransition h q = (targetIsometryEquiv T).symm (targetIsometryEquiv S q) := by
  apply (targetIsometryEquiv T).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact targetEquiv_transition h q

/-- Throughout the prime-support filtration, centering gives the original defect class. -/
theorem support_connecting (n : ℕ) (a : ℝ) :
    targetEquiv (supportSpace n) (connecting (supportSpace n) a) =
      a • mixedInMeanZero.mkQ defect :=
  (targetEquiv_connecting _ a).trans (boundary_apply a)

/-- At the support union, the remaining mixed subspace of the intermediate
ambient mean quotient is exactly its closure of zero. -/
theorem mixedImage_supportUnion_eq_closure_zero :
    (mixedImage (⨆ n, supportSpace n) : Set (meanZero ⧸ zeroDen (⨆ n, supportSpace n))) =
      closure ({0} : Set _) := by
  let U : Submodule ℝ mixedClosure := ⨆ n, supportSpace n
  let D := zeroDen U
  have hDM : D ≤ mixedInMeanZero := by
    rintro _ ⟨m, _, rfl⟩
    exact m.property
  have hD : D.topologicalClosure = mixedInMeanZero := by
    apply le_antisymm (Submodule.topologicalClosure_minimal _ hDM mixedInMeanZero_closed)
    let K := D.topologicalClosure.comap mixedInclusion.toLinearMap
    have hK : IsClosed (K : Set mixedClosure) :=
      (isClosed_closure : IsClosed (closure (D : Set meanZero))).preimage mixedInclusion.continuous
    have hUK : U ≤ K := fun m hm => Submodule.le_topologicalClosure D ⟨m, hm, rfl⟩
    have hd := Submodule.topologicalClosure_minimal _ hUK hK
    rw [show U.topologicalClosure = ⊤ from supportSpace_dense] at hd
    intro z hz
    exact hd (show (⟨z.val, hz⟩ : mixedClosure) ∈ ⊤ from trivial)
  have hp : D.mkQ ⁻¹' ({0} : Set (meanZero ⧸ D)) = (D : Set meanZero) := by
    ext z
    exact Submodule.Quotient.mk_eq_zero D
  have hc := D.isOpenMap_mkQ.preimage_closure_eq_closure_preimage
    D.isOpenQuotientMap_mkQ.continuous ({0} : Set (meanZero ⧸ D))
  rw [hp] at hc
  change D.mkQ ⁻¹' closure ({0} : Set (meanZero ⧸ D)) = (D.topologicalClosure : Set meanZero) at hc
  rw [hD] at hc
  ext q
  obtain ⟨z, rfl⟩ := D.mkQ_surjective q
  calc
    D.mkQ z ∈ mixedImage U ↔ (mixedImage U).mkQ (D.mkQ z) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).symm
    _ ↔ (targetEquiv U) ((mixedImage U).mkQ (D.mkQ z)) = (targetEquiv U) 0 :=
      (targetEquiv U).injective.eq_iff.symm
    _ ↔ mixedInMeanZero.mkQ z = 0 := by rw [map_zero]; rfl
    _ ↔ z ∈ mixedInMeanZero := Submodule.Quotient.mk_eq_zero _
    _ ↔ D.mkQ z ∈ closure ({0} : Set _) := (Set.ext_iff.mp hc z).symm

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.Stage

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.Stage
open CoefficientStabilization MixedConductorBasis LegalMeanAlgebra
open scoped LegalMeanAlgebra

variable (S : Submodule ℝ mixedClosure)

private theorem constant_iff_center_zero (v : closedSpace) :
    v ∈ legalConstants ↔ centerLegal v = 0 := by
  change v.val ∈ Submodule.span ℝ {hilbertOne} ↔ center v.val = 0
  rw [Submodule.mem_span_singleton, center_apply, sub_eq_zero]
  constructor
  · rintro ⟨a, ha⟩
    rw [← ha]
    simp
  · intro h
    exact ⟨hilbertMeanContinuous v.val, h.symm⟩

/-- Passing a legal constant to its class in the middle vertical kernel. -/
def constantToKernel : legalConstants →ₗ[ℝ] (middleVertical S).ker :=
  ((legalDen S).mkQ.comp legalConstants.subtype).codRestrict _ (by
    intro v
    change (ambientDen S).mkQ (centerLegal v.val) = 0
    rw [(constant_iff_center_zero v.val).1 v.property, map_zero])

theorem constantToKernel_bijective : Function.Bijective (constantToKernel S) := by
  constructor
  · intro x y h
    apply constantMean_injective
    exact congrArg (fun q : (middleVertical S).ker => upperMean S q.val) h
  · intro q
    obtain ⟨v, hv⟩ := (legalDen S).mkQ_surjective q.val
    have hc : centerLegal v ∈ ambientDen S := by
      apply (Submodule.Quotient.mk_eq_zero _).1
      change middleVertical S ((legalDen S).mkQ v) = 0
      rw [hv]
      exact q.property
    obtain ⟨m, hm, he⟩ := hc
    have hu : v - legalMixedInclusion m ∈ legalConstants := by
      apply (constant_iff_center_zero _).2
      rw [map_sub, sub_eq_zero]
      exact he.symm.trans (DFunLike.congr_fun left_square m)
    refine ⟨⟨_, hu⟩, Subtype.ext ?_⟩
    change (legalDen S).mkQ (v - legalMixedInclusion m) = q.val
    have hz : (legalDen S).mkQ (legalMixedInclusion m) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 ⟨m, hm, rfl⟩
    rw [map_sub, hz, sub_zero, hv]

def kernelEquiv : legalConstants ≃ₗ[ℝ] (middleVertical S).ker :=
  LinearEquiv.ofBijective (constantToKernel S) (constantToKernel_bijective S)

abbrev StageCokernel := (ThresholdHilbert ⧸ ambientDen S) ⧸ LinearMap.range (middleVertical S)

theorem centerRange_eq :
    LinearMap.range (middleVertical S) = (LinearMap.range centerLegal.toLinearMap).map
      (ambientDen S).mkQ := by
  ext q
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨v, rfl⟩ := (legalDen S).mkQ_surjective a
    exact ⟨centerLegal v, ⟨v, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨(legalDen S).mkQ v, rfl⟩

/-- The middle vertical cokernel has the same ambient representative at each stage. -/
def centerCokernelEquiv : StageCokernel S ≃ₗ[ℝ] CenterCokernel :=
  (Submodule.quotEquivOfEq _ _ (centerRange_eq S)).trans
    (Submodule.quotientQuotientEquivQuotient (ambientDen S)
      (LinearMap.range centerLegal.toLinearMap) (by
        rintro _ ⟨m, _, rfl⟩
        exact ⟨legalMixedInclusion m, (DFunLike.congr_fun left_square m).symm⟩))

def kernelMean : (middleVertical S).ker →ₗ[ℝ] ℝ :=
  (upperMean S).comp (middleVertical S).ker.subtype

theorem kernelMean_injective : Function.Injective (kernelMean S) := by
  intro x y h
  obtain ⟨u, rfl⟩ := (kernelEquiv S).surjective x
  obtain ⟨v, rfl⟩ := (kernelEquiv S).surjective y
  exact congrArg (kernelEquiv S) (constantMean_injective h)

def toCokernel : Target S →ₗ[ℝ] StageCokernel S :=
  (mixedImage S).liftQ ((LinearMap.range (middleVertical S)).mkQ.comp (lowerInclusion S))
    (by
      rintro _ ⟨z, hz, rfl⟩
      apply (Submodule.Quotient.mk_eq_zero _).2
      let m : mixedClosure := ⟨z.val, hz⟩
      exact ⟨(legalDen S).mkQ (legalMixedInclusion m),
        congrArg (ambientDen S).mkQ (DFunLike.congr_fun left_square m).symm⟩)

def terminalMean : StageCokernel S →ₗ[ℝ] ℝ :=
  (LinearMap.range (middleVertical S)).liftQ (lowerMean S) (by
    rintro _ ⟨v, rfl⟩
    exact DFunLike.congr_fun (right_comm S) v)

theorem exact_kernelMean_connecting : Function.Exact (kernelMean S) (connecting S) := by
  unfold connecting
  apply SnakeLemma.exact_δ_right (ι₂ := (middleVertical S).ker.subtype)
    (hι₂ := LinearMap.exact_subtype_ker_map _)
  · rfl
  · exact Function.injective_id

theorem exact_connecting_toCokernel : Function.Exact (connecting S) (toCokernel S) := by
  unfold connecting
  apply SnakeLemma.exact_δ_left (π₂ := (LinearMap.range (middleVertical S)).mkQ)
    (hπ₂ := LinearMap.exact_map_mkQ_range _)
  · apply LinearMap.ext
    intro q
    rfl
  · exact (mixedImage S).mkQ_surjective

theorem exact_toCokernel_terminalMean : Function.Exact (toCokernel S) (terminalMean S) := by
  intro q
  obtain ⟨x, rfl⟩ := (LinearMap.range (middleVertical S)).mkQ_surjective q
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := (lower_exact S x).1 hx
    exact ⟨(mixedImage S).mkQ z, congrArg (LinearMap.range (middleVertical S)).mkQ hz⟩
  · rintro ⟨a, ha⟩
    rw [← ha]
    obtain ⟨z, rfl⟩ := (mixedImage S).mkQ_surjective a
    exact (lower_exact S _).2 ⟨z, rfl⟩

theorem terminalMean_surjective : Function.Surjective (terminalMean S) := by
  intro a
  refine ⟨(LinearMap.range (middleVertical S)).mkQ (lowerSection S a), ?_⟩
  change hilbertMeanContinuous (a • hilbertOne) = a
  simp

private abbrev StageZero := ↥(⊥ : Submodule ℝ ℝ)

def longSequence : ComposableArrows (ModuleCat ℝ) 6 :=
  (ComposableArrows.mk₅ (ModuleCat.ofHom (kernelMean S)) (ModuleCat.ofHom (connecting S))
    (ModuleCat.ofHom (toCokernel S)) (ModuleCat.ofHom (terminalMean S))
    (ModuleCat.ofHom (0 : ℝ →ₗ[ℝ] StageZero))).precomp
      (ModuleCat.ofHom (0 : StageZero →ₗ[ℝ] (middleVertical S).ker))

private theorem exactPair {X Y Z : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module ℝ X] [Module ℝ Y] [Module ℝ Z] (f : X →ₗ[ℝ] Y) (g : Y →ₗ[ℝ] Z)
    (h : Function.Exact f g) :
    (ComposableArrows.mk₂ (ModuleCat.ofHom f) (ModuleCat.ofHom g)).Exact := by
  have he := ModuleCat.shortComplex_exact (ShortComplex.moduleCatMk f g h.linearMap_comp_eq_zero) h
  exact he.exact_toComposableArrows

/-- The full kernel–cokernel exact sequence of the stage diagram, including both endpoints. -/
theorem longSequence_exact : (longSequence S).Exact := by
  apply ComposableArrows.exact_of_δ₀
  · apply exactPair (0 : StageZero →ₗ[ℝ] (middleVertical S).ker) (kernelMean S)
    exact (LinearMap.exact_zero_iff_injective _ _).2 (kernelMean_injective S)
  apply ComposableArrows.exact_of_δ₀
  · exact exactPair _ _ (exact_kernelMean_connecting S)
  apply ComposableArrows.exact_of_δ₀
  · exact exactPair _ _ (exact_connecting_toCokernel S)
  apply ComposableArrows.exact_of_δ₀
  · exact exactPair _ _ (exact_toCokernel_terminalMean S)
  exact exactPair (terminalMean S) (0 : ℝ →ₗ[ℝ] StageZero)
    ((LinearMap.exact_zero_iff_surjective _ _).2 (terminalMean_surjective S))

/-- All four non-endpoint arrows correspond to those of the original ambient snake. -/
theorem longSequence_comparison :
    (∀ v : legalConstants, quotientEquiv.symm (kernelMean S (kernelEquiv S v)) = constantClass v) ∧
    (∀ a : ℝ, targetEquiv S (connecting S a) = quotientBoundary (quotientEquiv.symm a)) ∧
    (∀ q : Target S, centerCokernelEquiv S (toCokernel S q) = toCenterCokernel (targetEquiv S q)) ∧
    (∀ q : StageCokernel S, terminalMean S q = cokernelMean (centerCokernelEquiv S q)) := by
  refine ⟨fun _ => rfl, ?_, ?_, ?_⟩
  · intro a
    rw [targetEquiv_connecting, quotientBoundary_apply, quotientEquiv.apply_symm_apply]
  · intro q
    obtain ⟨z, rfl⟩ := (mixedImage S).mkQ_surjective q
    obtain ⟨x, rfl⟩ := (zeroDen S).mkQ_surjective z
    rfl
  · intro q
    obtain ⟨z, rfl⟩ := (LinearMap.range (middleVertical S)).mkQ_surjective q
    obtain ⟨x, rfl⟩ := (ambientDen S).mkQ_surjective z
    rfl

/-- The quotient diagram's own connecting morphism realizes the algebra tower's boundary. -/
theorem support_connecting_algebra (n : ℕ) (v : closedSpace) :
    targetEquiv (supportSpace n) (connecting (supportSpace n) (legalPacketMean v)) =
      stageMeanBoundary n (Ideal.Quotient.mk (supportIdeal n) v) := by
  rw [targetEquiv_connecting, boundary_of_lift, stageMeanBoundary_mk]

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.Stage

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.Stage
open CoefficientStabilization MixedConductorBasis

private def quotientArrow {E : Type} [AddCommGroup E] [Module ℝ E] {A B : Submodule ℝ E}
    (h : A ≤ B) : ModuleCat.of ℝ (E ⧸ A) ⟶ ModuleCat.of ℝ (E ⧸ B) :=
  ModuleCat.ofHom (A.mapQ B LinearMap.id h)

private theorem quotientArrow_id {E : Type} [AddCommGroup E] [Module ℝ E] (A : Submodule ℝ E) :
    quotientArrow (le_refl A) = 𝟙 _ := by
  apply ConcreteCategory.hom_ext
  intro q
  obtain ⟨x, rfl⟩ := A.mkQ_surjective q
  rfl

private theorem quotientArrow_comp {E : Type} [AddCommGroup E] [Module ℝ E]
    {A B C : Submodule ℝ E} (h : A ≤ B) (k : B ≤ C) :
    quotientArrow (h.trans k) = quotientArrow h ≫ quotientArrow k := by
  apply ConcreteCategory.hom_ext
  intro q
  obtain ⟨x, rfl⟩ := A.mkQ_surjective q
  rfl

variable {S T : Submodule ℝ mixedClosure}

/-- Quotient the legal row along an inclusion of mixed submodules. -/
def upperTransition (h : S ≤ T) : upperRow S ⟶ upperRow T where
  τ₁ := quotientArrow h
  τ₂ := quotientArrow (Submodule.map_mono h : legalDen S ≤ legalDen T)
  τ₃ := 𝟙 _
  comm₁₂ := by
    apply ConcreteCategory.hom_ext
    intro q
    obtain ⟨m, rfl⟩ := S.mkQ_surjective q
    rfl
  comm₂₃ := by
    apply ConcreteCategory.hom_ext
    intro q
    obtain ⟨v, rfl⟩ := (legalDen S).mkQ_surjective q
    rfl

/-- Quotient the ambient row along the same inclusion. -/
def lowerTransition (h : S ≤ T) : lowerRow S ⟶ lowerRow T where
  τ₁ := quotientArrow (Submodule.map_mono h : zeroDen S ≤ zeroDen T)
  τ₂ := quotientArrow (Submodule.map_mono h : ambientDen S ≤ ambientDen T)
  τ₃ := 𝟙 _
  comm₁₂ := by
    apply ConcreteCategory.hom_ext
    intro q
    obtain ⟨z, rfl⟩ := (zeroDen S).mkQ_surjective q
    rfl
  comm₂₃ := by
    apply ConcreteCategory.hom_ext
    intro q
    obtain ⟨x, rfl⟩ := (ambientDen S).mkQ_surjective q
    rfl

/-- The legal short exact rows form a functor on the inclusion poset. -/
def upperRowFunctor : Submodule ℝ mixedClosure ⥤ ShortComplex (ModuleCat ℝ) where
  obj S := upperRow S
  map f := upperTransition (leOfHom f)
  map_id S := ShortComplex.hom_ext _ _ (quotientArrow_id S) (quotientArrow_id (legalDen S)) rfl
  map_comp {S T U} f g := ShortComplex.hom_ext _ _
    (quotientArrow_comp (leOfHom f) (leOfHom g))
    (quotientArrow_comp (Submodule.map_mono (leOfHom f) : legalDen S ≤ legalDen T)
      (Submodule.map_mono (leOfHom g) : legalDen T ≤ legalDen U)) rfl

/-- The ambient short exact rows form a functor on the same poset. -/
def lowerRowFunctor : Submodule ℝ mixedClosure ⥤ ShortComplex (ModuleCat ℝ) where
  obj S := lowerRow S
  map f := lowerTransition (leOfHom f)
  map_id S := ShortComplex.hom_ext _ _
    (quotientArrow_id (zeroDen S)) (quotientArrow_id (ambientDen S)) rfl
  map_comp {S T U} f g := ShortComplex.hom_ext _ _
    (quotientArrow_comp (Submodule.map_mono (leOfHom f) : zeroDen S ≤ zeroDen T)
      (Submodule.map_mono (leOfHom g) : zeroDen T ≤ zeroDen U))
    (quotientArrow_comp (Submodule.map_mono (leOfHom f) : ambientDen S ≤ ambientDen T)
      (Submodule.map_mono (leOfHom g) : ambientDen T ≤ ambientDen U)) rfl

/-- Both sections and both retractions commute with a change of stage. -/
theorem splittings_natural (h : S ≤ T) :
    (upperTransition h).τ₂ ≫ (upperSplitting T).r =
      (upperSplitting S).r ≫ (upperTransition h).τ₁ ∧
    (upperSplitting S).s ≫ (upperTransition h).τ₂ =
      (upperTransition h).τ₃ ≫ (upperSplitting T).s ∧
    (lowerTransition h).τ₂ ≫ (lowerSplitting T).r =
      (lowerSplitting S).r ≫ (lowerTransition h).τ₁ ∧
    (lowerSplitting S).s ≫ (lowerTransition h).τ₂ =
      (lowerTransition h).τ₃ ≫ (lowerSplitting T).s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro q
    obtain ⟨v, rfl⟩ := (legalDen S).mkQ_surjective q
    rfl
  · apply ConcreteCategory.hom_ext
    intro a
    rfl
  · apply ConcreteCategory.hom_ext
    intro q
    obtain ⟨x, rfl⟩ := (ambientDen S).mkQ_surjective q
    rfl
  · apply ConcreteCategory.hom_ext
    intro a
    rfl

/-- Centering is a natural transformation between the two diagrams of rows. -/
def diagramTransformation : upperRowFunctor ⟶ lowerRowFunctor where
  app S := diagram S
  naturality {S T} f := by
    apply ShortComplex.hom_ext
    · apply ConcreteCategory.hom_ext
      intro q
      obtain ⟨m, rfl⟩ := S.mkQ_surjective q
      rfl
    · apply ConcreteCategory.hom_ext
      intro q
      obtain ⟨v, rfl⟩ := (legalDen S).mkQ_surjective q
      rfl
    · rfl

/-- Restriction of the natural comparison to the infinite prime-support tower. -/
def supportDiagramTransformation :
    supportSpace_mono.functor ⋙ upperRowFunctor ⟶ supportSpace_mono.functor ⋙ lowerRowFunctor where
  app n := diagram (supportSpace n)
  naturality {i j} f := diagramTransformation.naturality (supportSpace_mono.functor.map f)

theorem supportDiagramTransformation_app (n : ℕ) :
    supportDiagramTransformation.app n = diagram (supportSpace n) := rfl

/-- The native stage cokernels are connected by their representative-preserving transitions. -/
def targetFunctor : Submodule ℝ mixedClosure ⥤ ModuleCat ℝ where
  obj S := ModuleCat.of ℝ (Target S)
  map f := ModuleCat.ofHom (targetTransition (leOfHom f))
  map_id S := by
    apply ConcreteCategory.hom_ext
    intro q
    obtain ⟨z, rfl⟩ := (mixedImage S).mkQ_surjective q
    obtain ⟨x, rfl⟩ := (zeroDen S).mkQ_surjective z
    rfl
  map_comp {S T U} f g := by
    apply ConcreteCategory.hom_ext
    intro q
    obtain ⟨z, rfl⟩ := (mixedImage S).mkQ_surjective q
    obtain ⟨x, rfl⟩ := (zeroDen S).mkQ_surjective z
    rfl

/-- The connecting maps form a natural transformation out of the constant scalar diagram. -/
def connectingTransformation :
    (Functor.const (Submodule ℝ mixedClosure)).obj (ModuleCat.of ℝ ℝ) ⟶ targetFunctor where
  app S := ModuleCat.ofHom (connecting S)
  naturality {S T} f := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (connecting_natural (leOfHom f) a).symm

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.Stage
