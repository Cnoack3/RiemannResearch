import RiemannResearch.RH.CenteredMeanQuotients
import RiemannResearch.RH.CenteredMeanSnake
import RiemannResearch.RH.MixedConductorSquareZero
import RiemannResearch.RH.MixedConductorSplitExact
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The centered mean long exact sequence

Let `Z` be the ambient mean kernel and let `c(v) = v - C(v) • 1` on the legal
space `V`. Comparing the two split short exact mean sequences gives

`0 → V ∩ ℝ1 → V/M → Z/M → H/c(V) → ℝ → 0`.

We identify the scalar kernel of the zero vertical arrow with the screened
algebra quotient by its augmentation ideal. Its connecting map sends the
class of a legal vector to its centered class. The two cokernel arrows below
are induced by inclusion and ambient expectation.

The sign convention is that of mathlib's `SnakeLemma.δ`, used in
`CenteredMeanSnake`. For the general six-term sequence see the Stacks Project,
Tag 07JV, https://stacks.math.columbia.edu/tag/07JV.
-/

noncomputable section

open CategoryTheory

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
open CoefficientStabilization LegalMeanAlgebra
open scoped LegalMeanAlgebra

/-- The middle cokernel of the vertical maps in the centered diagram. -/
abbrev CenterCokernel := ThresholdHilbert ⧸ LinearMap.range centerLegal.toLinearMap

/-- The inclusion of the ambient mean kernel descends through the mixed subspace. -/
def toCenterCokernel : BoundaryTarget →ₗ[ℝ] CenterCokernel :=
  mixedInMeanZero.liftQ ((LinearMap.range centerLegal.toLinearMap).mkQ.comp meanZero.subtype) (by
    intro x hx
    apply (Submodule.Quotient.mk_eq_zero _).2
    refine ⟨legalMixedInclusion ⟨x.val, hx⟩, ?_⟩
    change center x.val = x.val
    rw [center_apply, show hilbertMeanContinuous x.val = 0 from x.property, zero_smul, sub_zero])

/-- Ambient expectation factors through the middle cokernel. -/
def cokernelMean : CenterCokernel →ₗ[ℝ] ℝ :=
  (LinearMap.range centerLegal.toLinearMap).liftQ hilbertMeanContinuous.toLinearMap (by
    rintro _ ⟨v, rfl⟩
    exact center_mem (v : ThresholdHilbert))

/-- The algebra class of a legal ambient constant. -/
def constantClass : legalConstants →ₗ[ℝ] (closedSpace ⧸ mixedIdeal) :=
  quotientEquiv.symm.toLinearEquiv.toLinearMap.comp constantMean

/-- The snake connecting map in the scalar coordinates supplied by the algebra quotient. -/
def quotientBoundary : (closedSpace ⧸ mixedIdeal) →ₗ[ℝ] BoundaryTarget :=
  snakeMap.comp quotientEquiv.toLinearEquiv.toLinearMap

theorem quotientBoundary_apply (q : closedSpace ⧸ mixedIdeal) :
    quotientBoundary q = boundary (quotientEquiv q) :=
  (DFunLike.congr_fun boundary_toLinearMap (quotientEquiv q)).symm

/-- Any representative of a legal algebra class gives its connecting class by centering. -/
theorem quotientBoundary_mk (v : closedSpace) :
    quotientBoundary (Ideal.Quotient.mk mixedIdeal v) =
      mixedInMeanZero.mkQ ⟨center v.val, center_mem v.val⟩ := by
  rw [quotientBoundary_apply, quotientEquiv_mk, boundary_of_lift]

theorem constantClass_injective : Function.Injective constantClass :=
  quotientEquiv.symm.injective.comp constantMean_injective

theorem exact_constantClass_quotientBoundary : Function.Exact constantClass quotientBoundary := by
  intro q
  rw [quotientBoundary_apply, exact_constantMean_boundary (quotientEquiv q)]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, quotientEquiv.injective (by simpa [constantClass] using hx)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, by simp [constantClass]⟩

theorem exact_quotientBoundary_toCenterCokernel :
    Function.Exact quotientBoundary toCenterCokernel := by
  intro q
  constructor
  · obtain ⟨z, rfl⟩ := mixedInMeanZero.mkQ_surjective q
    intro hz
    obtain ⟨v, hv⟩ := (Submodule.Quotient.mk_eq_zero (LinearMap.range centerLegal.toLinearMap)).1 hz
    refine ⟨Ideal.Quotient.mk mixedIdeal v, (quotientBoundary_mk v).trans ?_⟩
    exact congrArg mixedInMeanZero.mkQ (Subtype.ext hv)
  · rintro ⟨a, rfl⟩
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [quotientBoundary_mk]
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨v, rfl⟩

theorem exact_toCenterCokernel_cokernelMean : Function.Exact toCenterCokernel cokernelMean := by
  intro q
  constructor
  · obtain ⟨x, rfl⟩ := (LinearMap.range centerLegal.toLinearMap).mkQ_surjective q
    intro hx
    exact ⟨mixedInMeanZero.mkQ ⟨x, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := mixedInMeanZero.mkQ_surjective y
    exact x.property

theorem cokernelMean_surjective : Function.Surjective cokernelMean := by
  intro a
  refine ⟨(LinearMap.range centerLegal.toLinearMap).mkQ (a • hilbertOne), ?_⟩
  change hilbertMeanContinuous (a • hilbertOne) = a
  simp

private abbrev ZeroTerm := ↥(⊥ : Submodule ℝ ℝ)

/-- All six arrows, including the two endpoint zero maps, in real modules. -/
def centeredLongSequence : ComposableArrows (ModuleCat ℝ) 6 :=
  (ComposableArrows.mk₅ (ModuleCat.ofHom constantClass) (ModuleCat.ofHom quotientBoundary)
    (ModuleCat.ofHom toCenterCokernel) (ModuleCat.ofHom cokernelMean)
    (ModuleCat.ofHom (0 : ℝ →ₗ[ℝ] ZeroTerm))).precomp
      (ModuleCat.ofHom (0 : ZeroTerm →ₗ[ℝ] legalConstants))

private theorem pairExact {X Y Z : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module ℝ X] [Module ℝ Y] [Module ℝ Z] (f : X →ₗ[ℝ] Y) (g : Y →ₗ[ℝ] Z)
    (h : Function.Exact f g) :
    (ComposableArrows.mk₂ (ModuleCat.ofHom f) (ModuleCat.ofHom g)).Exact := by
  have hz : g.comp f = 0 := LinearMap.ext fun x => (h (f x)).2 ⟨x, rfl⟩
  exact (ModuleCat.shortComplex_exact (ShortComplex.moduleCatMk f g hz) h).exact_toComposableArrows

theorem centeredLongSequence_exact : centeredLongSequence.Exact := by
  apply ComposableArrows.exact_of_δ₀
  · apply pairExact (0 : ZeroTerm →ₗ[ℝ] legalConstants) constantClass
    exact (LinearMap.exact_zero_iff_injective _ _).2 constantClass_injective
  apply ComposableArrows.exact_of_δ₀
  · exact pairExact _ _ exact_constantClass_quotientBoundary
  apply ComposableArrows.exact_of_δ₀
  · exact pairExact _ _ exact_quotientBoundary_toCenterCokernel
  apply ComposableArrows.exact_of_δ₀
  · exact pairExact _ _ exact_toCenterCokernel_cokernelMean
  exact pairExact cokernelMean (0 : ℝ →ₗ[ℝ] ZeroTerm)
    ((LinearMap.exact_zero_iff_surjective _ _).2 cokernelMean_surjective)

/-- In the ambient quotient the algebra unit maps to the negative residual class. -/
theorem quotientBoundary_unit_residual :
    boundaryTargetEquivLegalQuotient (quotientBoundary 1) = -closedSpace.mkQ limitResidual := by
  rw [quotientBoundary_apply, map_one, boundaryTargetEquivLegalQuotient_boundary, one_smul]
  change -closedSpace.mkQ hilbertOne = -closedSpace.mkQ (hilbertOne - limitProjection)
  rw [map_sub, show closedSpace.mkQ limitProjection = 0 from
    (Submodule.Quotient.mk_eq_zero _).2 (closedSpace.starProjection_apply_mem _), sub_zero]

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
