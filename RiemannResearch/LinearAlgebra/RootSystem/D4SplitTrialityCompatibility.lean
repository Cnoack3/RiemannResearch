/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.Algebra.Category.ModuleCat.Basic
import RiemannResearch.LinearAlgebra.RootSystem.D4OrthogonalRelatedTriples
import RiemannResearch.LinearAlgebra.RootSystem.D4SplitFock

/-!
# Split D4 representation compatibility with orthogonal related triples

This file packages the constructed vector and two exterior-Fock half-spin
representations as a three-label family and constructs the homomorphism from
split spin points to orthogonal related triples defined by those
representations. Given a symmetric triality tensor, common charts,
quadratic- and tensor-preservation proofs, and bijectivity, it produces the
Spin-to-related-triples equivalence, the component chart law, and compatible
faithful outer S3 pointwise triality data.

The tensor, charts, preservation proofs, and bijectivity are explicit remaining
pointwise comparison obligations; they are not inferred from matching
dimensions.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

open RiemannResearch.LinearAlgebra

universe uK uV

section SplitCompatibility

variable (K : Type uK) [Field K] [Invertible (2 : K)]

/-- The three already-constructed split D4 representation spaces. -/
def SplitTrialityModule : TrialityLabel → ModuleCat K
  | .vector => ModuleCat.of K (SplitD4Space K)
  | .halfSpinPlus => ModuleCat.of K (SplitHalfSpinPlus K)
  | .halfSpinMinus => ModuleCat.of K (SplitHalfSpinMinus K)

/-- The vector and the two Fock half-spin representations as one family. -/
noncomputable def splitTrialityRepresentation :
    (l : TrialityLabel) →
      Representation K (CliffordEven.SpinPoint (splitD4Form K))
        (SplitTrialityModule K l)
  | .vector => CliffordEven.spinVectorRepresentation (splitD4Form K)
  | .halfSpinPlus => splitHalfSpinPlusRepresentation K
  | .halfSpinMinus => splitHalfSpinMinusRepresentation K

theorem splitTrialityModule_finrank (l : TrialityLabel) :
    Module.finrank K (SplitTrialityModule K l) = 8 := by
  cases l with
  | vector => exact (splitD4Form_regular K).1
  | halfSpinPlus => exact splitHalfSpinPlus_finrank K
  | halfSpinMinus => exact splitHalfSpinMinus_finrank K

variable (V : Type uV) [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

/-- Exact component formula needed to identify the three existing
representations with a related-triples realization. -/
def IsSplitRepresentationChart
    (t : OrthogonalTrialityTensor K V)
    (e : CliffordEven.SpinPoint (splitD4Form K) ≃*
      orthogonalRelatedTripleGroup K V Q t)
    (chart : ∀ l, (SplitTrialityModule K l) ≃ₗ[K] V) : Prop :=
  ∀ (g : CliffordEven.SpinPoint (splitD4Form K))
      (l : TrialityLabel) (x : SplitTrialityModule K l),
    ((e g).1 l).1 (chart l x) =
      chart l (splitTrialityRepresentation K l g x)

theorem trialityTensor_invariant_of_splitRepresentationChart
    (t : OrthogonalTrialityTensor K V)
    (e : CliffordEven.SpinPoint (splitD4Form K) ≃*
      orthogonalRelatedTripleGroup K V Q t)
    (chart : ∀ l, (SplitTrialityModule K l) ≃ₗ[K] V)
    (hc : IsSplitRepresentationChart K V Q t e chart)
    (g : CliffordEven.SpinPoint (splitD4Form K))
    (x : ∀ l, SplitTrialityModule K l) :
    orthogonalTrialityTensorEval K V t
        (fun l => chart l (splitTrialityRepresentation K l g (x l))) =
      orthogonalTrialityTensorEval K V t (fun l => chart l (x l)) := by
  calc
    orthogonalTrialityTensorEval K V t
        (fun l => chart l (splitTrialityRepresentation K l g (x l))) =
      orthogonalTrialityTensorEval K V t
        (fun l => ((e g).1 l).1 (chart l (x l))) := by
          congr 1
          funext l
          exact (hc g l (x l)).symm
    _ = orthogonalTrialityTensorEval K V t (fun l => chart l (x l)) := (e g).2 _

/-- The chart-induced transport from the `σ⁻¹ l` representation to the
`l` representation. -/
def splitTrialityChartTransport
    (chart : ∀ l, (SplitTrialityModule K l) ≃ₗ[K] V)
    (σ : DiagramSymmetry) (l : TrialityLabel) :
    (SplitTrialityModule K (σ⁻¹ l)) ≃ₗ[K]
      (SplitTrialityModule K l) :=
  (chart (σ⁻¹ l)).trans (chart l).symm

/-- The related-triples relabel action transported to Mathlib spin points. -/
def spinRelatedTripleAction
    (t : OrthogonalTrialityTensor K V) (ht : t.IsSymmetric K V)
    (e : CliffordEven.SpinPoint (splitD4Form K) ≃*
      orthogonalRelatedTripleGroup K V Q t) :
    DiagramSymmetry →*
      MulAut (CliffordEven.SpinPoint (splitD4Form K)) :=
  transportMulAutAction e
    (orthogonalRelatedTripleRelabelAction K V Q t ht)

theorem spinRelatedTripleAction_chart_equivariant
    (t : OrthogonalTrialityTensor K V) (ht : t.IsSymmetric K V)
    (e : CliffordEven.SpinPoint (splitD4Form K) ≃*
      orthogonalRelatedTripleGroup K V Q t)
    (chart : ∀ l, (SplitTrialityModule K l) ≃ₗ[K] V)
    (hc : IsSplitRepresentationChart K V Q t e chart)
    (σ : DiagramSymmetry)
    (g : CliffordEven.SpinPoint (splitD4Form K))
    (l : TrialityLabel) (x : SplitTrialityModule K (σ⁻¹ l)) :
    splitTrialityChartTransport K V chart σ l
        (splitTrialityRepresentation K (σ⁻¹ l) g x) =
      splitTrialityRepresentation K l
        (spinRelatedTripleAction K V Q t ht e σ g)
        (splitTrialityChartTransport K V chart σ l x) := by
  apply (chart l).injective
  simp only [splitTrialityChartTransport, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [← hc g (σ⁻¹ l) x]
  rw [← hc (spinRelatedTripleAction K V Q t ht e σ g) l
    ((chart l).symm (chart (σ⁻¹ l) x))]
  simpa [spinRelatedTripleAction, transportMulAutAction, transportMulAut,
    orthogonalRelatedTripleRelabelAction,
    orthogonalRelatedTripleRelabel, orthogonalTupleRelabel]

theorem spinRelatedTripleAction_not_inner_of_ne_one
    (t : OrthogonalTrialityTensor K V) (ht : t.IsSymmetric K V)
    (v : V) (hv : -v ≠ v)
    (e : CliffordEven.SpinPoint (splitD4Form K) ≃*
      orthogonalRelatedTripleGroup K V Q t)
    (σ : DiagramSymmetry) (hσ : σ ≠ 1) :
    ¬ IsInnerAutomorphism (spinRelatedTripleAction K V Q t ht e σ) := by
  intro hinner
  apply orthogonalRelatedTripleRelabel_not_inner_of_ne_one
    K V Q t ht v hv σ hσ
  apply (isInner_transportMulAut_iff e
    (orthogonalRelatedTripleRelabelAction K V Q t ht σ)).mp
  simpa [spinRelatedTripleAction, transportMulAutAction] using hinner

theorem spinRelatedTripleAction_injective
    (t : OrthogonalTrialityTensor K V) (ht : t.IsSymmetric K V)
    (v : V) (hv : -v ≠ v)
    (e : CliffordEven.SpinPoint (splitD4Form K) ≃*
      orthogonalRelatedTripleGroup K V Q t) :
    Function.Injective (spinRelatedTripleAction K V Q t ht e) :=
  action_injective_of_nontrivial_not_inner
    (spinRelatedTripleAction K V Q t ht e)
    (spinRelatedTripleAction_not_inner_of_ne_one K V Q t ht v hv e)

/-- Construct the existing pointwise triality interface from an actual
related-triples realization and the central-sign outerness certificate. -/
def spinPointTrialityDataOfOrthogonalRelatedTriple
    (t : OrthogonalTrialityTensor K V) (ht : t.IsSymmetric K V)
    (v : V) (hv : -v ≠ v)
    (e : CliffordEven.SpinPoint (splitD4Form K) ≃*
      orthogonalRelatedTripleGroup K V Q t) :
    SpinPointTrialityData (splitD4Form K) where
  regularEightDimensional := splitD4Form_regular K
  action := spinRelatedTripleAction K V Q t ht e
  faithful := spinRelatedTripleAction_injective K V Q t ht v hv e

end SplitCompatibility

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality


namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

universe uK

section SplitSpecialization

variable (K : Type uK) [Field K] [Invertible (2 : K)]

/-- A canonical witness that the central sign markers are distinct on the
standard split D4 space. -/
theorem splitFockParityUnit_neg_ne :
    -(splitFockParityUnit K) ≠ splitFockParityUnit K := by
  intro h
  have hc := congrArg (fun x : SplitD4Space K => x.2 0) h
  simp [splitFockParityUnit] at hc
  have htwo : (2 : K) ≠ 0 :=
    isUnit_iff_ne_zero.mp (isUnit_of_invertible (2 : K))
  apply htwo
  calc
    (2 : K) = 1 + 1 := by norm_num
    _ = (-1 : K) + 1 :=
      congrArg (fun z : K => z + 1) hc.symm
    _ = 0 := neg_add_cancel 1

/-- Once a symmetric tensor and the Spin-to-related-triples equivalence are
constructed on the standard split space, the faithful outer pointwise
triality data needs no additional sign or faithfulness witness. -/
def splitSpinPointTrialityDataOfOrthogonalRelatedTriple
    (t : OrthogonalTrialityTensor K (SplitD4Space K))
    (ht : t.IsSymmetric K (SplitD4Space K))
    (e : RiemannResearch.LinearAlgebra.CliffordEven.SpinPoint
        (splitD4Form K) ≃*
      orthogonalRelatedTripleGroup K (SplitD4Space K)
        (splitD4Form K) t) :
    SpinPointTrialityData (splitD4Form K) :=
  spinPointTrialityDataOfOrthogonalRelatedTriple
    K (SplitD4Space K) (splitD4Form K) t ht
    (splitFockParityUnit K) (splitFockParityUnit_neg_ne K) e

end SplitSpecialization

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

open RiemannResearch.LinearAlgebra

universe uK uV uG uH uS

section RepresentationBridgeHelpers

def representationLinearEquiv
    {K : Type uK} [Field K]
    {G : Type uG} [Group G]
    {W : Type uH} [AddCommGroup W] [Module K W]
    (ρ : Representation K G W) (g : G) : W ≃ₗ[K] W :=
  LinearEquiv.ofLinear (ρ g) (ρ g⁻¹)
    (by
      apply LinearMap.ext
      intro x
      have h := DFunLike.congr_fun (ρ.map_mul g g⁻¹).symm x
      simpa [Module.End.mul_apply] using h)
    (by
      apply LinearMap.ext
      intro x
      have h := DFunLike.congr_fun (ρ.map_mul g⁻¹ g).symm x
      simpa [Module.End.mul_apply] using h)

/-- Conjugate a representation into automorphisms of a chosen common chart. -/
def chartedRepresentation
    {K : Type uK} [Field K]
    {G : Type uG} [Group G]
    {W : Type uH} [AddCommGroup W] [Module K W]
    {V : Type uS} [AddCommGroup V] [Module K V]
    (ρ : Representation K G W) (chart : W ≃ₗ[K] V) :
    G →* (V ≃ₗ[K] V) where
  toFun g := chart.symm.trans ((representationLinearEquiv ρ g).trans chart)
  map_one' := by
    ext x
    simp [representationLinearEquiv]
  map_mul' g h := by
    ext x
    simp only [LinearEquiv.mul_apply, LinearEquiv.trans_apply]
    change chart (ρ (g * h) (chart.symm x)) =
      chart (ρ g (chart.symm (chart (ρ h (chart.symm x)))))
    rw [chart.symm_apply_apply]
    rw [ρ.map_mul]
    rfl

end RepresentationBridgeHelpers

section RepresentationDefinedBridge

variable (K : Type uK) [Field K] [Invertible (2 : K)]
variable (V : Type uV) [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

noncomputable def splitTrialityLinearTupleHom
    (chart : ∀ l, (SplitTrialityModule K l) ≃ₗ[K] V) :
    CliffordEven.SpinPoint (splitD4Form K) →*
      (TrialityLabel → (V ≃ₗ[K] V)) where
  toFun g l :=
    chartedRepresentation (splitTrialityRepresentation K l) (chart l) g
  map_one' := by
    funext l
    exact (chartedRepresentation
      (splitTrialityRepresentation K l) (chart l)).map_one
  map_mul' g h := by
    funext l
    exact (chartedRepresentation
      (splitTrialityRepresentation K l) (chart l)).map_mul g h

/-- Exact quadratic-form preservation obligation for the charted tuple. -/
def SplitTrialityTuplePreservesQuadratic
    (chart : ∀ l, (SplitTrialityModule K l) ≃ₗ[K] V) : Prop :=
  ∀ (g : CliffordEven.SpinPoint (splitD4Form K))
      (l : TrialityLabel) (x : V),
    Q (splitTrialityLinearTupleHom K V chart g l x) = Q x

/-- Exact trilinear-tensor preservation obligation for the charted tuple. -/
def SplitTrialityTuplePreservesTensor
    (t : OrthogonalTrialityTensor K V)
    (chart : ∀ l, (SplitTrialityModule K l) ≃ₗ[K] V) : Prop :=
  ∀ (g : CliffordEven.SpinPoint (splitD4Form K))
      (x : TrialityLabel → V),
    orthogonalTrialityTensorEval K V t
        (fun l => splitTrialityLinearTupleHom K V chart g l (x l)) =
      orthogonalTrialityTensorEval K V t x

/-- The homomorphism from the current pointwise Spin group into related
triples, constructed directly from the three existing representations. -/
noncomputable def splitSpinToOrthogonalRelatedTriples
    (t : OrthogonalTrialityTensor K V)
    (chart : ∀ l, (SplitTrialityModule K l) ≃ₗ[K] V)
    (hQ : SplitTrialityTuplePreservesQuadratic K V Q chart)
    (ht : SplitTrialityTuplePreservesTensor K V t chart) :
    CliffordEven.SpinPoint (splitD4Form K) →*
      orthogonalRelatedTripleGroup K V Q t where
  toFun g :=
    ⟨fun l =>
      ⟨splitTrialityLinearTupleHom K V chart g l, hQ g l⟩,
      ht g⟩
  map_one' := by
    apply Subtype.ext
    funext l
    apply Subtype.ext
    exact congrFun (splitTrialityLinearTupleHom K V chart).map_one l
  map_mul' g h := by
    apply Subtype.ext
    funext l
    apply Subtype.ext
    exact congrFun
      ((splitTrialityLinearTupleHom K V chart).map_mul g h) l

@[simp]
theorem splitSpinToOrthogonalRelatedTriples_component
    (t : OrthogonalTrialityTensor K V)
    (chart : ∀ l, (SplitTrialityModule K l) ≃ₗ[K] V)
    (hQ : SplitTrialityTuplePreservesQuadratic K V Q chart)
    (ht : SplitTrialityTuplePreservesTensor K V t chart)
    (g : CliffordEven.SpinPoint (splitD4Form K))
    (l : TrialityLabel) :
    ((splitSpinToOrthogonalRelatedTriples K V Q t chart hQ ht g).1 l).1 =
      splitTrialityLinearTupleHom K V chart g l :=
  rfl

/-- Bijectivity of the representation-defined homomorphism gives the exact
Spin-to-related-triples equivalence; no unrelated equivalence is selected. -/
noncomputable def splitSpinRelatedTripleEquiv
    (t : OrthogonalTrialityTensor K V)
    (chart : ∀ l, (SplitTrialityModule K l) ≃ₗ[K] V)
    (hQ : SplitTrialityTuplePreservesQuadratic K V Q chart)
    (ht : SplitTrialityTuplePreservesTensor K V t chart)
    (hbij : Function.Bijective
      (splitSpinToOrthogonalRelatedTriples K V Q t chart hQ ht)) :
    CliffordEven.SpinPoint (splitD4Form K) ≃*
      orthogonalRelatedTripleGroup K V Q t :=
  MulEquiv.ofBijective
    (splitSpinToOrthogonalRelatedTriples K V Q t chart hQ ht) hbij

theorem splitSpinRelatedTripleEquiv_isSplitRepresentationChart
    (t : OrthogonalTrialityTensor K V)
    (chart : ∀ l, (SplitTrialityModule K l) ≃ₗ[K] V)
    (hQ : SplitTrialityTuplePreservesQuadratic K V Q chart)
    (ht : SplitTrialityTuplePreservesTensor K V t chart)
    (hbij : Function.Bijective
      (splitSpinToOrthogonalRelatedTriples K V Q t chart hQ ht)) :
    IsSplitRepresentationChart K V Q t
      (splitSpinRelatedTripleEquiv K V Q t chart hQ ht hbij) chart := by
  intro g l x
  simp [splitSpinRelatedTripleEquiv,
    splitSpinToOrthogonalRelatedTriples,
    splitTrialityLinearTupleHom, chartedRepresentation,
    representationLinearEquiv]

/-- The compatible faithful outer action obtained from the
representation-defined related-triples map once its concrete preservation
and bijectivity obligations have been proved. -/
noncomputable def splitSpinPointTrialityDataOfRepresentationBridge
    (t : OrthogonalTrialityTensor K V)
    (hsym : t.IsSymmetric K V)
    (chart : ∀ l, (SplitTrialityModule K l) ≃ₗ[K] V)
    (hQ : SplitTrialityTuplePreservesQuadratic K V Q chart)
    (ht : SplitTrialityTuplePreservesTensor K V t chart)
    (hbij : Function.Bijective
      (splitSpinToOrthogonalRelatedTriples K V Q t chart hQ ht))
    (v : V) (hv : -v ≠ v) :
    SpinPointTrialityData (splitD4Form K) :=
  spinPointTrialityDataOfOrthogonalRelatedTriple
    K V Q t hsym v hv
      (splitSpinRelatedTripleEquiv K V Q t chart hQ ht hbij)

end RepresentationDefinedBridge

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality
