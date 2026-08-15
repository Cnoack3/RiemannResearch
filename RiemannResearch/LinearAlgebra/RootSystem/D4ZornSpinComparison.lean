/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.LinearAlgebra.RootSystem.D4SplitTrialityFaithfulness
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornRelatedTriples

/-!
# Split spin representations and the concrete Zorn triality action

This module connects the constructed vector/Fock representation family to the
concrete split-Zorn related-triples group.  The homomorphism into related
triples is defined componentwise from the three representations.  Once its
explicit norm and tensor preservation laws and its surjectivity are proved,
the concrete twisted relabeling action transports to a compatible faithful
outer action on Mathlib spin points; injectivity is proved in this module.

Odd diagram permutations use Zorn conjugation in the chart transport.  This is
the concrete correction absent from a pure-relabel symmetric-tensor model.

The norm/tensor preservation and surjectivity boundary is deliberately
visible: it is the remaining comparison with the classical
Spin(8)-related-triples theorem, not a consequence of dimension counting.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

open RiemannResearch.LinearAlgebra

universe u

noncomputable section

variable (K : Type u) [Field K] [Invertible (2 : K)]

/-- A simultaneous choice of Zorn coordinates on the vector and two Fock
half-spin representation spaces. -/
abbrev SplitZornChart :=
  ∀ l, (SplitTrialityModule K l) ≃ₗ[K] Zorn.Octonion K

/-- Exact norm-preservation obligation for the three charted actions. -/
def SplitZornTuplePreservesNorm (chart : SplitZornChart K) : Prop :=
  ∀ (g : CliffordEven.SpinPoint (splitD4Form K))
      (l : TrialityLabel) (x : Zorn.Octonion K),
    Zorn.normForm K
        (splitTrialityLinearTupleHom K (Zorn.Octonion K) chart g l x) =
      Zorn.normForm K x

/-- Exact Zorn triality-tensor preservation obligation for the three charted
actions. -/
def SplitZornTuplePreservesTensor (chart : SplitZornChart K) : Prop :=
  ∀ (g : CliffordEven.SpinPoint (splitD4Form K))
      (x : TrialityLabel → Zorn.Octonion K),
    Zorn.trialityEval K
        (fun l =>
          splitTrialityLinearTupleHom K (Zorn.Octonion K) chart g l (x l)) =
      Zorn.trialityEval K x

/-- The representation-defined homomorphism from split spin points to the
concrete Zorn related-triples group. -/
noncomputable def splitSpinToZornRelatedTriples
    (chart : SplitZornChart K)
    (hQ : SplitZornTuplePreservesNorm K chart)
    (ht : SplitZornTuplePreservesTensor K chart) :
    CliffordEven.SpinPoint (splitD4Form K) →*
      Zorn.relatedTripleGroup K where
  toFun g :=
    ⟨fun l =>
      ⟨splitTrialityLinearTupleHom K (Zorn.Octonion K) chart g l,
        hQ g l⟩,
      ht g⟩
  map_one' := by
    apply Subtype.ext
    funext l
    apply Subtype.ext
    exact congrFun
      (splitTrialityLinearTupleHom K (Zorn.Octonion K) chart).map_one l
  map_mul' g h := by
    apply Subtype.ext
    funext l
    apply Subtype.ext
    exact congrFun
      ((splitTrialityLinearTupleHom K
        (Zorn.Octonion K) chart).map_mul g h) l

@[simp] theorem splitSpinToZornRelatedTriples_component
    (chart : SplitZornChart K)
    (hQ : SplitZornTuplePreservesNorm K chart)
    (ht : SplitZornTuplePreservesTensor K chart)
    (g : CliffordEven.SpinPoint (splitD4Form K))
    (l : TrialityLabel) :
    ((splitSpinToZornRelatedTriples K chart hQ ht g).1 l).1 =
      splitTrialityLinearTupleHom K (Zorn.Octonion K) chart g l :=
  rfl

/-- The representation-defined map from split spin points to Zorn related
triples is injective for every choice of charts and preservation proofs. -/
theorem splitSpinToZornRelatedTriples_injective
    (chart : SplitZornChart K)
    (hQ : SplitZornTuplePreservesNorm K chart)
    (ht : SplitZornTuplePreservesTensor K chart) :
    Function.Injective
      (splitSpinToZornRelatedTriples K chart hQ ht) := by
  intro g h hgh
  apply splitTrialityLinearTupleHom_injective K
    (Zorn.Octonion K) chart
  funext l
  have hc := congrArg
    (fun t : Zorn.relatedTripleGroup K => (t.1 l).1) hgh
  exact hc

/-- For the representation-defined comparison, bijectivity is exactly
surjectivity: injectivity follows from the faithful pair of Fock half-spin
blocks. -/
theorem splitSpinToZornRelatedTriples_bijective_iff_surjective
    (chart : SplitZornChart K)
    (hQ : SplitZornTuplePreservesNorm K chart)
    (ht : SplitZornTuplePreservesTensor K chart) :
    Function.Bijective
        (splitSpinToZornRelatedTriples K chart hQ ht) ↔
      Function.Surjective
        (splitSpinToZornRelatedTriples K chart hQ ht) := by
  constructor
  · exact fun h => h.2
  · intro hsurj
    exact ⟨splitSpinToZornRelatedTriples_injective K chart hQ ht,
      hsurj⟩

/-- A bijectivity witness gives the concrete Spin-to-Zorn-related-triples
equivalence; only its surjectivity component remains to be constructed. -/
noncomputable def splitSpinZornRelatedTripleEquiv
    (chart : SplitZornChart K)
    (hQ : SplitZornTuplePreservesNorm K chart)
    (ht : SplitZornTuplePreservesTensor K chart)
    (hbij : Function.Bijective
      (splitSpinToZornRelatedTriples K chart hQ ht)) :
    CliffordEven.SpinPoint (splitD4Form K) ≃*
      Zorn.relatedTripleGroup K :=
  MulEquiv.ofBijective (splitSpinToZornRelatedTriples K chart hQ ht) hbij

/-- The concrete Zorn outer action transported along the
representation-defined equivalence. -/
def splitSpinZornOuterAction
    (chart : SplitZornChart K)
    (hQ : SplitZornTuplePreservesNorm K chart)
    (ht : SplitZornTuplePreservesTensor K chart)
    (hbij : Function.Bijective
      (splitSpinToZornRelatedTriples K chart hQ ht)) :
    DiagramSymmetry →*
      MulAut (CliffordEven.SpinPoint (splitD4Form K)) :=
  transportMulAutAction
    (splitSpinZornRelatedTripleEquiv K chart hQ ht hbij)
    (Zorn.relatedTripleOuterAction K)

/-- Every nonidentity transported Zorn symmetry is non-inner. -/
theorem splitSpinZornOuterAction_not_inner
    (chart : SplitZornChart K)
    (hQ : SplitZornTuplePreservesNorm K chart)
    (ht : SplitZornTuplePreservesTensor K chart)
    (hbij : Function.Bijective
      (splitSpinToZornRelatedTriples K chart hQ ht))
    (σ : DiagramSymmetry) (hσ : σ ≠ 1) :
    ¬IsInnerAutomorphism
      (splitSpinZornOuterAction K chart hQ ht hbij σ) := by
  intro hinner
  apply Zorn.relatedTripleOuterAction_not_inner K σ hσ
  apply (isInner_transportMulAut_iff
    (splitSpinZornRelatedTripleEquiv K chart hQ ht hbij)
    (Zorn.relatedTripleOuterAction K σ)).mp
  simpa [splitSpinZornOuterAction, transportMulAutAction] using hinner

/-- The transported concrete Zorn action on split spin points is faithful. -/
theorem splitSpinZornOuterAction_injective
    (chart : SplitZornChart K)
    (hQ : SplitZornTuplePreservesNorm K chart)
    (ht : SplitZornTuplePreservesTensor K chart)
    (hbij : Function.Bijective
      (splitSpinToZornRelatedTriples K chart hQ ht)) :
    Function.Injective (splitSpinZornOuterAction K chart hQ ht hbij) :=
  action_injective_of_nontrivial_not_inner
    (splitSpinZornOuterAction K chart hQ ht hbij)
    (splitSpinZornOuterAction_not_inner K chart hQ ht hbij)

/-- The chart-side involution used by odd diagram permutations. -/
def zornDiagramTwist (σ : DiagramSymmetry) :
    Zorn.Octonion K ≃ₗ[K] Zorn.Octonion K :=
  if Zorn.DiagramEven σ then LinearEquiv.refl K (Zorn.Octonion K)
  else Zorn.conjugationLinearEquiv K

/-- Transport between the representation spaces, including conjugation for
odd diagram permutations. -/
def splitZornChartTransport
    (chart : SplitZornChart K)
    (σ : DiagramSymmetry) (l : TrialityLabel) :
    (SplitTrialityModule K (σ⁻¹ l)) ≃ₗ[K]
      (SplitTrialityModule K l) :=
  (chart (σ⁻¹ l)).trans
    ((zornDiagramTwist K σ).trans (chart l).symm)

/-- Exact component law relating a group equivalence to the three chosen
representation charts. -/
def IsSplitZornRepresentationChart
    (e : CliffordEven.SpinPoint (splitD4Form K) ≃*
      Zorn.relatedTripleGroup K)
    (chart : SplitZornChart K) : Prop :=
  ∀ (g : CliffordEven.SpinPoint (splitD4Form K))
      (l : TrialityLabel) (x : SplitTrialityModule K l),
    ((e g).1 l).1 (chart l x) =
      chart l (splitTrialityRepresentation K l g x)

/-- The representation-defined equivalence satisfies the component chart
law by construction. -/
theorem splitSpinZornRelatedTripleEquiv_isSplitRepresentationChart
    (chart : SplitZornChart K)
    (hQ : SplitZornTuplePreservesNorm K chart)
    (ht : SplitZornTuplePreservesTensor K chart)
    (hbij : Function.Bijective
      (splitSpinToZornRelatedTriples K chart hQ ht)) :
    IsSplitZornRepresentationChart K
      (splitSpinZornRelatedTripleEquiv K chart hQ ht hbij) chart := by
  intro g l x
  simp [splitSpinZornRelatedTripleEquiv, splitSpinToZornRelatedTriples,
    splitTrialityLinearTupleHom, chartedRepresentation,
    representationLinearEquiv]

/-- The chart transports intertwine the three representations with the
corrected Zorn outer action.  For odd permutations the intertwiner includes
octonion conjugation. -/
theorem splitSpinZornOuterAction_chart_equivariant
    (chart : SplitZornChart K)
    (hQ : SplitZornTuplePreservesNorm K chart)
    (ht : SplitZornTuplePreservesTensor K chart)
    (hbij : Function.Bijective
      (splitSpinToZornRelatedTriples K chart hQ ht))
    (σ : DiagramSymmetry)
    (g : CliffordEven.SpinPoint (splitD4Form K))
    (l : TrialityLabel) (x : SplitTrialityModule K (σ⁻¹ l)) :
    splitZornChartTransport K chart σ l
        (splitTrialityRepresentation K (σ⁻¹ l) g x) =
      splitTrialityRepresentation K l
        (splitSpinZornOuterAction K chart hQ ht hbij σ g)
        (splitZornChartTransport K chart σ l x) := by
  let e := splitSpinZornRelatedTripleEquiv K chart hQ ht hbij
  have hc : IsSplitZornRepresentationChart K e chart :=
    splitSpinZornRelatedTripleEquiv_isSplitRepresentationChart
      K chart hQ ht hbij
  apply (chart l).injective
  simp only [splitZornChartTransport, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [← hc g (σ⁻¹ l) x]
  rw [← hc
    (splitSpinZornOuterAction K chart hQ ht hbij σ g) l
    ((chart l).symm
      (zornDiagramTwist K σ (chart (σ⁻¹ l) x)))]
  rw [(chart l).apply_symm_apply]
  change
    zornDiagramTwist K σ
        (((e g).1 (σ⁻¹ l)).1 (chart (σ⁻¹ l) x)) =
      ((e (splitSpinZornOuterAction K chart hQ ht hbij σ g)).1 l).1
        (zornDiagramTwist K σ (chart (σ⁻¹ l) x))
  by_cases hσ : Zorn.DiagramEven σ
  · simp [e, splitSpinZornOuterAction, transportMulAutAction,
      transportMulAut, Zorn.relatedTripleOuterAction,
      Zorn.relatedTripleRelabel, Zorn.tupleTwistedRelabel,
      Zorn.pureTupleRelabel, orthogonalTupleRelabel,
      zornDiagramTwist, hσ]
  · simp [e, splitSpinZornOuterAction, transportMulAutAction,
      transportMulAut, Zorn.relatedTripleOuterAction,
      Zorn.relatedTripleRelabel, Zorn.tupleTwistedRelabel,
      Zorn.pureTupleRelabel, Zorn.tupleConjugation,
      orthogonalTupleRelabel, Zorn.conjugateIsometry,
      Zorn.conjugationIsometry, zornDiagramTwist, hσ]

/-- The compatible faithful outer pointwise triality package produced by the
concrete Zorn comparison. -/
noncomputable def splitSpinPointTrialityDataOfZornComparison
    (chart : SplitZornChart K)
    (hQ : SplitZornTuplePreservesNorm K chart)
    (ht : SplitZornTuplePreservesTensor K chart)
    (hbij : Function.Bijective
      (splitSpinToZornRelatedTriples K chart hQ ht)) :
    SpinPointTrialityData (splitD4Form K) where
  regularEightDimensional := splitD4Form_regular K
  action := splitSpinZornOuterAction K chart hQ ht hbij
  faithful := splitSpinZornOuterAction_injective K chart hQ ht hbij

end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality
