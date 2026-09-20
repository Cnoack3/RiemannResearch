import RiemannResearch.Probability.FiniteDeterminantalLaw
import RiemannResearch.Probability.FiniteSubsetLaw
import RiemannResearch.Probability.BooleanProjectiveLimit

/-!
# Existence of discrete determinantal laws for real positive contractions

Source: Lyons, Determinantal Probability Measures, arXiv:math/0204325,
Sections 7-8, for the existence statement. Finite laws are constructed from
explicit determinant weights, their consistency follows from inclusion-law
uniqueness, and compact Boolean cylinders supply the projective extension.
No DPP law, marginal consistency, or coupling is assumed by contractionDPP.
The only inputs are positivity of each finite principal matrix and its
complement. The arithmetic consumer proves both inputs from projections.
-/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Classical ENNReal
namespace RiemannResearch.Probability.DPP

open RiemannResearch.Probability.DPP
open RiemannResearch.Probability.FiniteSubsetLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def finiteBoolLaw (K : Matrix ι ι ℝ) (hpos : ∀ S, 0 ≤ exactWeight K S) :
    PMF (ι → Bool) :=
  (finiteLaw K hpos).map (fun S i => decide (i ∈ S))

theorem finiteBoolLaw_isDPP (K : Matrix ι ι ℝ)
    (hpos : ∀ S, 0 ≤ exactWeight K S) :
    IsDPP (finiteBoolLaw K hpos).toMeasure (fun x => {i | x i = true}) K := by
  letI : MeasurableSpace (Finset ι) := ⊤
  constructor
  · intro i
    exact (Set.toFinite _).measurableSet
  · intro n e
    change (((finiteLaw K hpos).map (fun S i => decide (i ∈ S))).toMeasure
      {x | ∀ i, x (e i) = true}).toReal = _
    rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_finite _)
      (Set.toFinite _).measurableSet]
    simpa only [Measure.real, Set.preimage_ofPred_eq, decide_eq_true_eq, Finset.mem_coe]
      using (finiteLaw_isDPP K hpos).correlation n e

/-- All finite correlations determine a finite Boolean law. -/
theorem boolMeasure_eq_of_isDPP
    (μ ν : Measure (ι → Bool)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : ι → ι → ℝ)
    (hμ : IsDPP μ (fun x => {i | x i = true}) K)
    (hν : IsDPP ν (fun x => {i | x i = true}) K) : μ = ν := by
  apply boolMeasure_eq_of_inclusion_eq
  intro T
  let q : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  let e : Fin (Fintype.card T) ↪ ι :=
    q.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ T))
  have hevent : {x : ι → Bool | ∀ j, x (e j) = true} =
      {x | ∀ i ∈ T, x i = true} := by
    ext x
    constructor
    · intro hx i hi
      obtain ⟨j, hj⟩ := q.surjective ⟨i, hi⟩
      have he : e j = i := congrArg Subtype.val hj
      simpa only [he] using hx j
    · intro hx j
      exact hx (e j) (q j).property
  rw [← hevent]
  exact (hμ.correlation _ e).trans (hν.correlation _ e).symm

variable {α : Type*}

/-- Finite DPP laws for the principal restrictions of one kernel automatically
form a projective family: exact correlations prove full marginal equality. -/
theorem isProjectiveFamily_of_isDPP
    (K : α → α → ℝ) (P : (I : Finset α) → Measure (I → Bool))
    [∀ I, IsProbabilityMeasure (P I)]
    (hDPP : ∀ I, IsDPP (P I) (fun x => {i | x i = true})
      (fun i j : I => K i.1 j.1)) : IsProjectiveMeasureFamily (α := fun _ : α => Bool) P := by
  intro I J hJI
  let r : (I → Bool) → (J → Bool) := fun x i => x ⟨i.1, hJI i.property⟩
  have hr : Measurable r := measurable_of_finite r
  let ν : Measure (J → Bool) := (P I).map r
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hr.aemeasurable
  apply boolMeasure_eq_of_isDPP (P J) ν (fun i j : J => K i.1 j.1) (hDPP J)
  constructor
  · intro i
    exact (Set.toFinite _).measurableSet
  · intro n e
    let eI : Fin n ↪ I :=
      ⟨fun i => ⟨(e i).1, hJI (e i).property⟩,
        fun i j hij => e.injective (Subtype.ext (congrArg (fun x : I => (x : α)) hij))⟩
    change (Measure.map r (P I) {x | ∀ i, x (e i) = true}).toReal = _
    rw [Measure.map_apply hr (Set.toFinite _).measurableSet]
    exact (hDPP I).correlation n eI

def finiteBoolFamily (K : α → α → ℝ)
    (hpos : ∀ I : Finset α, ∀ S,
      0 ≤ exactWeight (Matrix.of (fun i j : I => K i.1 j.1)) S)
    (I : Finset α) : Measure (I → Bool) :=
  (finiteBoolLaw (Matrix.of (fun i j : I => K i.1 j.1)) (hpos I)).toMeasure

instance finiteBoolFamily_probability (K : α → α → ℝ)
    (hpos : ∀ I : Finset α, ∀ S,
      0 ≤ exactWeight (Matrix.of (fun i j : I => K i.1 j.1)) S)
    (I : Finset α) : IsProbabilityMeasure (finiteBoolFamily K hpos I) := by
  unfold finiteBoolFamily
  infer_instance

theorem finiteBoolFamily_isDPP (K : α → α → ℝ)
    (hpos : ∀ I : Finset α, ∀ S,
      0 ≤ exactWeight (Matrix.of (fun i j : I => K i.1 j.1)) S)
    (I : Finset α) :
    IsDPP (finiteBoolFamily K hpos I) (fun x => {i | x i = true})
      (fun i j : I => K i.1 j.1) :=
  finiteBoolLaw_isDPP _ _

theorem finiteBoolFamily_projective (K : α → α → ℝ)
    (hpos : ∀ I : Finset α, ∀ S,
      0 ≤ exactWeight (Matrix.of (fun i j : I => K i.1 j.1)) S) :
    IsProjectiveMeasureFamily (α := fun _ : α => Bool) (finiteBoolFamily K hpos) :=
  isProjectiveFamily_of_isDPP K _ (finiteBoolFamily_isDPP K hpos)

end RiemannResearch.Probability.DPP

namespace RiemannResearch.Probability.DPP

open RiemannResearch.Probability.DPP
open RiemannResearch.Probability.BooleanProjective

variable {α : Type*}

def contractionDPP (K : α → α → ℝ)
    (hK : ∀ I : Finset α, (Matrix.of (fun i j : I => K i.1 j.1)).PosSemidef)
    (hI : ∀ I : Finset α, (1 - (Matrix.of (fun i j : I => K i.1 j.1))).PosSemidef) :
    Measure (α → Bool) :=
  boolProjectiveLimit (finiteBoolFamily_projective K
    (fun I S => exactWeight_nonneg _ (hK I) (hI I) S))

instance contractionDPP_probability (K : α → α → ℝ)
    (hK : ∀ I : Finset α, (Matrix.of (fun i j : I => K i.1 j.1)).PosSemidef)
    (hI : ∀ I : Finset α, (1 - (Matrix.of (fun i j : I => K i.1 j.1))).PosSemidef) :
    IsProbabilityMeasure (contractionDPP K hK hI) := by
  unfold contractionDPP
  infer_instance

/-- General existence of a DPP on an arbitrary discrete ground set, for every
real kernel whose finite principal matrices are positive contractions. -/
theorem contractionDPP_isDPP (K : α → α → ℝ)
    (hK : ∀ I : Finset α, (Matrix.of (fun i j : I => K i.1 j.1)).PosSemidef)
    (hI : ∀ I : Finset α, (1 - (Matrix.of (fun i j : I => K i.1 j.1))).PosSemidef) :
    IsDPP (contractionDPP K hK hI) (fun x => {i | x i = true}) K :=
  boolProjectiveLimit_isDPP _ K
    (finiteBoolFamily_isDPP K (fun I S => exactWeight_nonneg _ (hK I) (hI I) S))

end RiemannResearch.Probability.DPP
