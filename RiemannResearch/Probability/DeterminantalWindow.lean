import RiemannResearch.Probability.DeterminantalExistence
import RiemannResearch.Probability.FiniteDeterminantalGenerating

/-!
# Finite-window laws and gap determinants of discrete DPPs

Source: Hough--Krishnapur--Peres--Virag, Determinantal Processes and
Independence, arXiv:math/0503110, for the gap-probability statement. Finite-law
identification below uses uniqueness from all inclusion probabilities.
Positivity of the explicit finite configuration weights is discharged by the
positive-contraction constructor in each arithmetic application.
-/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Classical
namespace RiemannResearch.Probability.DPP
variable {ι α Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → Set α} {K : α → α → ℝ}

/-- An arbitrary DPP's complete finite restriction agrees with the explicit
finite determinantal law, not merely with its one-point marginals. -/
theorem IsDPP.finite_restriction_law (h : IsDPP μ X K) (e : ι ↪ α)
    (hpos : ∀ S, 0 ≤ exactWeight (Matrix.of (fun i j : ι => K (e i) (e j))) S) :
    Measure.map (fun ω i => decide (e i ∈ X ω)) μ =
      (finiteBoolLaw (Matrix.of (fun i j : ι => K (e i) (e j))) hpos).toMeasure := by
  let r : Ω → (ι → Bool) := fun ω i => decide (e i ∈ X ω)
  have hr : Measurable r := by
    apply measurable_pi_lambda
    intro i
    change Measurable (({ω | e i ∈ X ω} : Set Ω).piecewise
      (fun _ => true) (fun _ => false))
    exact measurable_const.piecewise (h.measurable_occupancy (e i)) measurable_const
  let ν : Measure (ι → Bool) := μ.map r
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hr.aemeasurable
  have hν : IsDPP ν (fun x => {i | x i = true}) (fun i j => K (e i) (e j)) := by
    constructor
    · intro i
      exact (Set.toFinite _).measurableSet
    · intro m a
      change ((Measure.map r μ) {x | ∀ i, x (a i) = true}).toReal = _
      rw [Measure.map_apply hr (Set.toFinite _).measurableSet]
      simpa [r, Measure.real, Function.Embedding.trans_apply] using
        h.correlation m (a.trans e)
  exact boolMeasure_eq_of_isDPP ν _ _ hν (finiteBoolLaw_isDPP _ hpos)

/-- The probability that every site of a finite determinantal law is vacant. -/
theorem finiteBoolLaw_gap (Q : Matrix ι ι ℝ)
    (hpos : ∀ S, 0 ≤ exactWeight Q S) :
    (finiteBoolLaw Q hpos).toMeasure.real {x | ∀ i, x i ≠ true} = (1 - Q).det := by
  letI : MeasurableSpace (Finset ι) := ⊤
  have he : (fun S : Finset ι => fun i => decide (i ∈ S)) ⁻¹'
      {x : ι → Bool | ∀ i, x i ≠ true} = ({∅} : Set (Finset ι)) := by
    ext S
    change (∀ i, decide (i ∈ S) ≠ true) ↔ S = ∅
    constructor
    · intro hS
      ext i
      constructor
      · intro hi
        exact (hS i (by simp [hi])).elim
      · intro hi
        simp at hi
    · rintro rfl i
      simp
  change (((finiteLaw Q hpos).map (fun S i => decide (i ∈ S))).toMeasure
    {x | ∀ i, x i ≠ true}).toReal = _
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_finite _) (Set.toFinite _).measurableSet,
    he, (finiteLaw Q hpos).toMeasure_apply_singleton ∅ (measurableSet_singleton _)]
  change (ENNReal.ofReal (exactWeight Q ∅)).toReal = _
  rw [ENNReal.toReal_ofReal (hpos ∅)]
  change (mixedRows Q ∅).det = (1 - Q).det
  apply congrArg Matrix.det
  ext i j
  simp [mixedRows, Finset.piecewise]

/-- The finite-window Fredholm determinant is the actual gap probability. -/
theorem IsDPP.finite_gap (h : IsDPP μ X K) (e : ι ↪ α)
    (hpos : ∀ S, 0 ≤ exactWeight (Matrix.of (fun i j : ι => K (e i) (e j))) S) :
    μ.real {ω | ∀ i, e i ∉ X ω} =
      (1 - Matrix.of (fun i j : ι => K (e i) (e j))).det := by
  let r : Ω → (ι → Bool) := fun ω i => decide (e i ∈ X ω)
  have hr : Measurable r := by
    apply measurable_pi_lambda
    intro i
    change Measurable (({ω | e i ∈ X ω} : Set Ω).piecewise
      (fun _ => true) (fun _ => false))
    exact measurable_const.piecewise (h.measurable_occupancy (e i)) measurable_const
  have hl := h.finite_restriction_law e hpos
  have hp := finiteBoolLaw_gap (Matrix.of (fun i j : ι => K (e i) (e j))) hpos
  rw [← hl] at hp
  change ((μ.map r) {x | ∀ i, x i ≠ true}).toReal = _ at hp
  rw [Measure.map_apply hr (Set.toFinite _).measurableSet] at hp
  simpa [r, Measure.real] using hp

end RiemannResearch.Probability.DPP
