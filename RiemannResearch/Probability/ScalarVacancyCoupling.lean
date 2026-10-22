import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Ring

/-!
# Uniform threshold coupling of one-site vacancies

Source: the elementary common-uniform coupling of Bernoulli distributions.
This supplies a genuine monotone process for one fixed site, with exact entry
ratios. It does not claim spatial determinantal correlations or a monotone
coupling of the full random subsets.
-/

noncomputable section
open MeasureTheory
open scoped unitInterval
namespace RiemannResearch.Probability.DPP

def scalarHoleEvent (p : I) : Set I := Set.Iic p

def scalarOccupiedEvent (p : I) : Set I := Set.Ioi p

theorem scalarHoleEvent_measurable (p : I) : MeasurableSet (scalarHoleEvent p) :=
  measurableSet_Iic

theorem scalarOccupiedEvent_measurable (p : I) :
    MeasurableSet (scalarOccupiedEvent p) := measurableSet_Ioi

theorem scalarHoleEvent_probability (p : I) :
    (volume : Measure I).real (scalarHoleEvent p) = (p : ℝ) := by
  rw [scalarHoleEvent, Measure.real, unitInterval.volume_Iic,
    ENNReal.toReal_ofReal p.property.1]

theorem scalarOccupiedEvent_probability (p : I) :
    (volume : Measure I).real (scalarOccupiedEvent p) = 1 - (p : ℝ) := by
  rw [scalarOccupiedEvent, Measure.real, unitInterval.volume_Ioi,
    ENNReal.toReal_ofReal (sub_nonneg.mpr p.property.2)]

theorem scalarHoleEvent_antitone (p : ℕ → I) (hp : Antitone p) :
    Antitone (fun n => scalarHoleEvent (p n)) := by
  intro m n hmn u hu
  exact hu.trans (hp hmn)

theorem scalarOccupiedEvent_monotone (p : ℕ → I) (hp : Antitone p) :
    Monotone (fun n => scalarOccupiedEvent (p n)) := by
  intro m n hmn u hu
  exact lt_of_le_of_lt (hp hmn) hu

/-- A genuine common probability space realizes every decreasing scalar vacancy
probability by nested events. This statement concerns one fixed site only. -/
theorem exists_scalarVacancy_coupling (d : ℕ → ℝ)
    (hd : ∀ n, 0 ≤ d n ∧ d n ≤ 1) (hmono : Antitone d) :
    ∃ H O : ℕ → Set I,
      (∀ n, MeasurableSet (H n) ∧ MeasurableSet (O n)) ∧
      Antitone H ∧ Monotone O ∧
      (∀ n, (volume : Measure I).real (H n) = d n) ∧
      (∀ n, (volume : Measure I).real (O n) = 1 - d n) ∧
      (∀ n, O n = (H n)ᶜ) := by
  let p : ℕ → I := fun n => ⟨d n, hd n⟩
  have hp : Antitone p := by
    intro m n hmn
    exact hmono hmn
  refine ⟨fun n => scalarHoleEvent (p n), fun n => scalarOccupiedEvent (p n),
    ?_, scalarHoleEvent_antitone p hp, scalarOccupiedEvent_monotone p hp,
    ?_, ?_, ?_⟩
  · intro n
    exact ⟨scalarHoleEvent_measurable _, scalarOccupiedEvent_measurable _⟩
  · intro n
    exact scalarHoleEvent_probability (p n)
  · intro n
    exact scalarOccupiedEvent_probability (p n)
  · intro n
    ext u
    simp [scalarHoleEvent, scalarOccupiedEvent]

end RiemannResearch.Probability.DPP


namespace RiemannResearch.Probability.DPP
open MeasureTheory
open scoped unitInterval

theorem scalarEntry_probability (p q : I) (hqp : q ≤ p) :
    (volume : Measure I).real (scalarOccupiedEvent q \ scalarOccupiedEvent p) =
      (p : ℝ) - (q : ℝ) := by
  have hsub : scalarOccupiedEvent p ⊆ scalarOccupiedEvent q :=
    fun u hu => lt_of_le_of_lt hqp hu
  rw [measureReal_sdiff hsub (scalarOccupiedEvent_measurable p),
    scalarOccupiedEvent_probability, scalarOccupiedEvent_probability]
  ring

theorem scalarEntry_ratio (p q : I) (hqp : q ≤ p) (hp : 0 < (p : ℝ)) :
    (volume : Measure I).real (scalarOccupiedEvent q \ scalarOccupiedEvent p) /
      (volume : Measure I).real (scalarHoleEvent p) = 1 - (q : ℝ) / (p : ℝ) := by
  rw [scalarEntry_probability p q hqp, scalarHoleEvent_probability, sub_div,
    div_self (ne_of_gt hp)]
end RiemannResearch.Probability.DPP
